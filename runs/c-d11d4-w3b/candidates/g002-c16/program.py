import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: dominating-cover vertex extension.
#
# Repeatedly adds one vertex v on a side opposite to a set S of same-side
# vertices with spare degree. v is joined to S, so the distance from v to x is
# at most D exactly when some s in S has d(s, x) <= D-1. Finding S is a
# min-conflicts set-cover search with tabu, run over bitmask balls of radius
# D-1. Only vertices are added and edges are added between opposite sides, so
# every old distance stays within D and bipartiteness is preserved. Finally,
# leftover spare degree is filled with opposite-side edges (this only shortens
# paths).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4000
#define WMAX ((MAXN + 63) / 64)
#define DEGMAX 32
#define ITERS 800
#define MAXFAIL 8

static int DEG, DIAM, nv, W, lastK;
static int adj[MAXN][DEGMAX];
static int deg[MAXN];
static int col[MAXN];
static uint64_t ball[MAXN][WMAX];
static uint64_t tmpW[MAXN][WMAX];
static int cnt[MAXN];
static int tabu[MAXN];
static int cand[MAXN];
static int stk[MAXN];
static int chosen[DEGMAX];
static int inChosen[MAXN];
static uint64_t umask[WMAX], omask[WMAX];
static uint64_t rs = 88172645463325252ULL;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nextr() % (uint64_t)k); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int bit(const uint64_t *row, int v) {
    return (int)((row[v >> 6] >> (v & 63)) & 1ULL);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adj[a][i] == b) return 1;
    return 0;
}

/* ball[v] = all vertices within distance DIAM-1 of v. */
static void compute_balls(void) {
    W = (nv + 63) >> 6;
    for (int v = 0; v < nv; v++) {
        for (int w = 0; w < W; w++) ball[v][w] = 0;
        ball[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 1; r < DIAM; r++) {
        for (int v = 0; v < nv; v++) {
            for (int w = 0; w < W; w++) tmpW[v][w] = ball[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) tmpW[v][w] |= ball[u][w];
            }
        }
        for (int v = 0; v < nv; v++)
            for (int w = 0; w < W; w++) ball[v][w] = tmpW[v][w];
    }
}

/* Rebuild the uncovered mask (cnt==0) and the once-covered mask (cnt==1). */
static int build_masks(void) {
    int unc = 0;
    for (int w = 0; w < W; w++) {
        umask[w] = 0;
        omask[w] = 0;
    }
    for (int u = 0; u < nv; u++) {
        if (cnt[u] == 0) {
            umask[u >> 6] |= 1ULL << (u & 63);
            unc++;
        } else if (cnt[u] == 1) {
            omask[u >> 6] |= 1ULL << (u & 63);
        }
    }
    return unc;
}

/* Try to find <= DEG same-side (colour c, spare degree) vertices whose
   radius-(DIAM-1) balls cover all vertices. Result in chosen[0..lastK-1]. */
static int find_cover(int c) {
    int nc = 0;
    for (int v = 0; v < nv; v++)
        if (col[v] == c && deg[v] < DEG) cand[nc++] = v;
    if (nc == 0) return 0;
    int k = nc < DEG ? nc : DEG;
    lastK = k;
    for (int v = 0; v < nv; v++) {
        inChosen[v] = 0;
        tabu[v] = 0;
    }
    for (int i = 0; i < k; i++) {
        int s;
        do {
            s = cand[rnd(nc)];
        } while (inChosen[s]);
        inChosen[s] = 1;
        chosen[i] = s;
    }
    for (int u = 0; u < nv; u++) cnt[u] = 0;
    for (int i = 0; i < k; i++) {
        int s = chosen[i];
        for (int u = 0; u < nv; u++)
            if (bit(ball[s], u)) cnt[u]++;
    }
    int unc = 0;
    for (int it = 0; it < ITERS; it++) {
        unc = build_masks();
        if (unc == 0) return 1;

        /* Pick a random uncovered vertex u. */
        int u = -1, seen = 0;
        for (int x = 0; x < nv; x++) {
            if (cnt[x] == 0) {
                seen++;
                if (rnd(seen) == 0) u = x;
            }
        }

        /* Add the non-tabu candidate covering u with the largest gain. */
        int bs = -1, bg = -1, nties = 0;
        for (int j = 0; j < nc; j++) {
            int s = cand[j];
            if (inChosen[s] || tabu[s] > it || !bit(ball[s], u)) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(ball[s][w] & umask[w]);
            if (g > bg) {
                bg = g;
                bs = s;
                nties = 1;
            } else if (g == bg) {
                nties++;
                if (rnd(nties) == 0) bs = s;
            }
        }
        if (bs < 0) continue;

        /* Remove the chosen vertex whose loss (vertices only it covers) is smallest. */
        int bi = -1, bl = 1 << 30, nt = 0;
        for (int i = 0; i < k; i++) {
            int t = chosen[i];
            int l = 0;
            for (int w = 0; w < W; w++) l += pc64(ball[t][w] & omask[w]);
            if (l < bl) {
                bl = l;
                bi = i;
                nt = 1;
            } else if (l == bl) {
                nt++;
                if (rnd(nt) == 0) bi = i;
            }
        }
        int t = chosen[bi];
        for (int x = 0; x < nv; x++) {
            if (bit(ball[t], x)) cnt[x]--;
            if (bit(ball[bs], x)) cnt[x]++;
        }
        inChosen[t] = 0;
        inChosen[bs] = 1;
        chosen[bi] = bs;
        tabu[t] = it + 3 + rnd(7);
    }
    unc = build_masks();
    return unc == 0;
}

static void add_vertex(int c) {
    int v = nv++;
    col[v] = 1 - c;
    deg[v] = 0;
    for (int i = 0; i < lastK; i++) {
        int s = chosen[i];
        adj[s][deg[s]++] = v;
        adj[v][deg[v]++] = s;
    }
}

/* Add opposite-side edges between vertices with spare degree (never breaks validity). */
static void saturate(void) {
    static int order[MAXN];
    int no = 0;
    for (int v = 0; v < nv; v++)
        if (deg[v] < DEG) order[no++] = v;
    for (int i = no - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t = order[i];
        order[i] = order[j];
        order[j] = t;
    }
    for (int ii = 0; ii < no; ii++) {
        int a = order[ii];
        for (int jj = 0; jj < no && deg[a] < DEG; jj++) {
            int b = order[jj];
            if (col[a] == col[b] || deg[b] >= DEG || deg[a] >= DEG) continue;
            if (has_edge(a, b)) continue;
            adj[a][deg[a]++] = b;
            adj[b][deg[b]++] = a;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 1234567ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();
    if (DEG < 1 || DEG > DEGMAX || DIAM < 2 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        n = 0;
        m = 0;
    }
    if (n < 1 || n > MAXN - 2) {
        printf("0 0\n");
        return 0;
    }
    nv = n;
    for (int i = 0; i < nv; i++) {
        deg[i] = 0;
        col[i] = -1;
    }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= nv || v >= nv || u == v) continue;
        if (deg[u] >= DEG || deg[v] >= DEG || has_edge(u, v)) continue;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }

    for (int s = 0; s < nv; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[u][i];
                if (col[w] == -1) {
                    col[w] = 1 - col[u];
                    stk[sp++] = w;
                }
            }
        }
    }

    clock_t t0 = clock();
    int fails = 0;
    while (nv + 1 < MAXN) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (el >= tl) break;
        compute_balls();
        int first = rnd(2);
        int added = 0;
        for (int q = 0; q < 2 && !added; q++) {
            int c = (q == 0) ? first : 1 - first;
            if (find_cover(c)) {
                add_vertex(c);
                added = 1;
            }
        }
        if (added) {
            fails = 0;
        } else if (++fails >= MAXFAIL) {
            break;
        }
    }

    saturate();

    long long em = 0;
    for (int v = 0; v < nv; v++) em += deg[v];
    printf("%d %lld\n", nv, em / 2);
    for (int v = 0; v < nv; v++)
        for (int i = 0; i < deg[v]; i++)
            if (v < adj[v][i]) printf("%d %d\n", v, adj[v][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _run_ext(d, D, seed, graph, budget):
    """Run the C cover-extension engine from `graph` for about `budget` CPU seconds."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                    stdin_graph=graph, timeout=budget + 6.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)

    # Trivial cases.
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Calibration: D = 3 with d - 1 a prime power is the Moore-optimal incidence graph.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, e0, d, D):
            return n0, e0

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Structured base: a diameter-3 projective plane for D = 3, or the
    # generalized quadrangle W(q) (diameter 4, valid for every D >= 4).
    base = None
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                base = lib.projective_plane_incidence(q)
                break
    elif D >= 4:
        base = _best_gq(d)
    if base is not None:
        consider(base[0], base[1])

    # Main search: repeated dominating-cover extension in C, from the best graph so far.
    # Two runs with different seeds share the budget; each starts from the best found.
    end = start + 0.88 * tl - 1.0
    runs = 2
    for idx in range(runs):
        remaining = end - time.monotonic()
        budget = remaining / (runs - idx)
        if budget < 1.0:
            break
        try:
            n2, e2 = _run_ext(d, D, seed + 101 * idx, best, budget)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
