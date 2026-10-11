import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New routine: pair insertion followed by simulated-annealing repair.
#
# The C engine keeps a graph with max degree d and bipartition (side 0, side 1).
# Growth step: cut d-1 edges that form a matching, delete them, and add two new
# vertices a (side 0) and b (side 1) with a adjacent to the d-1 freed side-1
# ends, b adjacent to the freed side-0 ends, and a adjacent to b. All degrees
# stay the same or exactly d. Then simulated annealing over double-edge swaps
# (which preserve every degree and bipartiteness) minimises the number of vertex
# pairs at distance greater than D, using bitset balls. The first zero-cost state
# becomes the new anchor. Rejected stages restart from the anchor with fresh random
# cut edges and a doubled annealing budget. Before growth, random edges are added
# between deficient vertices, which can only shrink distances.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 3000
#define MAXDEG 16
#define MAXE (MAXN * MAXDEG / 2)
#define MAXW ((MAXN + 63) / 64)
#define THI 1.0
#define TLO 0.08
#define SEG 3000
#define STAGE_BASE 2500
#define BIG_BUDGET 400000000LL

static int DEG = 3, DIAM = 3;
static int N = 0, M = 0;
static int ex[MAXE + 64], ey[MAXE + 64];
static int eu[MAXE + 64], evv[MAXE + 64];
static int aex[MAXE + 64], aey[MAXE + 64];
static int aM = 0, aN = 0;
static int adj[MAXN * MAXDEG];
static int dg[MAXN + 4];
static int colr[MAXN + 4];
static int mx[MAXN + 4], my[MAXN + 4];
static int stamp = 0;
static uint64_t BA[MAXN * MAXW], BB[MAXN * MAXW];
static uint64_t rs = 88172645463325252ULL;
static double deadline = 0.0;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double rand01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void rebuild(void) {
    for (int v = 0; v < N; v++) dg[v] = 0;
    for (int e = 0; e < M; e++) {
        int x = ex[e], y = ey[e];
        adj[x * MAXDEG + dg[x]++] = y;
        adj[y * MAXDEG + dg[y]++] = x;
    }
}

static int has_edge(int x, int y) {
    for (int t = 0; t < dg[x]; t++)
        if (adj[x * MAXDEG + t] == y) return 1;
    return 0;
}

static void replace_nb(int v, int old, int nw) {
    for (int t = 0; t < dg[v]; t++) {
        if (adj[v * MAXDEG + t] == old) {
            adj[v * MAXDEG + t] = nw;
            return;
        }
    }
}

/* Edges e1 = (a,p), e2 = (c,q) become (a,q), (c,p). Applying it twice undoes it. */
static int try_swap(int e1, int e2) {
    int a = ex[e1], p = ey[e1], c = ex[e2], q = ey[e2];
    if (e1 == e2 || a == c || p == q) return 0;
    if (has_edge(a, q) || has_edge(c, p)) return 0;
    ey[e1] = q;
    ey[e2] = p;
    replace_nb(a, p, q);
    replace_nb(p, a, c);
    replace_nb(c, q, p);
    replace_nb(q, c, a);
    return 1;
}

/* Number of unordered vertex pairs at distance greater than DIAM. */
static long long bad_count(void) {
    int nw = (N + 63) / 64;
    uint64_t *cur = BA, *nxt = BB;
    size_t tot_words = (size_t)N * (size_t)nw;
    memset(cur, 0, sizeof(uint64_t) * tot_words);
    for (int v = 0; v < N; v++)
        cur[(size_t)v * nw + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    long long tot = N, prev = N;
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * nw;
            const uint64_t *cv = cur + (size_t)v * nw;
            memcpy(o, cv, sizeof(uint64_t) * (size_t)nw);
            for (int t = 0; t < dg[v]; t++) {
                const uint64_t *cu = cur + (size_t)adj[v * MAXDEG + t] * nw;
                for (int w = 0; w < nw; w++) o[w] |= cu[w];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        tot = 0;
        for (size_t i = 0; i < tot_words; i++) tot += pc64(cur[i]);
        if (tot == prev) break;
        prev = tot;
    }
    return ((long long)N * N - tot) / 2;
}

/* 2-colour the graph; returns 0 if it is not bipartite or has a self-loop. */
static int color_graph(int n, int m) {
    for (int v = 0; v < n; v++) colr[v] = -1;
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int e = 0; e < m; e++) {
            int u = eu[e], v = evv[e];
            if (colr[u] < 0 && colr[v] >= 0) {
                colr[u] = 1 - colr[v];
                changed = 1;
            } else if (colr[v] < 0 && colr[u] >= 0) {
                colr[v] = 1 - colr[u];
                changed = 1;
            }
        }
        if (!changed) {
            for (int v = 0; v < n; v++) {
                if (colr[v] < 0) {
                    colr[v] = 0;
                    changed = 1;
                    break;
                }
            }
        }
    }
    for (int e = 0; e < m; e++) {
        int u = eu[e], v = evv[e];
        if (u == v || colr[u] == colr[v]) return 0;
        if (colr[u] == 0) {
            ex[e] = u;
            ey[e] = v;
        } else {
            ex[e] = v;
            ey[e] = u;
        }
    }
    return 1;
}

/* Add random side0-side1 edges between vertices of degree below DEG (never hurts diameter). */
static void fill_deficits(void) {
    for (long t = 0; t < 4000000L && M < MAXE; t++) {
        int x = rint_(N), y = rint_(N);
        if (colr[x] != 0 || colr[y] != 1) continue;
        if (dg[x] >= DEG || dg[y] >= DEG) continue;
        if (has_edge(x, y)) continue;
        ex[M] = x;
        ey[M] = y;
        M++;
        adj[x * MAXDEG + dg[x]++] = y;
        adj[y * MAXDEG + dg[y]++] = x;
    }
}

/* Cut DEG-1 matching edges and insert a vertex pair. Returns 0 if impossible. */
static int pair_insert(void) {
    int k = DEG - 1;
    if (k < 1) return 0;
    if (N + 2 > MAXN || M + DEG > MAXE) return 0;
    int idx[MAXDEG], xs[MAXDEG], ys[MAXDEG];
    int cnt = 0;
    for (int attempt = 0; attempt < 50 && cnt < k; attempt++) {
        cnt = 0;
        stamp++;
        for (int t = 0; t < 100 * k && cnt < k; t++) {
            int e = rint_(M);
            int x = ex[e], y = ey[e];
            if (mx[x] == stamp || my[y] == stamp) continue;
            mx[x] = stamp;
            my[y] = stamp;
            idx[cnt++] = e;
        }
    }
    if (cnt < k) return 0;
    for (int i = 0; i < k; i++) {
        xs[i] = ex[idx[i]];
        ys[i] = ey[idx[i]];
    }
    /* sort chosen indices in descending order, then swap-remove them */
    for (int i = 1; i < k; i++) {
        int v = idx[i], j = i - 1;
        while (j >= 0 && idx[j] < v) {
            idx[j + 1] = idx[j];
            j--;
        }
        idx[j + 1] = v;
    }
    for (int i = 0; i < k; i++) {
        int e = idx[i];
        ex[e] = ex[M - 1];
        ey[e] = ey[M - 1];
        M--;
    }
    int a = N, b = N + 1;
    colr[a] = 0;
    colr[b] = 1;
    for (int i = 0; i < k; i++) {
        ex[M] = a;
        ey[M] = ys[i];
        M++;
        ex[M] = xs[i];
        ey[M] = b;
        M++;
    }
    ex[M] = a;
    ey[M] = b;
    M++;
    N += 2;
    rebuild();
    return 1;
}

/* Simulated annealing over double-edge swaps. Returns 1 on success (bad == 0),
   0 if the budget ran out, -1 on timeout. */
static int sa_repair(long long budget) {
    long long cur = bad_count();
    if (cur == 0) return 1;
    double ratio = TLO / THI;
    for (long long it = 0; it < budget; it++) {
        if ((it & 63) == 0 && now_s() > deadline) return -1;
        int e1 = rint_(M), e2 = rint_(M);
        if (!try_swap(e1, e2)) continue;
        long long nb = bad_count();
        long long delta = nb - cur;
        int acc;
        if (delta <= 0) {
            acc = 1;
        } else {
            double T = THI * pow(ratio, (double)(it % SEG) / (double)SEG);
            acc = rand01() < exp(-(double)delta / T);
        }
        if (acc) {
            cur = nb;
            if (cur == 0) return 1;
        } else {
            try_swap(e1, e2);
        }
    }
    return 0;
}

static void save_anchor(void) {
    aN = N;
    aM = M;
    memcpy(aex, ex, sizeof(int) * (size_t)M);
    memcpy(aey, ey, sizeof(int) * (size_t)M);
}

static void restore_anchor(void) {
    N = aN;
    M = aM;
    memcpy(ex, aex, sizeof(int) * (size_t)M);
    memcpy(ey, aey, sizeof(int) * (size_t)M);
    rebuild();
}

int main(int argc, char **argv) {
    DEG = argc > 1 ? atoi(argv[1]) : 3;
    DIAM = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 5.0;
    if (DEG < 2 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n < 2 || n > MAXN || m < 1 || m > MAXE) {
        printf("0 0\n");
        return 0;
    }
    for (int e = 0; e < m; e++) {
        if (scanf("%d %d", &eu[e], &evv[e]) != 2 || eu[e] < 0 || eu[e] >= n ||
            evv[e] < 0 || evv[e] >= n) {
            printf("0 0\n");
            return 0;
        }
    }
    if (!color_graph(n, m)) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    M = m;
    for (int v = 0; v < N; v++) dg[v] = 0;
    for (int e = 0; e < M; e++) {
        dg[ex[e]]++;
        dg[ey[e]]++;
    }
    for (int v = 0; v < N; v++) {
        if (dg[v] > DEG) {
            printf("0 0\n");
            return 0;
        }
    }
    rebuild();
    fill_deficits();
    if (sa_repair(BIG_BUDGET) != 1) {
        printf("0 0\n");
        return 0;
    }

    save_anchor();
    int fails = 0;
    while (now_s() < deadline) {
        restore_anchor();
        if (!pair_insert()) break;
        int sh = fails < 4 ? fails : 4;
        long long budget = (long long)STAGE_BASE << sh;
        int r = sa_repair(budget);
        if (r == 1) {
            save_anchor();
            fails = 0;
        } else if (r < 0) {
            break;
        } else {
            fails++;
        }
    }
    restore_anchor();
    printf("%d %d\n", N, M);
    for (int e = 0; e < M; e++) printf("%d %d\n", ex[e], ey[e]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, then the C growth and repair search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(2.0, min(0.9 * time_limit, time_limit - 4.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is optimal for D = 2, so it is the fallback.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if 2 <= d <= 16 and D >= 3:
        remaining = deadline - time.monotonic()
        c_budget = remaining - 1.0
        if c_budget >= 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}"],
                                stdin_graph=best, timeout=time_limit - 1.5)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
