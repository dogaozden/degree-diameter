"""Growth engine for bipartite graphs with max degree d and diameter D.

Structured starts: PG(2, q) incidence for D = 3, and the generalized quadrangle
incidence W(q) for D >= 4. The C engine then grows the best start. Its moves are:
  * sacrifice insertion: free one edge at each of t saturated vertices, attach a new
    vertex to a greedy set cover of the ball of radius D-1, re-saturate, keep if valid;
  * edge-swap walk: preserves degrees and bipartiteness, kept only if still valid.
Every state it keeps is valid, and a bitset all-pairs oracle checks each candidate.
"""
import itertools
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4096
#define MAXD 64
#define MAXW 64

static int DEG, DIAM, nv;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t bufA[MAXN * MAXW];
static uint64_t bufB[MAXN * MAXW];
static uint64_t rs = 88172645463325252ULL;

static int snv;
static int sdeg[MAXN];
static int sadj[MAXN][MAXD];
static int scol[MAXN];

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }

static int pc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int wcount(void) { return (nv + 63) / 64; }

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adj[a][i] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void rm_half(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a][i] == b) {
            adj[a][i] = adj[a][--deg[a]];
            return;
        }
    }
}

static void del_edge(int a, int b) {
    rm_half(a, b);
    rm_half(b, a);
}

/* Bitmask of vertices within distance r of each vertex, stored in out (row v at v*MAXW). */
static void balls(int r, uint64_t *out) {
    int W = wcount();
    uint64_t *cur = out;
    uint64_t *nxt = (out == bufA) ? bufB : bufA;
    for (int v = 0; v < nv; v++) {
        for (int w = 0; w < W; w++) cur[v * MAXW + w] = 0;
        cur[v * MAXW + v / 64] |= 1ULL << (v % 64);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < nv; v++) {
            uint64_t *dst = nxt + v * MAXW;
            const uint64_t *src = cur + v * MAXW;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *su = cur + adj[v][i] * MAXW;
                for (int w = 0; w < W; w++) dst[w] |= su[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    if (cur != out) memcpy(out, cur, sizeof(uint64_t) * (size_t)nv * MAXW);
}

static int diam_ok(void) {
    balls(DIAM, bufA);
    int W = wcount();
    int rem = nv % 64;
    uint64_t last = rem ? ((1ULL << rem) - 1) : ~0ULL;
    for (int v = 0; v < nv; v++) {
        for (int w = 0; w < W - 1; w++)
            if (bufA[v * MAXW + w] != ~0ULL) return 0;
        if (bufA[v * MAXW + W - 1] != last) return 0;
    }
    return 1;
}

/* Greedy cover of all vertices by balls (in bufA) of candidates on `side`. */
static int cover_pick(int side, int *chosen, int *nch) {
    static int cand[MAXN];
    static int gain[MAXN];
    static char taken[MAXN];
    int W = wcount();
    uint64_t cov[MAXW];
    int nc = 0, covered = 0;
    for (int v = 0; v < nv; v++) {
        taken[v] = 0;
        if (col[v] == side && deg[v] < DEG) cand[nc++] = v;
    }
    for (int w = 0; w < W; w++) cov[w] = 0;
    *nch = 0;
    while (covered < nv && *nch < DEG) {
        int bg = 0;
        for (int i = 0; i < nc; i++) {
            int c = cand[i];
            if (taken[c]) {
                gain[i] = -1;
                continue;
            }
            int g = 0;
            const uint64_t *bc = bufA + c * MAXW;
            for (int w = 0; w < W; w++) g += pc(bc[w] & ~cov[w]);
            gain[i] = g;
            if (g > bg) bg = g;
        }
        if (bg == 0) break;
        int thr = bg;
        if (bg > 1 && rndi(4) == 0) thr = bg - 1;
        int opts = 0;
        for (int i = 0; i < nc; i++)
            if (gain[i] >= thr) opts++;
        int pick = rndi(opts), idx = -1;
        for (int i = 0; i < nc; i++) {
            if (gain[i] >= thr) {
                if (pick == 0) {
                    idx = i;
                    break;
                }
                pick--;
            }
        }
        int c = cand[idx];
        taken[c] = 1;
        chosen[(*nch)++] = c;
        const uint64_t *bc = bufA + c * MAXW;
        covered = 0;
        for (int w = 0; w < W; w++) {
            cov[w] |= bc[w];
            covered += pc(cov[w]);
        }
    }
    return covered == nv;
}

/* Join deficient opposite-side vertices. Only lowers distances, so validity is kept. */
static void saturate(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < nv; v++) {
        if (deg[v] < DEG) {
            if (col[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    if (nl == 0 || nr == 0) return;
    long tries = 50L * (nl + nr) + 1000;
    for (long t = 0; t < tries; t++) {
        int a = L[rndi(nl)], b = R[rndi(nr)];
        if (deg[a] < DEG && deg[b] < DEG && !has_edge(a, b)) add_edge(a, b);
    }
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr; j++) {
            if (deg[a] >= DEG) break;
            int b = R[j];
            if (deg[b] < DEG && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

static void save_state(void) {
    snv = nv;
    memcpy(sdeg, deg, sizeof(int) * (size_t)nv);
    memcpy(sadj, adj, sizeof(int) * MAXD * (size_t)nv);
    memcpy(scol, col, sizeof(int) * (size_t)nv);
}

static void restore_state(void) {
    nv = snv;
    memcpy(deg, sdeg, sizeof(int) * (size_t)nv);
    memcpy(adj, sadj, sizeof(int) * MAXD * (size_t)nv);
    memcpy(col, scol, sizeof(int) * (size_t)nv);
}

/* Sacrifice insertion of one vertex. Returns 1 if the graph grew and stays valid. */
static int try_move(void) {
    if (nv + 2 >= MAXN) return 0;
    int t = 1 + rndi(3);
    int side = rndi(2);
    static int sat[MAXN];
    int ns = 0;
    for (int v = 0; v < nv; v++)
        if (col[v] == side && deg[v] >= DEG) sat[ns++] = v;
    save_state();
    for (int k = 0; k < t && ns > 0; k++) {
        int j = rndi(ns);
        int s = sat[j];
        sat[j] = sat[--ns];
        if (deg[s] == 0) continue;
        int y = adj[s][rndi(deg[s])];
        del_edge(s, y);
    }
    balls(DIAM - 1, bufA);
    int chosen[MAXD];
    int nch = 0;
    if (!cover_pick(side, chosen, &nch)) {
        restore_state();
        return 0;
    }
    int v = nv++;
    deg[v] = 0;
    col[v] = 1 - side;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], v);
    saturate();
    if (!diam_ok()) {
        restore_state();
        return 0;
    }
    return 1;
}

/* Degree- and bipartition-preserving edge swap, kept only if the graph stays valid. */
static void edge_swap(void) {
    int a = -1, c = -1;
    for (int tr = 0; tr < 200 && (a < 0 || c < 0); tr++) {
        int x = rndi(nv);
        if (col[x] == 0 && deg[x] > 0) {
            if (a < 0) a = x;
            else if (c < 0 && x != a) c = x;
        }
    }
    if (a < 0 || c < 0) return;
    int b = adj[a][rndi(deg[a])];
    int dd = adj[c][rndi(deg[c])];
    if (b == dd || has_edge(a, dd) || has_edge(c, b)) return;
    save_state();
    del_edge(a, b);
    del_edge(c, dd);
    add_edge(a, dd);
    add_edge(c, b);
    if (!diam_ok()) restore_state();
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        printf("0 0\n");
        return 0;
    }
    if (DEG < 1 || DEG > MAXD || DIAM < 2 || n < 1 || n > MAXN - 512 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    nv = n;
    for (int v = 0; v < n; v++) {
        deg[v] = 0;
        col[v] = -1;
    }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || has_edge(u, v) ||
            deg[u] >= DEG || deg[v] >= DEG) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int x = queue[qh++];
            for (int i = 0; i < deg[x]; i++) {
                int y = adj[x][i];
                if (col[y] < 0) {
                    col[y] = 1 - col[x];
                    queue[qt++] = y;
                } else if (col[y] == col[x]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    if (!diam_ok()) {
        printf("0 0\n");
        return 0;
    }
    saturate();
    if (!diam_ok()) {
        printf("0 0\n");
        return 0;
    }

    clock_t c0 = clock();
    while (nv + 2 < MAXN) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= budget) break;
        if (!try_move()) {
            if (rndi(3) == 0) edge_swap();
        }
    }

    int ne = 0;
    for (int v = 0; v < nv; v++)
        for (int i = 0; i < deg[v]; i++)
            if (adj[v][i] > v) ne++;
    printf("%d %d\n", nv, ne);
    for (int v = 0; v < nv; v++)
        for (int i = 0; i < deg[v]; i++)
            if (adj[v][i] > v) printf("%d %d\n", v, adj[v][i]);
    return 0;
}
"""


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are all points of PG(3, q); lines are totally isotropic lines of the
    symplectic form B(x, y) = x0*y1 - x1*y0 + x2*y3 - x3*y2. Degree is q + 1,
    diameter is 4, and the order is 2(q+1)(q^2+1).
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


def _starts(d, D):
    """Structured valid starts: PG(2, q) for D = 3, W(q) for D >= 4 (largest q with q + 1 <= d)."""
    qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
    out = []
    if D == 3:
        for q in qs[:2]:
            out.append(lib.projective_plane_incidence(q))
    elif D >= 4:
        for q in [q for q in qs if q <= 16][:2]:
            out.append(_gq_w(q))
    return out


def _c_grow(n, edges, d, D, seed, budget, timeout):
    """Run the C growth engine from (n, edges). Returns a valid larger graph, or None."""
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                         stdin_graph=(n, edges), timeout=timeout)
        n2, e2 = lib.parse_graph_text(text)
    except (RuntimeError, ValueError, OSError):
        return None
    if n2 > n and lib.is_valid(n2, e2, d, D):
        return n2, e2
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if D == 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])
    if d < 1 or D < 1:
        return 1, []

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    starts = [(n, e) for n, e in _starts(d, D) if lib.is_valid(n, e, d, D)]
    if not starts:
        starts = [fallback]
    best = max(starts, key=lambda g: g[0])
    if best[0] < fallback[0]:
        best = fallback
    limit = lib.moore_bound(d, D)
    if best[0] >= limit:
        return best

    order = sorted(starts, key=lambda g: -g[0])
    for i, (n, e) in enumerate(order):
        now = time.monotonic() - t0
        left = 0.8 * time_limit - now - 1.0
        if left < 0.5:
            break
        budget = left / (len(order) - i)
        timeout = min(budget + 3.0, 0.95 * time_limit - now)
        res = _c_grow(n, e, d, D, seed + i, budget, timeout)
        if res is not None and res[0] > best[0]:
            best = res
        if best[0] >= limit:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
