import itertools
import time

import lib


# ----------------------------------------------------------------------------
# NEW: C engine "bitset anneal with greedy-cover insertion".
#
# State: a bipartite graph on <= 1024 vertices, max degree d. Cost = number of
# vertex pairs at distance > D, computed exactly from radius-D bitset balls.
#   * Moves: add an edge between spare vertices, rewire one endpoint to a spare
#     vertex, or a degree-preserving 2-switch. Accept by Metropolis rule.
#   * Insertion: whenever cost is 0, try to add a new vertex whose neighbours are
#     chosen greedily to cover all old vertices within distance D (radius D-1
#     balls of the chosen neighbours). This keeps cost 0 and grows n.
#   * Stagnation: if no zero-cost state appears for a while, restore the last
#     valid state and reheat.
# The best valid graph is printed; Python re-checks it with lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define WMAX 16
#define ADJMAX 64
#define MAXE 40000

static int DEG, DIAM;
static int adjv[MAXN][ADJMAX];
static int degv[MAXN];
static unsigned char col[MAXN];
static int N;
static uint64_t bufA[MAXN * WMAX], bufB[MAXN * WMAX];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }

static inline int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_e(int a, int b) {
    adjv[a][degv[a]++] = b;
    adjv[b][degv[b]++] = a;
}
static void rem_from(int a, int b) {
    for (int k = 0; k < degv[a]; k++) {
        if (adjv[a][k] == b) { adjv[a][k] = adjv[a][--degv[a]]; return; }
    }
}
static void del_e(int a, int b) { rem_from(a, b); rem_from(b, a); }
static int has_edge(int a, int b) {
    for (int k = 0; k < degv[a]; k++) if (adjv[a][k] == b) return 1;
    return 0;
}

/* Balls of radius r around every vertex 0..n-1, stride WMAX words. */
static uint64_t *compute_balls(int n, int r) {
    int W = (n + 63) >> 6;
    uint64_t *cur = bufA, *nxt = bufB;
    for (int v = 0; v < n; v++) {
        uint64_t *p = cur + (size_t)v * WMAX;
        for (int w = 0; w < W; w++) p[w] = 0;
        p[v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * WMAX;
            const uint64_t *src = cur + (size_t)v * WMAX;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int k = 0; k < degv[v]; k++) {
                const uint64_t *s2 = cur + (size_t)adjv[v][k] * WMAX;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    return cur;
}

static long long eval_cost(int n) {
    uint64_t *b = compute_balls(n, DIAM);
    int W = (n + 63) >> 6;
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *p = b + (size_t)v * WMAX;
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(p[w]);
        tot += n - c;
    }
    return tot / 2;
}

/* Undo log for one move. */
typedef struct { int t, a, b; } Op;
static Op ops[8];
static int nops = 0;

static void do_add(int a, int b) {
    add_e(a, b);
    ops[nops].t = 0; ops[nops].a = a; ops[nops].b = b; nops++;
}
static void do_del(int a, int b) {
    del_e(a, b);
    ops[nops].t = 1; ops[nops].a = a; ops[nops].b = b; nops++;
}
static void undo_all(void) {
    while (nops > 0) {
        nops--;
        Op o = ops[nops];
        if (o.t == 0) del_e(o.a, o.b);
        else add_e(o.a, o.b);
    }
}

static int move_add(int n) {
    int a = -1;
    for (int t = 0; t < 50; t++) {
        int x = rndi(n);
        if (degv[x] < DEG) { a = x; break; }
    }
    if (a < 0) return 0;
    for (int t = 0; t < 50; t++) {
        int y = rndi(n);
        if (col[y] != col[a] && degv[y] < DEG && !has_edge(a, y)) {
            do_add(a, y);
            return 1;
        }
    }
    return 0;
}

static int move_rewire(int n) {
    int u = -1;
    for (int t = 0; t < 50; t++) {
        int x = rndi(n);
        if (degv[x] > 0) { u = x; break; }
    }
    if (u < 0) return 0;
    int v = adjv[u][rndi(degv[u])];
    do_del(u, v);
    for (int t = 0; t < 50; t++) {
        int w = rndi(n);
        if (col[w] != col[u] && w != v && degv[w] < DEG && !has_edge(u, w)) {
            do_add(u, w);
            return 1;
        }
    }
    return 0;
}

static int move_swap(int n) {
    int u = -1;
    for (int t = 0; t < 50; t++) {
        int x = rndi(n);
        if (degv[x] > 0) { u = x; break; }
    }
    if (u < 0) return 0;
    int v = adjv[u][rndi(degv[u])];
    int x2 = -1;
    for (int t = 0; t < 50; t++) {
        int x = rndi(n);
        if (col[x] == col[u] && x != u && degv[x] > 0) { x2 = x; break; }
    }
    if (x2 < 0) return 0;
    int y = adjv[x2][rndi(degv[x2])];
    if (y == v) return 0;
    if (has_edge(u, y) || has_edge(x2, v)) return 0;
    do_del(u, v);
    do_del(x2, y);
    do_add(u, y);
    do_add(x2, v);
    return 1;
}

/* Greedy-cover insertion: new vertex with neighbours covering all old vertices
   within distance D. Commits only if the result has cost 0. */
static int try_grow(int n) {
    if (n + 1 > MAXN || DIAM < 2) return 0;
    uint64_t *b = compute_balls(n, DIAM - 1);
    int W = (n + 63) >> 6;
    uint64_t cov[WMAX];
    for (int w = 0; w < W; w++) cov[w] = 0;
    int c = rndi(2);
    static int cand[MAXN];
    static unsigned char used[MAXN];
    int nc = 0;
    for (int v = 0; v < n; v++) {
        used[v] = 0;
        if (col[v] != c && degv[v] < DEG) cand[nc++] = v;
    }
    if (nc == 0) return 0;
    int chosen[ADJMAX];
    int k = 0;
    int covcount = 0;
    while (k < DEG && covcount < n) {
        int best = 0, pick = -1, ties = 0;
        for (int i = 0; i < nc; i++) {
            int s = cand[i];
            if (used[s]) continue;
            const uint64_t *p = b + (size_t)s * WMAX;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(p[w] & ~cov[w]);
            if (g > best) { best = g; pick = s; ties = 1; }
            else if (g == best && g > 0) {
                ties++;
                if (rndi(ties) == 0) pick = s;
            }
        }
        if (best <= 0 || pick < 0) break;
        used[pick] = 1;
        chosen[k++] = pick;
        const uint64_t *p = b + (size_t)pick * WMAX;
        for (int w = 0; w < W; w++) cov[w] |= p[w];
        covcount = 0;
        for (int w = 0; w < W; w++) covcount += pc64(cov[w]);
    }
    if (k == 0 || covcount < n) return 0;
    degv[n] = 0;
    col[n] = (unsigned char)c;
    for (int i = 0; i < k; i++) add_e(n, chosen[i]);
    if (eval_cost(n + 1) != 0) {
        for (int i = 0; i < k; i++) del_e(n, chosen[i]);
        degv[n] = 0;
        return 0;
    }
    return 1;
}

typedef struct {
    int n, m;
    int eu[MAXE], ev[MAXE];
    unsigned char c[MAXN];
} Snap;
static Snap bestS, baseS;
static int best_valid = 0;

static void take_snap(Snap *s) {
    s->n = N;
    s->m = 0;
    for (int u = 0; u < N; u++) {
        for (int k = 0; k < degv[u]; k++) {
            int v = adjv[u][k];
            if (u < v && s->m < MAXE) {
                s->eu[s->m] = u;
                s->ev[s->m] = v;
                s->m++;
            }
        }
    }
    memcpy(s->c, col, N);
}

static void load_snap(const Snap *s) {
    memset(degv, 0, sizeof(degv));
    N = s->n;
    memcpy(col, s->c, N);
    for (int i = 0; i < s->m; i++) add_e(s->eu[i], s->ev[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs = seed * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || DEG < 1 || DEG > ADJMAX) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (has_edge(u, v) || degv[u] >= DEG || degv[v] >= DEG) continue;
        add_e(u, v);
    }

    /* Bipartition by BFS. */
    static int q[MAXN];
    static unsigned char seen[MAXN];
    memset(seen, 0, sizeof(seen));
    for (int s = 0; s < n; s++) {
        if (seen[s]) continue;
        seen[s] = 1;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int k = 0; k < degv[u]; k++) {
                int v = adjv[u][k];
                if (!seen[v]) {
                    seen[v] = 1;
                    col[v] = (unsigned char)(1 - col[u]);
                    q[t++] = v;
                }
            }
        }
    }

    long long cur = eval_cost(N);
    take_snap(&bestS);
    take_snap(&baseS);
    best_valid = (cur == 0);

    if (DIAM >= 2) {
        clock_t t0 = clock();
        double T = 1.0;
        long long iter = 0, lastzero = 0;
        const long long STAG = 30000;
        for (;;) {
            iter++;
            if ((iter & 63) == 0) {
                double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
                if (el >= budget) break;
            }
            if (cur == 0) {
                lastzero = iter;
                take_snap(&baseS);
                if (!best_valid || N > bestS.n) {
                    take_snap(&bestS);
                    best_valid = 1;
                }
                if (try_grow(N)) {
                    N++;
                    cur = 0;
                    continue;
                }
            }
            if (iter - lastzero > STAG) {
                load_snap(&baseS);
                cur = eval_cost(N);
                T = 1.0;
                lastzero = iter;
                continue;
            }
            nops = 0;
            double r = rndu();
            int ok;
            if (r < 0.2) ok = move_add(N);
            else if (r < 0.35) ok = move_rewire(N);
            else ok = move_swap(N);
            if (!ok) {
                undo_all();
                continue;
            }
            long long nc = eval_cost(N);
            long long delta = nc - cur;
            if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
                cur = nc;
                nops = 0;
            } else {
                undo_all();
            }
            T *= 0.99997;
            if (T < 0.15) T = 0.15;
        }
    }

    printf("%d %d\n", bestS.n, bestS.m);
    for (int i = 0; i < bestS.m; i++) printf("%d %d\n", bestS.eu[i], bestS.ev[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases (from the parent): PG(2,q) for D = 3, W(q) for D = 4.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver: best structured base, then the C annealer does the rest.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])

    cands = []
    if D >= 4:
        cands.append(_best_gq(d))
    if D >= 3:
        cands.append(_best_pg(d))
    for g in cands:
        if g is not None and g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = g

    if best[0] >= lib.moore_bound(d, D) or D < 2:
        return best[0], list(best[1])

    budget = max(0.5, 0.72 * time_limit - 1.0)
    try:
        out = lib.run_c(C_SOURCE, [d, D, int(seed) & 0xFFFFFFFF, f"{budget:.3f}"],
                        stdin_graph=best, timeout=0.85 * time_limit)
        n, e = lib.parse_graph_text(out)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass

    return best[0], list(best[1])
