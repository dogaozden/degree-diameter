"""Bold variant: base-extension lift search in C, with Python fallbacks.

Python picks a valid start (K_{d,d}, or a known construction for D = 3 or 4) and calls the C engine.
C searches for bi-regular voltage lifts over groups Z_m x|_r Z_k2 (including direct products, r = 1).
Instead of growing the graph by two vertices, it grows the BASE graph by one vertex pair at a time:
the existing darts keep their voltages, d darts are re-hooked to a new base vertex pair, and the
new darts are annealed. Left multiplication is an automorphism, so the diameter test is one BFS of
depth D from each of the 2*KB class representatives. Every output is re-checked in C and Python.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search: base-extension voltage lifts.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Model: base multigraph with KB vertices per side and ND = d*KB darts. Dart t = (DI[t], DJ[t], DS[t])
 * joins A_{i,g} to B_{j, g*DS[t]} for all g in the group G. Every A and every B has exactly d darts,
 * so the lift is d-regular. Moves: change one voltage, or swap the B-endpoints of two darts.
 * Both keep the degree counts. Cost = number of unreached (class representative, vertex) pairs.
 * Extension: pick d darts, move their B-endpoint to a new base vertex B', and add d darts from a
 * new base vertex A' to the old B-endpoints. Old voltages are kept, and the new darts are annealed.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXKB 12
#define MAXDART (MAXD * MAXKB)
#define BIGCOST 1000000000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

/* ------------------------------------------------------------ utilities */

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Upper bound on the order of a bipartite graph with max degree d and diameter D. */
static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* ------------------------------------------------------------ graph basics */

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

/* ------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance > D. Zero means diameter <= D. */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        total += n - c;
    }
    return total / 2;
}

static int is_valid(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

/* ------------------------------------------------------------ input / output */

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) { g->side[u] = 1 - g->side[v]; queue[tail++] = u; }
                else if (g->side[u] == g->side[v]) { g->n = 0; return; }
            }
        }
    }
    if (!is_valid(g)) g->n = 0;
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k2: element a*k2+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k2). r = 1 is a direct product. */
static int GM, GK2, GORD;
static int RP[MAXN];

static void set_group(int m, int k2, int r) {
    GM = m;
    GK2 = k2;
    GORD = m * k2;
    RP[0] = 1 % m;
    for (int b = 1; b < k2; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
}

static int gmul(int x, int y) {
    int a = x / GK2, b = x % GK2, c = y / GK2, e = y % GK2;
    return (int)(((long)a + (long)RP[b] * c) % GM) * GK2 + (b + e) % GK2;
}

/* Uniform reservoir pick over candidate groups of order G, including direct products (r = 1). */
static int pick_group(int G, int *om, int *ok2, int *orr) {
    int cnt = 0;
    for (int m = 1; m <= G; m++) {
        if (G % m) continue;
        int k2 = G / m;
        if (rndint(++cnt) == 0) { *om = m; *ok2 = k2; *orr = 1; }
        if (m > 2 && k2 > 1) {
            for (int t = 0; t < 60; t++) {
                int r = 2 + rndint(m - 2);
                if (gcd(r, m) != 1 || powmod(r, k2, m) != 1 % m) continue;
                if (rndint(++cnt) == 0) { *om = m; *ok2 = k2; *orr = r; }
            }
        }
    }
    return cnt > 0;
}

/* ------------------------------------------------------------ base-graph state */

static int KB, ND;
static int DI[MAXDART], DJ[MAXDART], DS[MAXDART];
static int LADJ[MAXN][MAXD];
static int LDEG[MAXN];
static int VIS[MAXN], VST = 0;
static int QU[MAXN];

static int SKB, SND;
static int SDI[MAXDART], SDJ[MAXDART], SDS[MAXDART];

static void save_state(void) {
    SKB = KB;
    SND = ND;
    memcpy(SDI, DI, sizeof(int) * ND);
    memcpy(SDJ, DJ, sizeof(int) * ND);
    memcpy(SDS, DS, sizeof(int) * ND);
}

static void restore_state(void) {
    KB = SKB;
    ND = SND;
    memcpy(DI, SDI, sizeof(int) * ND);
    memcpy(DJ, SDJ, sizeof(int) * ND);
    memcpy(DS, SDS, sizeof(int) * ND);
}

/* Random layered base with kb vertices per side: each layer is a permutation. */
static void init_state(int kb) {
    KB = kb;
    ND = d * kb;
    int perm[MAXKB];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < kb; i++) perm[i] = i;
        for (int i = kb - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < kb; i++) {
            int t = l * kb + i;
            DI[t] = i;
            DJ[t] = perm[i];
            DS[t] = rndint(GORD);
        }
    }
}

/* Base extension: d old darts get their B-endpoint moved to a new B' = KB; d new darts join
 * a new A' = KB to the old B-endpoints. Degrees of all old vertices are preserved. */
static void extend_state(void) {
    int oldND = ND;
    int chosen[MAXD];
    for (int k = 0; k < d; k++) {
        int t, ok;
        do {
            t = rndint(oldND);
            ok = 1;
            for (int q = 0; q < k; q++)
                if (chosen[q] == t) ok = 0;
        } while (!ok);
        chosen[k] = t;
    }
    for (int k = 0; k < d; k++) {
        int t = chosen[k];
        int j_old = DJ[t];
        DI[oldND + k] = KB;
        DJ[oldND + k] = j_old;
        DS[oldND + k] = rndint(GORD);
        DJ[t] = KB;
    }
    KB++;
    ND = oldND + d;
}

static int has_dup(void) {
    for (int a = 0; a < ND; a++)
        for (int b = a + 1; b < ND; b++)
            if (DI[a] == DI[b] && DJ[a] == DJ[b] && DS[a] == DS[b]) return 1;
    return 0;
}

static void build_ladj(void) {
    int N = 2 * KB * GORD;
    for (int v = 0; v < N; v++) LDEG[v] = 0;
    for (int t = 0; t < ND; t++)
        for (int g = 0; g < GORD; g++) {
            int a = DI[t] * GORD + g;
            int b = (KB + DJ[t]) * GORD + gmul(g, DS[t]);
            LADJ[a][LDEG[a]++] = b;
            LADJ[b][LDEG[b]++] = a;
        }
}

/* Unreached (class representative, vertex) pairs over the 2KB representatives. */
static long orbit_cost(void) {
    int cA[MAXKB], cB[MAXKB];
    for (int i = 0; i < KB; i++) cA[i] = cB[i] = 0;
    for (int t = 0; t < ND; t++) { cA[DI[t]]++; cB[DJ[t]]++; }
    for (int i = 0; i < KB; i++)
        if (cA[i] != d || cB[i] != d) return BIGCOST;
    if (has_dup()) return BIGCOST;
    build_ladj();
    int N = 2 * KB * GORD;
    long total = 0;
    for (int rep = 0; rep < 2 * KB; rep++) {
        int src = rep * GORD;
        if (++VST >= 2000000000) { memset(VIS, 0, sizeof VIS); VST = 1; }
        int head = 0, tail = 0;
        VIS[src] = VST;
        QU[tail++] = src;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int u = QU[head++];
                for (int i = 0; i < LDEG[u]; i++) {
                    int v = LADJ[u][i];
                    if (VIS[v] != VST) { VIS[v] = VST; QU[tail++] = v; }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

/* Annealing on the current base. Returns the final cost (0 means a valid lift). */
static long anneal(long steps) {
    long cost = orbit_cost();
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 31) == 0 && now() > t_end) break;
        double T = 1.5 * (1.0 - (double)s / (double)steps) + 0.05;
        if (rnd01() < 0.75) {
            int t = rndint(ND);
            int old = DS[t];
            int nv = rndint(GORD);
            if (nv == old) continue;
            DS[t] = nv;
            long c2 = orbit_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else DS[t] = old;
        } else {
            int t1 = rndint(ND), t2 = rndint(ND);
            if (t1 == t2 || DJ[t1] == DJ[t2]) continue;
            int tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp;
            long c2 = orbit_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else { tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp; }
        }
    }
    return cost;
}

static void build_full(Graph *g) {
    int N = 2 * KB * GORD;
    g->n = N;
    for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = v >= KB * GORD; }
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < GORD; x++)
            add_edge(g, DI[t] * GORD + x, (KB + DJ[t]) * GORD + gmul(x, DS[t]));
}

static void record(Graph *best, Graph *cand) {
    build_full(cand);
    if (cand->n > best->n && is_valid(cand)) copy_graph(best, cand);
}

/* Repeated runs: pick a group, anneal a small base to a valid lift, then extend the base
 * one vertex pair at a time while annealing. Every valid state is recorded. */
static void lift_runs(Graph *best, double until) {
    static Graph cand;
    long cap = moore_bound();
    if (cap > MAXN) cap = MAXN;
    while (now() < until) {
        int kb0 = 1 + rndint(2);
        long glo = best->n / (2L * MAXKB) + 2;
        long ghi = cap / (2L * kb0);
        if (ghi > 3 * glo) ghi = 3 * glo;
        if (ghi < glo) return;
        long G = glo + rndint((int)(ghi - glo + 1));
        int m, k2, r;
        if (!pick_group((int)G, &m, &k2, &r)) continue;
        set_group(m, k2, r);
        init_state(kb0);
        if (anneal(4000 + rndint(4000)) != 0) continue;
        record(best, &cand);
        int fails = 0;
        while (now() < until && KB < MAXKB && 2L * (KB + 1) * GORD <= cap) {
            save_state();
            extend_state();
            if (anneal(6000 + rndint(6000)) == 0) {
                fails = 0;
                record(best, &cand);
            } else {
                restore_state();
                if (++fails >= 3) break;
            }
        }
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (d == 1 || D < 2) { printf("2 1\n0 1\n"); return 0; }

    static Graph best, start;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    copy_graph(&start, &best);

    if (best.n < moore_bound()) lift_runs(&best, t_end);
    if (!is_valid(&best)) copy_graph(&best, &start);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, degree q+1."""
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


def known_start(d, D):
    """Best known construction Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    if D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q) and q + 1 <= d:
                return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))          # K_{d,d}: valid for D >= 2
    try:
        start = known_start(d, D)
    except (ValueError, RuntimeError):
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
