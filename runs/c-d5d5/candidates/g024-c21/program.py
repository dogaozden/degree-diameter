"""Generic-group voltage lifts in C, with grow-by-two annealing.

Change from the parent: the lift search no longer uses only metacyclic groups Z_m x| Z_k.
Python builds full multiplication tables for two families and passes them to C:
  * affine groups F_q x| C_h, with q a non-prime prime power (for example 9, 16, 25, 64) and C_h
    acting by multiplication. These are generally NOT metacyclic.
  * metacyclic groups Z_m x| Z_k (a few random members).
C checks each table (identity, row and column permutations), then runs voltage lifts over random
groups from the list with kb in {1,2,3} base vertices per side. Left multiplication is an
automorphism, so the diameter is checked by 2kb BFS runs. A valid lift is grown by two with
annealing. The start graph is always valid (K_{d,d}, or a known construction for D = 3 or 4),
so every case returns a valid graph.

Transport: lib.run_c only takes a graph on stdin, so the group tables are packed into the
edge list of the stdin graph as integer pairs, and C reads them back as a flat integer stream.
"""
import itertools
import math
import random
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core, generic group tables.
 *
 * Usage:   prog d D seed time_limit   < stdin
 * stdin:   header "n m" (ignored), then the stream:
 *            NG, then NG blocks of: G, then G*G integers (row-major multiplication table,
 *            identity = element 0), then the start graph as "n m" and m lines "u v".
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Lift: base with kb vertices per side, d layers; layer l is a permutation of the kb base
 *   vertices, so each base vertex has one dart per layer. Dart (i, j, s) joins A_{i,g} to
 *   B_{j, g*s}. Left multiplication is an automorphism, so the diameter is <= D iff a BFS of
 *   depth D from each of the 2kb representatives A_{i,e}, B_{j,e} reaches everything.
 * Grow: add one vertex per side, then anneal degree-preserving edge swaps.
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
#define MAXK 3
#define MAXDART (MAXD * MAXK)
#define MAXG 400
#define MAXGR 16
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

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void del_half(Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][--g->deg[u]];
            return;
        }
}

static void del_edge(Graph *g, int u, int v) {
    del_half(g, u, v);
    del_half(g, v, u);
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
static int badv[MAXN];

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
        badv[v] = n - c;
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

static int NGR = 0;
static int GRD[MAXGR];
static int GTAB[MAXGR][MAXG * MAXG];

/* Latin-square check plus identity at element 0. */
static int check_group(const int *T, int G) {
    static int seen[MAXG];
    static int stc = 0;
    for (int x = 0; x < G; x++)
        if (T[x] != x || T[x * G] != x) return 0;
    for (int x = 0; x < G; x++) {
        stc++;
        for (int y = 0; y < G; y++) {
            int v = T[x * G + y];
            if (seen[v] == stc) return 0;
            seen[v] = stc;
        }
        stc++;
        for (int y = 0; y < G; y++) {
            int v = T[y * G + x];
            if (seen[v] == stc) return 0;
            seen[v] = stc;
        }
    }
    return 1;
}

static int read_groups(void) {
    int ng;
    if (scanf("%d", &ng) != 1 || ng < 0) return 0;
    for (int gi = 0; gi < ng; gi++) {
        int G;
        if (scanf("%d", &G) != 1 || G < 1 || G > MAXG) return 0;
        if (NGR >= MAXGR) return 0;
        int *T = GTAB[NGR];
        int ok = 1;
        for (int i = 0; i < G * G; i++) {
            int v;
            if (scanf("%d", &v) != 1) return 0;
            if (v < 0 || v >= G) { ok = 0; v = 0; }
            T[i] = v;
        }
        if (ok && check_group(T, G)) { GRD[NGR] = G; NGR++; }
    }
    return 1;
}

/* ------------------------------------------------------------ voltage lifts */

static int KB, ND, GORD;
static const int *CUR;             /* multiplication table of the current group */
static int DI[MAXDART], DJ[MAXDART], DS[MAXDART];
static int DPERM[MAXDART][MAXG];   /* DPERM[t][g] = g * DS[t] */
static int LADJ[MAXN][MAXD];
static int LDEG[MAXN];
static int VIS[MAXN], VST = 0;
static int QU[MAXN];

static void set_dart_perm(int t) {
    for (int g = 0; g < GORD; g++) DPERM[t][g] = CUR[g * GORD + DS[t]];
}

static int has_dup(void) {
    for (int t1 = 0; t1 < ND; t1++)
        for (int t2 = t1 + 1; t2 < ND; t2++)
            if (DI[t1] == DI[t2] && DJ[t1] == DJ[t2] && DS[t1] == DS[t2]) return 1;
    return 0;
}

static void build_ladj(void) {
    int N = 2 * KB * GORD;
    for (int v = 0; v < N; v++) LDEG[v] = 0;
    for (int t = 0; t < ND; t++)
        for (int g = 0; g < GORD; g++) {
            int a = DI[t] * GORD + g;
            int b = (KB + DJ[t]) * GORD + DPERM[t][g];
            LADJ[a][LDEG[a]++] = b;
            LADJ[b][LDEG[b]++] = a;
        }
}

/* Unreached (representative, vertex) pairs over the 2KB class representatives. */
static long orbit_cost(void) {
    if (has_dup()) return BIGCOST;
    build_ladj();
    int N = 2 * KB * GORD;
    long total = 0;
    for (int rep = 0; rep < 2 * KB; rep++) {
        int src = rep * GORD;
        VST++;
        int head = 0, tail = 0;
        VIS[src] = VST;
        QU[tail++] = src;
        for (int depth = 0; depth < D; depth++) {
            int end = tail;
            if (head == end) break;
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

static void build_full(Graph *g) {
    int N = 2 * KB * GORD;
    g->n = N;
    for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = v >= KB * GORD; }
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < GORD; x++)
            add_edge(g, DI[t] * GORD + x, (KB + DJ[t]) * GORD + DPERM[t][x]);
}

/* One annealing run over voltages and layer permutations for group gi. */
static int lift_climb(int gi, int kb, long steps, Graph *out) {
    KB = kb;
    ND = d * kb;
    CUR = GTAB[gi];
    GORD = GRD[gi];
    int perm[MAXK];
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
            set_dart_perm(t);
        }
    }
    long cost = orbit_cost();
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 31) == 0 && now() > t_end) return 0;
        double T = 2.0 * (1.0 - (double)s / (double)steps) + 0.05;
        if (rnd01() < 0.7) {
            int t = rndint(ND);
            int old = DS[t];
            int nv = rndint(GORD);
            if (nv == old) continue;
            DS[t] = nv;
            set_dart_perm(t);
            long c2 = orbit_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else { DS[t] = old; set_dart_perm(t); }
        } else {
            if (kb < 2) continue;
            int l = rndint(d);
            int i1 = rndint(kb), i2 = rndint(kb);
            if (i1 == i2) continue;
            int t1 = l * kb + i1, t2 = l * kb + i2;
            int tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp;
            long c2 = orbit_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else { tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp; }
        }
    }
    if (cost != 0) return 0;
    build_full(out);
    return 1;
}

static Graph LCAND;

static void lift_search(Graph *best, double until) {
    long moore = moore_bound();
    while (now() < until) {
        if (best->n + 2 > moore) return;
        int gi = rndint(NGR);
        int kb = 1 + rndint(3);
        long N = 2L * kb * GRD[gi];
        if (N <= best->n || N > moore || N > MAXN || kb * d > MAXDART) continue;
        long steps = 3000 + rndint(9000);
        if (lift_climb(gi, kb, steps, &LCAND) && LCAND.n > best->n && is_valid(&LCAND))
            copy_graph(best, &LCAND);
    }
}

/* ------------------------------------------------------------ grow by two */

static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
    long bad = bad_pairs(work);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (work->side[s] != work->side[v] || s == v || work->deg[s] == 0) continue;
        int t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
        long nb = bad_pairs(work);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(work, v, t);
            del_edge(work, s, u);
            add_edge(work, v, u);
            add_edge(work, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

static void grow_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound() && best->n + 2 <= MAXN) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < stdin\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    int hn = 0, hm = 0;
    if (scanf("%d %d", &hn, &hm) != 2) { hn = 0; hm = 0; }
    (void)hn;
    (void)hm;

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (d == 1 || D < 2) { printf("2 1\n0 1\n"); return 0; }

    read_groups();

    static Graph best, start;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    copy_graph(&start, &best);

    long moore = moore_bound();
    if (best.n < moore && NGR > 0) {
        lift_search(&best, t0 + (t_end - t0) * 0.7);
    }
    if (best.n < moore) {
        grow_search(&best, t_end);
    }
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


def _pp_exp(q):
    """Exponent k if q = p^k (k >= 1), else 0."""
    if q < 2:
        return 0
    p = next(x for x in range(2, q + 1) if q % x == 0)
    k = 0
    while q % p == 0:
        q //= p
        k += 1
    return k if q == 1 else 0


def _table_aff(q, h):
    """Multiplication table of F_q x| C_h (affine maps x -> c*x + b, c in a subgroup of order h).
    Element (b, e) is coded as b*h + e; identity is 0."""
    F = lib.GF(q)
    g = F.primitive_element()
    step = (q - 1) // h
    G = q * h
    Cv = np.array([F.pow(g, e * step) for e in range(h)], dtype=np.int64)
    idx = np.arange(G, dtype=np.int64)
    b, e = idx // h, idx % h
    inner = F.mul_table[Cv[e][:, None], b[None, :]]    # c_{e1} * b2
    Bv = F.add_table[b[:, None], inner]                # b1 + c_{e1} * b2
    Ev = (e[:, None] + e[None, :]) % h
    return (Bv * h + Ev).astype(np.int64)


def _table_met(m, k, r):
    """Multiplication table of Z_m x|_r Z_k; element (a, b) is coded as a*k + b; identity is 0."""
    G = m * k
    idx = np.arange(G, dtype=np.int64)
    a, bb = idx // k, idx % k
    RP = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    A = (a[:, None] + RP[bb][:, None] * a[None, :]) % m
    B = (bb[:, None] + bb[None, :]) % k
    return (A * k + B).astype(np.int64)


def _pick_groups(seed, moore):
    """Sample a few group tables (affine non-prime-power families plus metacyclic) with orders in range."""
    Gmin = max(3, moore // 12)
    Gmax = min(340, moore // 2)
    if Gmax < Gmin:
        return []
    aff, met = [], []
    for q in range(4, Gmax + 1):
        if _pp_exp(q) < 2:          # only non-prime prime powers: these are not metacyclic
            continue
        for h in range(1, q):
            if (q - 1) % h == 0 and Gmin <= q * h <= Gmax:
                aff.append((q, h))
    for G in range(Gmin, Gmax + 1):
        for m in range(1, G + 1):
            if G % m:
                continue
            k = G // m
            if m == 1 or k == 1:
                met.append((m, k, 1))
                continue
            rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            for r in rs[:3]:
                met.append((m, k, r))
    rng = random.Random(seed * 7919 + 101)
    chosen_aff = rng.sample(aff, min(len(aff), 7))
    chosen_met = rng.sample(met, min(len(met), 3))
    out = []
    for q, h in chosen_aff:
        out.append((q * h, _table_aff(q, h)))
    for m, k, r in chosen_met:
        out.append((m * k, _table_met(m, k, r)))
    return out


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

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    try:
        groups = _pick_groups(seed, moore)
    except (ValueError, RuntimeError, ZeroDivisionError):
        groups = []
    if not groups:
        return best

    # Pack the group tables and the start graph into the integer stream (see C header).
    stream = [len(groups)]
    for G, T in groups:
        stream.append(G)
        stream.extend(T.ravel().tolist())
    stream += [best[0], len(best[1])]
    for u, v in best[1]:
        stream += [u, v]
    if len(stream) % 2:
        stream.append(0)
    pairs = list(zip(stream[0::2], stream[1::2]))

    # Use most of the limit; keep a margin for compilation and process startup.
    budget = 0.92 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=(1, pairs), timeout=budget + 3)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
