"""Non-abelian group-lift search, then grow-by-two.

Python builds explicit multiplication tables for small groups (non-solvable ones such as
A5 x Z_k, PSL(2,7), PGL(2,7), SL(2,5), and solvable ones such as S4, A4, SL(2,3) and
direct and semidirect products). Each table is passed to the C engine, which searches for
voltage lifts: base with kb vertices per side, d darts per base vertex, darts labelled by
group elements. Left multiplication is an automorphism of every such lift, so the diameter
is checked with 2kb BFS runs. Groups are tried in order of closeness to order 168, the order
that gives a 336-vertex Haar graph. The best lift is then grown by two. Every output is
checked in Python with lib.is_valid, and the previous valid graph is kept as the fallback.
"""
import itertools
import math
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search: group-table lift search, then grow-by-two.
 *
 * Usage: prog d D seed time_limit mode
 *   mode "lift": stdin is a start graph, followed by a group block encoded as edges:
 *                the pair (-1, G), then G*G pairs (x*G+y, x*y) with the table of a group
 *                of order G whose identity is element 0.
 *   mode "grow": stdin is a start graph only.
 * stdout: "n m" then m lines "u v" for the largest valid graph found.
 *
 * Lift: dart (i, j, s) joins A_{i,g} to B_{j, g*s}. Left multiplication by x is an
 * automorphism (needs associativity), so diameter <= D iff a BFS of depth D from each of the
 * 2kb representatives A_{i,e}, B_{j,e} reaches everything.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1536
#define MAXW 24
#define MAXD 16
#define MAXG 400
#define MAXK 3
#define MAXDART (MAXD * MAXK)
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

/* ------------------------------------------------------------ group globals */

static int GO = 0;                       /* group order, 0 = no group */
static unsigned short MT[MAXG][MAXG];    /* MT[x][y] = x*y, identity is 0 */

/* ------------------------------------------------------------ input / output */

static void read_input(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    int *buf = (int *)malloc(sizeof(int) * 2 * (size_t)(m + 1));
    if (!buf) return;
    for (int i = 0; i < 2 * m; i++)
        if (scanf("%d", &buf[i]) != 1) { free(buf); return; }
    int s = m;
    for (int e = 0; e < m; e++)
        if (buf[2 * e] == -1) { s = e; break; }

    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    int ok = 1;
    for (int e = 0; e < s && ok; e++) {
        int u = buf[2 * e], v = buf[2 * e + 1];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) ok = 0;
        else add_edge(g, u, v);
    }
    GO = 0;
    if (ok && s < m) {
        int G = buf[2 * s + 1];
        if (G < 1 || G > MAXG || m - s - 1 != G * G) ok = 0;
        else {
            for (int k = 0; k < G * G; k++) {
                int p = s + 1 + k;
                int key = buf[2 * p], val = buf[2 * p + 1];
                if (key < 0 || key >= G * G || val < 0 || val >= G) { ok = 0; break; }
                MT[key / G][key % G] = (unsigned short)val;
            }
            if (ok) GO = G;
        }
    }
    free(buf);
    if (!ok) { g->n = 0; GO = 0; return; }

    static int queue[MAXN];
    for (int s0 = 0; s0 < n; s0++) {
        if (g->side[s0] != 255) continue;
        int head = 0, tail = 0;
        g->side[s0] = 0;
        queue[tail++] = s0;
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

/* ------------------------------------------------------------ voltage lifts */

static int KB, ND;
static int DI[MAXDART], DJ[MAXDART], DS[MAXDART];
static int DPERM[MAXDART][MAXG];   /* DPERM[t][g] = g * DS[t] */
static int LADJ[MAXN][MAXD];
static int LDEG[MAXN];
static int VIS[MAXN], VST = 0;
static int QU[MAXN];

static void set_dart_perm(int t) {
    for (int g = 0; g < GO; g++) DPERM[t][g] = MT[g][DS[t]];
}

static int has_dup(void) {
    for (int t1 = 0; t1 < ND; t1++)
        for (int t2 = t1 + 1; t2 < ND; t2++)
            if (DI[t1] == DI[t2] && DJ[t1] == DJ[t2] && DS[t1] == DS[t2]) return 1;
    return 0;
}

static void build_ladj(void) {
    int N = 2 * KB * GO;
    for (int v = 0; v < N; v++) LDEG[v] = 0;
    for (int t = 0; t < ND; t++)
        for (int g = 0; g < GO; g++) {
            int a = DI[t] * GO + g;
            int b = (KB + DJ[t]) * GO + DPERM[t][g];
            LADJ[a][LDEG[a]++] = b;
            LADJ[b][LDEG[b]++] = a;
        }
}

/* Unreached (representative, vertex) pairs over the 2KB class representatives. */
static long orbit_cost(void) {
    if (has_dup()) return BIGCOST;
    build_ladj();
    int N = 2 * KB * GO;
    long total = 0;
    for (int rep = 0; rep < 2 * KB; rep++) {
        int src = rep * GO;
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
    int N = 2 * KB * GO;
    g->n = N;
    for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = v >= KB * GO; }
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < GO; x++)
            add_edge(g, DI[t] * GO + x, (KB + DJ[t]) * GO + DPERM[t][x]);
}

/* One annealing run over voltages and layer permutations. */
static int lift_climb(int kb, long steps, Graph *out) {
    KB = kb;
    ND = d * kb;
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
            DS[t] = rndint(GO);
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
            int nv = rndint(GO);
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

static void lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        /* kb = 1 most of the time: 2*GO vertices; kb = 2 gives 4*GO. */
        int kb = (rndint(5) == 0) ? 2 : 1;
        long N = 2L * kb * GO;
        if (N <= best->n || N > moore || N > MAXN) {
            kb = 3 - kb;
            N = 2L * kb * GO;
            if (N <= best->n || N > moore || N > MAXN) return;
        }
        long extra = (long)(fails / 20) * 3000;
        if (extra > 60000) extra = 60000;
        long steps = 4000 + rndint(8000) + extra;
        if (lift_climb(kb, steps, &cand) && cand.n > best->n && is_valid(&cand)) {
            copy_graph(best, &cand);
            fails = 0;
        } else {
            fails++;
        }
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
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit lift|grow < input\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lift_mode = argv[5][0] == 'l';
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (d == 1 || D < 2) { printf("2 1\n0 1\n"); return 0; }

    static Graph best, start;
    read_input(&best);
    if (best.n == 0) { GO = 0; complete_bipartite(&best); }
    copy_graph(&start, &best);

    if (best.n < moore_bound()) {
        if (lift_mode) {
            if (GO > 0) lift_search(&best, t_end);
        } else {
            GO = 0;
            grow_search(&best, t_end);
        }
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


# ------------------------------------------------------------ group tables

GROUP_CAP = 400


def _closure(gens, mul, ident, cap=GROUP_CAP):
    """Multiplication table (list of lists, identity = index 0) of the group generated by gens, or None if larger than cap."""
    elems = [ident]
    idx = {ident: 0}
    frontier = [ident]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = mul(x, g)
                if y not in idx:
                    if len(elems) >= cap:
                        return None
                    idx[y] = len(elems)
                    elems.append(y)
                    nxt.append(y)
        frontier = nxt
    return [[idx[mul(a, b)] for b in elems] for a in elems]


def _perm_group(gens):
    n = len(gens[0])

    def mul(p, q):
        return tuple(p[q[i]] for i in range(n))

    return _closure(gens, mul, tuple(range(n)))


def _mat_group(p, gens, projective):
    """Group of 2x2 matrices over GF(p) generated by gens; projective=True works in PGL(2,p)."""
    def canon(m):
        if not projective:
            return m
        c = next(x for x in m if x % p)
        ci = pow(c, p - 2, p)
        return tuple((x * ci) % p for x in m)

    def mul(A, B):
        a, b, c, d = A
        e, f, g, h = B
        return canon(((a * e + b * g) % p, (a * f + b * h) % p,
                      (c * e + d * g) % p, (c * f + d * h) % p))

    return _closure([canon(tuple(g)) for g in gens], mul, canon((1, 0, 0, 1)))


def _cyc(k):
    return [[(a + b) % k for b in range(k)] for a in range(k)]


def _direct(T1, T2):
    """Direct product of two multiplication tables."""
    h1, h2 = len(T1), len(T2)
    n = h1 * h2
    T = [[0] * n for _ in range(n)]
    for a1 in range(h1):
        for b1 in range(h2):
            row = T[a1 * h2 + b1]
            for a2 in range(h1):
                r1 = T1[a1][a2] * h2
                for b2 in range(h2):
                    row[a2 * h2 + b2] = r1 + T2[b1][b2]
    return T


def _semi(m, k, r):
    """Table of the semidirect product Z_m x| Z_k with multiplier r."""
    order, mul, _ = lib.semidirect_group(m, k, r)
    return [[mul(x, y) for y in range(order)] for x in range(order)]


def _A5():
    return _perm_group([(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)])


def _S5():
    return _perm_group([(1, 2, 0, 3, 4), (1, 2, 3, 4, 0), (1, 0, 2, 3, 4)])


def _A4():
    return _perm_group([(1, 2, 0, 3), (1, 0, 3, 2)])


def _S4():
    return _perm_group([(1, 2, 0, 3), (1, 0, 2, 3), (1, 2, 3, 0)])


def _SL25():
    return _mat_group(5, [(1, 1, 0, 1), (0, 4, 1, 0)], False)


def _SL23():
    return _mat_group(3, [(1, 1, 0, 1), (0, 2, 1, 0)], False)


def _PSL27():
    return _mat_group(7, [(1, 1, 0, 1), (0, 6, 1, 0)], True)


def _catalog(lo, hi):
    """Map order -> (priority, builder) for groups with lo <= order <= hi. Lower priority is preferred."""
    cat = {}

    def add(G, pr, fn):
        if lo <= G <= hi and (G not in cat or pr < cat[G][0]):
            cat[G] = (pr, fn)

    # Non-solvable and other high-value groups first.
    for k in range(1, 7):
        add(60 * k, 0 if k == 1 else 1, lambda k=k: _direct(_A5(), _cyc(k)))
    add(120, 0, _S5)
    add(240, 1, lambda: _direct(_S5(), _cyc(2)))
    add(120, 0, _SL25)
    add(240, 1, lambda: _direct(_SL25(), _cyc(2)))
    add(168, 0, _PSL27)
    add(336, 1, lambda: _direct(_PSL27(), _cyc(2)))
    add(336, 0, lambda: _mat_group(7, [(1, 1, 0, 1), (0, 6, 1, 0)], False))   # SL(2,7)
    add(336, 0, lambda: _mat_group(7, [(1, 1, 0, 1), (0, 6, 1, 0), (3, 0, 0, 1)], True))  # PGL(2,7)

    # Solvable non-abelian families.
    for k in range(1, GROUP_CAP // 12 + 1):
        add(12 * k, 2, lambda k=k: _direct(_A4(), _cyc(k)))
    for k in range(1, GROUP_CAP // 24 + 1):
        add(24 * k, 2, lambda k=k: _direct(_S4(), _cyc(k)))
        add(24 * k, 2, lambda k=k: _direct(_SL23(), _cyc(k)))

    # Abelian direct products Z_a x Z_b (non-cyclic), not covered by cyclic lifts.
    for a in range(2, 9):
        for b in range(a, hi // a + 1):
            add(a * b, 3, lambda a=a, b=b: _direct(_cyc(a), _cyc(b)))

    # Semidirect Z_m x| Z_k with a single multiplier r (inversion or small).
    for m in range(3, hi + 1):
        for k in range(2, hi // m + 1):
            G = m * k
            if G < lo or G > hi:
                continue
            cands = list(range(2, min(m, 60))) + [m - 1]
            for r in cands:
                if 1 <= r < m and math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    add(G, 3, lambda m=m, k=k, r=r: _semi(m, k, r))
                    break

    # Cyclic groups (lowest priority, parent already searches these).
    for G in range(max(2, lo), hi + 1):
        add(G, 4, lambda G=G: _cyc(G))
    return cat


def _liftable(G, cur_n, moore):
    """True if a lift over a group of order G (kb = 1 or 2) can beat cur_n and stay within the Moore bound."""
    if G < 2 or G > GROUP_CAP:
        return False
    return (2 * G > cur_n and 2 * G <= moore) or (4 * G > cur_n and 4 * G <= moore)


def _pick_groups(cat, cur_n, moore, cap=14):
    items = [(G, pr, fn) for G, (pr, fn) in cat.items() if _liftable(G, cur_n, moore)]
    items.sort(key=lambda t: (abs(t[0] - 168), t[1]))
    return items[:cap]


def _lift_call(best, G, fn, seconds, d, D, seed):
    """Run the C lift search over one group. Returns a verified larger graph or None."""
    table = fn()
    if table is None or len(table) != G:
        return None
    edges = list(best[1])
    edges.append((-1, G))
    edges.extend((x * G + y, table[x][y]) for x in range(G) for y in range(G))
    text = lib.run_c(C_SOURCE, [d, D, seed, round(seconds, 2), "lift"],
                     stdin_graph=(best[0], edges), timeout=seconds + 8)
    n, out = lib.parse_graph_text(text)
    if n > best[0] and lib.is_valid(n, out, d, D):
        return n, out
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

    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d > 15:
        return best

    deadline = t0 + 0.85 * time_limit - 1.0
    if deadline - time.monotonic() < 1.0:
        return best

    try:
        cat = _catalog(max(2, best[0] // 4), min(GROUP_CAP, moore // 2))
    except (ValueError, RuntimeError):
        return best
    pending = _pick_groups(cat, best[0], moore)

    while pending:
        rem = deadline - time.monotonic()
        if rem < 1.0:
            break
        G, _, fn = pending.pop(0)
        if not _liftable(G, best[0], moore):
            continue
        sec = max(0.5, rem / (len(pending) + 1))
        try:
            res = _lift_call(best, G, fn, sec, d, D, seed)
        except (RuntimeError, ValueError, OSError, MemoryError):
            res = None
        if res is not None:
            best = res

    rem = deadline - time.monotonic()
    if rem >= 1.0 and best[0] < moore:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(rem, 2), "grow"],
                             stdin_graph=best, timeout=rem + 5)
            n, edges = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except (RuntimeError, ValueError, OSError):
            pass
    return best
