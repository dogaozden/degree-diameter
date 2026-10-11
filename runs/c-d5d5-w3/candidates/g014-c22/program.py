"""Non-solvable and direct-product voltage lifts, then grow-by-pairs annealing.

Changed construction: the parent only lifted over semidirect products Z_m x| Z_k. This
version also lifts over permutation groups from a catalogue (A5 x Z_k, S4 x Z_k, SL(2,5),
SL(2,3) x Z_8, PSL(2,7), PGL(2,7), GL(2,3), affine groups AGL(1,q)), plus a few
semidirect products. Each candidate has order near 0.55 * Moore bound / (2 kb), so the
lift has about 2 kb |G| vertices. Python passes the group as a multiplication table
(encoded as an edge list, since lib.run_c only takes a graph on stdin). C searches
voltages in that group with annealing on unreached (representative, vertex) pairs.
The best lift is then grown by repair annealing.

Safety: every stage starts from a validated graph (K_{d,d}, or a known construction),
only accepts strictly larger graphs that pass lib.is_valid, and keeps the previous best
on any error or timeout.
"""
import itertools
import math
import random
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core (lift mode + grow mode).
 *
 * Usage: prog d D seed time_limit mode kb
 *   mode 0 (lift): stdin = group table as a graph "G G*G" with edges (i, T[i][j]) in
 *     row-major order. Searches voltage lifts over that group with kb base vertices per
 *     side (d darts out of each base vertex). Prints the best lift, or K_{d,d}.
 *   mode 1 (grow): stdin = a valid start graph ("n m" then edges, or "0 0").
 *     Grows it by pairs of vertices with repair annealing.
 * Output: "n m" then m lines "u v".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1024
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXK 4
#define MAXG 400
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
static double LIFT_END;

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

/* ------------------------------------------------------------ group table */

static int GORD = 0;
static int GT[MAXG][MAXG];

/* Reads "G m" then m = G*G lines "u v" with u = row, v = T[row][col], row-major. */
static int read_table(void) {
    int G, m;
    if (scanf("%d %d", &G, &m) != 2) return 0;
    if (G < 1 || G > MAXG || m != G * G) return 0;
    for (int k = 0; k < m; k++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u != k / G || v < 0 || v >= G) return 0;
        GT[u][k % G] = v;
    }
    GORD = G;
    return 1;
}

/* ------------------------------------------------------------ voltage lifts */

static int KB, ND;
static int DI[MAXDART], DJ[MAXDART], DS[MAXDART];
static int DPERM[MAXDART][MAXG];   /* DPERM[t][g] = g * DS[t] in the group */
static int LADJ[MAXN][MAXD];
static int LDEG[MAXN];
static int VIS[MAXN], VST = 0;
static int QU[MAXN];

static void set_dart_perm(int t) {
    for (int g = 0; g < GORD; g++) DPERM[t][g] = GT[g][DS[t]];
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

/* Unreached (representative, vertex) pairs over the 2KB class representatives.
 * Left multiplication is an automorphism of the lift, so this is zero iff diameter <= D. */
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

/* One annealing run over voltages and layer swaps. On success, out holds the full lift. */
static int lift_climb(int kb, long steps, Graph *out) {
    KB = kb;
    ND = d * kb;
    int G = GORD;
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
            DS[t] = rndint(G);
            set_dart_perm(t);
        }
    }
    long cost = orbit_cost();
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 31) == 0 && now() > LIFT_END) return 0;
        double T = 2.0 * (1.0 - (double)s / (double)steps) + 0.05;
        if (rnd01() < 0.7) {
            int t = rndint(ND);
            int old = DS[t];
            int nv = rndint(G);
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

/* Restarts lift_climb with the fixed group until a lift larger than the best is found
 * (the group order is fixed, so a lift of order 2 kb |G| is the only target). */
static void lift_search(Graph *best, int kb, double until) {
    long moore = moore_bound();
    LIFT_END = until;
    long N = 2L * kb * GORD;
    if (N > moore || N > MAXN) return;
    int tries = 0;
    while (now() < until && N > best->n) {
        long steps = 3000 + rndint(6000) + (long)tries * 50;
        if (steps > 40000) steps = 40000;
        tries++;
        if (lift_climb(kb, steps, &LCAND) && LCAND.n > best->n && is_valid(&LCAND))
            copy_graph(best, &LCAND);
    }
}

/* ------------------------------------------------------------ grow by pairs */

/* Adds g pairs of new vertices (x side 0, y side 1, joined to each other), so the order
 * rises by 2g. Each pair steals d-1 old edges: x takes the far end b of an old edge a-b,
 * and y takes a. Old vertices are used at most once per call, so degrees stay exact.
 * Then annealing swaps edges until the diameter bound holds. */
static int grow_once(const Graph *best, Graph *work, double until, int g) {
    int n = best->n;
    if (g < 1) return 0;
    if (n + 2 * g > moore_bound() || n + 2 * g > MAXN) return 0;
    copy_graph(work, best);
    work->n = n + 2 * g;
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    for (int p = 0; p < g; p++) {
        int x = n + 2 * p, y = x + 1;
        work->deg[x] = work->deg[y] = 0;
        work->side[x] = 0;
        work->side[y] = 1;
        add_edge(work, x, y);
        used[x] = used[y] = stamp;
    }
    for (int p = 0; p < g; p++) {
        int x = n + 2 * p, y = x + 1;
        for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
            int a = rndint(n);
            if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
            int b = work->adj[a][rndint(work->deg[a])];
            if (b >= n || used[b] == stamp) continue;
            del_edge(work, a, b);
            add_edge(work, x, b);
            add_edge(work, y, a);
            used[a] = used[b] = stamp;
            k++;
        }
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
    int fails = 0;
    while (now() < until) {
        long lim = moore_bound();
        if (lim > MAXN) lim = MAXN;
        /* Every third failure, try a jump of two pairs (four vertices). */
        int g = (fails % 3 == 2) ? 2 : 1;
        if (best->n + 2 * g > lim) g = 1;
        if (best->n + 2 * g > lim) break;
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice, g)) {
            copy_graph(best, &work);
            fails = 0;
        } else {
            fails++;
        }
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit mode kb\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int mode = argc > 5 ? atoi(argv[5]) : 1;
    int kb = argc > 6 ? atoi(argv[6]) : 1;
    double t0 = now();
    t_end = t0 + limit * 0.97;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (d == 1 || D < 2) { printf("2 1\n0 1\n"); return 0; }

    static Graph best;
    if (mode == 0) {
        complete_bipartite(&best);
        if (read_table() && kb >= 1 && kb <= MAXK) lift_search(&best, kb, t_end);
    } else {
        read_start(&best);
        if (best.n == 0) complete_bipartite(&best);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ---------------------------------------------------------------- constructions

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


# ------------------------------------------------ permutation-group catalogue

def _compose(p, q):
    """(p * q)(i) = p[q[i]]."""
    return tuple(p[i] for i in q)


def _perm_group(gens, cap=400):
    """Closure of permutation generators: (elements, index), or None if the order exceeds cap."""
    n = len(gens[0])
    e = tuple(range(n))
    elems = [e]
    index = {e: 0}
    i = 0
    while i < len(elems):
        x = elems[i]
        i += 1
        for g in gens:
            y = _compose(x, g)
            if y not in index:
                if len(elems) >= cap:
                    return None
                index[y] = len(elems)
                elems.append(y)
    return elems, index


def _perm_table(elems, index):
    return [[index[_compose(a, b)] for b in elems] for a in elems]


def _sym_gens(k):
    return [(1, 0) + tuple(range(2, k)), tuple(range(1, k)) + (0,)]


def _three_cycle(k, j):
    p = list(range(k))
    p[0], p[1], p[j] = 1, j, 0
    return tuple(p)


def _alt_gens(k):
    return [_three_cycle(k, j) for j in range(2, k)]


def _cyc_gens(k):
    return [tuple(range(1, k)) + (0,)]


def _direct2(g1, g2):
    """Generators of the direct product of two permutation groups on disjoint point sets."""
    n1, n2 = len(g1[0]), len(g2[0])
    out = [g + tuple(range(n1, n1 + n2)) for g in g1]
    out += [tuple(range(n1)) + tuple(x + n1 for x in g) for g in g2]
    return out


def _prim_root(p):
    fac = [f for f in range(2, p) if (p - 1) % f == 0 and all(f % q for q in range(2, int(f ** 0.5) + 1))]
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fac):
            return g
    return 1


def _proj_gens(p, psl):
    """PSL(2,p) (psl=True) or PGL(2,p) acting on the projective line (p+1 points, p = infinity)."""
    g = _prim_root(p)
    h = g * g % p if psl else g
    mats = [(1, 1, 0, 1), (0, p - 1, 1, 0), (h, 0, 0, 1)]
    out = []
    for a, b, c, d in mats:
        perm = []
        for x in range(p):
            den = (c * x + d) % p
            perm.append(p if den == 0 else (a * x + b) * pow(den, p - 2, p) % p)
        perm.append(p if c % p == 0 else a * pow(c, p - 2, p) % p)
        out.append(tuple(perm))
    return out


def _vec_gens(p, gl):
    """SL(2,p) (gl=False) or GL(2,p) acting on the p^2-1 nonzero vectors of F_p^2."""
    pts = [(x, y) for x in range(p) for y in range(p) if (x, y) != (0, 0)]
    idx = {v: i for i, v in enumerate(pts)}
    mats = [(1, 1, 0, 1), (0, p - 1, 1, 0)]
    if gl:
        mats.append((_prim_root(p), 0, 0, 1))
    return [tuple(idx[((a * x + b * y) % p, (c * x + d * y) % p)] for x, y in pts)
            for a, b, c, d in mats]


def _agl_gens(q):
    """AGL(1,q) acting on the q field elements (q a prime power)."""
    F = lib.GF(q)
    gens = []
    for i in range(F.k):
        t = F.p ** i
        gens.append(tuple(F.add(x, t) for x in range(q)))
    gens.append(tuple(F.mul(F.primitive_element(), x) for x in range(q)))
    return gens


def _catalog():
    A, S, C, X = _alt_gens, _sym_gens, _cyc_gens, _direct2
    return [
        ("A5", A(5)), ("S5", S(5)),
        ("A5xZ2", X(A(5), C(2))), ("A5xZ3", X(A(5), C(3))), ("A5xZ4", X(A(5), C(4))),
        ("SL25", _vec_gens(5, False)), ("SL25xZ2", X(_vec_gens(5, False), C(2))),
        ("S4", S(4)), ("S4xZ2", X(S(4), C(2))), ("S4xZ4", X(S(4), C(4))),
        ("S4xZ8", X(S(4), C(8))), ("S4xS3", X(S(4), S(3))),
        ("A4xZ15", X(A(4), C(15))), ("A4xZ16", X(A(4), C(16))),
        ("GL23", _vec_gens(3, True)), ("SL23xZ8", X(_vec_gens(3, False), C(8))),
        ("PSL27", _proj_gens(7, True)), ("PGL27", _proj_gens(7, False)),
        ("SL27", _vec_gens(7, False)),
        ("AGL8", _agl_gens(8)), ("AGL9", _agl_gens(9)), ("AGL11", _agl_gens(11)),
        ("AGL13", _agl_gens(13)), ("AGL16", _agl_gens(16)), ("AGL17", _agl_gens(17)),
    ]


def _sd_table(m, k, r):
    G, mul, _ = lib.semidirect_group(m, k, r)
    return [[mul(i, j) for j in range(G)] for i in range(G)]


def _candidates(lo, hi, target, rng):
    """(distance to target, name, G, kb, table_maker) for group lifts with lo <= 2 kb |G| <= hi.

    Non-solvable and direct-product catalogue groups come first, then semidirect products.
    Returns the closest few of each kind, interleaved by closeness."""
    cat = []
    for name, gens in _catalog():
        grp = _perm_group(gens, 400)
        if grp is None:
            continue
        elems, index = grp
        G = len(elems)
        for kb in (1, 2, 3, 4):
            val = 2 * kb * G
            if lo <= val <= hi:
                cat.append((abs(val - target), name, G, kb,
                            lambda e=elems, x=index: _perm_table(e, x)))
    sd = []
    for G in range(max(2, lo // 8), hi // 2 + 1):
        kbs = [kb for kb in (1, 2, 3, 4) if lo <= 2 * kb * G <= hi]
        if not kbs:
            continue
        for m in range(1, G + 1):
            if G % m:
                continue
            k = G // m
            if m == 1:
                r = 0
            else:
                rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
                if not rs:
                    continue
                r = rs[rng.randrange(len(rs))]
            for kb in kbs:
                val = 2 * kb * G
                sd.append((abs(val - target), f"Z{m}x|{k}r{r}", G, kb,
                           lambda mm=m, kk=k, rr=r: _sd_table(mm, kk, rr)))
    cat.sort(key=lambda t: t[0])
    sd.sort(key=lambda t: t[0])
    picked = cat[:4] + sd[:4]
    rest = cat[4:] + sd[4:]
    rest.sort(key=lambda t: t[0])
    picked += rest[:max(0, 8 - len(picked))]
    picked.sort(key=lambda t: t[0])
    return picked


# ---------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    def left():
        return 0.93 * time_limit - (time.monotonic() - t0) - 1.0

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

    mb = lib.moore_bound(d, D)
    if best[0] >= mb or d > 32 or left() < 3.0:
        return best

    rng = random.Random(seed * 7919 + d * 131 + D)
    lo = max(best[0] + 1, int(0.35 * mb))
    hi = min(mb, 1024)
    target = 0.55 * mb
    if lo <= hi:
        cands = _candidates(lo, hi, target, rng)
    else:
        cands = []

    # Phase A: group lifts over the candidate groups, each run from the closest first.
    if cands:
        per = 0.7 * left() / len(cands)
        for _, name, G, kb, maker in cands:
            if left() < 3.0:
                break
            if 2 * kb * G <= best[0]:
                continue
            budget = min(per, left() - 2.0)
            if budget < 0.5:
                break
            try:
                table = maker()
                edges = [(i, row[j]) for i, row in enumerate(table) for j in range(G)]
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), 0, kb],
                                 stdin_graph=(G, edges), timeout=budget + 2.5)
                n, es = lib.parse_graph_text(text)
                if n > best[0] and lib.is_valid(n, es, d, D):
                    best = (n, es)
            except (RuntimeError, ValueError, OSError, MemoryError):
                pass

    # Phase B: grow the best graph by pairs of vertices.
    rem = left() - 1.0
    if rem > 1.0 and best[0] >= 2 * d:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed + 1, round(rem, 2), 1, 1],
                             stdin_graph=best, timeout=rem + 2.5)
            n, es = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, es, d, D):
                best = (n, es)
        except (RuntimeError, ValueError, OSError):
            pass

    return best
