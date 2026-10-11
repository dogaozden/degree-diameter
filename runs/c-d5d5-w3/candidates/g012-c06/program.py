"""Group-pool lift search in C, then grow-by-two annealing, in rounds.

Python builds a pool of finite groups (named nonabelian groups such as S5, A5, SL(2,5), PSL(2,7),
SL(2,7), PGL(2,7), direct products with cyclic groups, semidirect products, and cyclic groups) as
multiplication tables. The tables are embedded in the C source, so the C engine can lift over any
of them. A lift over a group G with base kb vertices per side uses d darts per base vertex: dart
(i, j, s) joins A_{i,x} to B_{j,x*s}. Left multiplication is an automorphism, so the diameter is
checked by BFS from the 2*kb block representatives.

Known constructions (K_{d,d}, the projective-plane Moore graph for D = 3, Araujo-Lopez for D = 3,
generalized quadrangles for D = 4) are the starting points. Every candidate is checked with
lib.is_valid, and the best valid graph is always returned.
"""
import itertools
import math
import random
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core with an embedded group pool.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0".
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1: lift search. For a group index gi (table GTAB[gi], order GORD_[gi], identity GIDN[gi])
 *   and kb in 1..3, the lift has 2*kb*|G| vertices. Voltages and layer permutations are
 *   annealed to minimise unreached pairs from the 2*kb representatives.
 * Phase 2: grow by two with bridge and 2-switch annealing.
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
#define MAXG 512
#define BIGCOST 1000000000L

/*@GROUPS@*/

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end, phase_end;

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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ group pool */

static int GORD, GID;
static const unsigned short *GTP;
static int DPERM[MAXDART][MAXG];

static void set_group(int gi) {
    GORD = GORD_[gi];
    GID = GIDN[gi];
    GTP = GTAB[gi];
}

static int gmul(int x, int y) { return (int)GTP[x * GORD + y]; }

/* ------------------------------------------------------------ voltage lifts */

static int KB, ND;
static int DI[MAXDART], DJ[MAXDART], DS[MAXDART];
static int LADJ[MAXN][MAXD];
static int LDEG[MAXN];
static int VIS[MAXN], VST = 0;
static int QU[MAXN];
static int PG[NGRP * MAXK], PK[NGRP * MAXK];

static void set_dart_perm(int t) {
    for (int g = 0; g < GORD; g++) DPERM[t][g] = gmul(g, DS[t]);
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

/* Unreached (representative, vertex) pairs over the 2KB block representatives. */
static long orbit_cost(void) {
    if (has_dup()) return BIGCOST;
    build_ladj();
    int N = 2 * KB * GORD;
    long total = 0;
    for (int rep = 0; rep < 2 * KB; rep++) {
        int src = rep * GORD + GID;
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

/* One annealing run for group gi and kb blocks per side. On success, out holds the lift. */
static int lift_climb(int kb, int gi, long steps, Graph *out) {
    KB = kb;
    ND = d * kb;
    set_group(gi);
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
        if ((s & 31) == 0 && now() > phase_end) return 0;
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

/* Fill PG/PK with (group, kb) pairs whose lift order exceeds n. Returns the count. */
static int feasible_pairs(int n, long moore) {
    int np = 0;
    for (int gi = 0; gi < NGRP; gi++)
        for (int kb = 1; kb <= MAXK; kb++) {
            long N = 2L * kb * GORD_[gi];
            if (N > n && N <= moore && N <= MAXN) { PG[np] = gi; PK[np] = kb; np++; }
        }
    return np;
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    phase_end = until;
    int np = feasible_pairs(best->n, moore);
    int fails = 0;
    while (np > 0 && now() < until) {
        int c = rndint(np);
        long extra = (long)(fails / 20) * 4000;
        if (extra > 60000) extra = 60000;
        long steps = 3000 + rndint(9000) + extra;
        int before = best->n;
        if (lift_climb(PK[c], PG[c], steps, &cand) && cand.n > best->n && is_valid(&cand))
            copy_graph(best, &cand);
        if (best->n > before) {
            fails = 0;
            np = feasible_pairs(best->n, moore);
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
        if (rnd01() < 0.5) {
            /* Bridge move: add v-w across a bad pair, removing (v,a) and (w,b). */
            int w = rndint(work->n);
            if (w == v || work->side[w] == work->side[v] || has_edge(work, v, w)) continue;
            if (work->deg[w] == 0) continue;
            int a = work->adj[v][rndint(work->deg[v])];
            int b = work->adj[w][rndint(work->deg[w])];
            if (a == w || b == v || has_edge(work, a, b)) continue;
            del_edge(work, v, a);
            del_edge(work, w, b);
            add_edge(work, v, w);
            add_edge(work, a, b);
            long nb = bad_pairs(work);
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
                bad = nb;
            } else {
                del_edge(work, v, w);
                del_edge(work, a, b);
                add_edge(work, v, a);
                add_edge(work, w, b);
            }
        } else {
            /* Random degree-preserving 2-switch. */
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
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
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

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (d == 1 || D < 2) { printf("2 1\n0 1\n"); return 0; }

    static Graph best, start;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    copy_graph(&start, &best);

    if (best.n < moore_bound()) {
        lift_search(&best, t0 + (t_end - t0) * 0.7);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) copy_graph(&best, &start);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ------------------------------------------------------------ group tables

def _group(order, T, name):
    """Finish a group from its flat table T (T[x*order+y] = x*y): find the identity index."""
    ident = None
    for e in range(order):
        if all(T[e * order + x] == x for x in range(order)):
            ident = e
            break
    if ident is None:
        raise ValueError("table is not a group")
    return {"order": order, "T": T, "e": ident, "name": name}


def _from_op(order, op, name):
    """Group from an operation on 0..order-1."""
    T = [op(x, y) for x in range(order) for y in range(order)]
    return _group(order, T, name)


def _from_closure(gens, mul, ident, name, limit):
    """Group generated by gens under mul; None if it exceeds limit elements."""
    elems = [ident]
    index = {ident: 0}
    frontier = [ident]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = mul(x, g)
                if y not in index:
                    if len(elems) >= limit:
                        return None
                    index[y] = len(elems)
                    elems.append(y)
                    nxt.append(y)
        frontier = nxt
    T = [index[mul(a, b)] for a in elems for b in elems]
    return _group(len(elems), T, name)


def _pmul(p, q):
    """Composition of permutations given as tuples."""
    return tuple(p[i] for i in q)


def _mat_mul(p, canon):
    """Product of 2x2 matrices mod p (tuples a,b,c,d), followed by canon."""
    def mul(x, y):
        a, b, c, d = x
        e, f, g, h = y
        return canon(((a * e + b * g) % p, (a * f + b * h) % p,
                      (c * e + d * g) % p, (c * f + d * h) % p))
    return mul


def _pgl_canon(p):
    """Normalise a matrix up to scalars: first nonzero entry becomes 1."""
    def canon(M):
        v = next(x for x in M if x)
        inv = pow(v, p - 2, p)
        return tuple((x * inv) % p for x in M)
    return canon


def _psl_canon(p):
    """Normalise a matrix up to sign."""
    def canon(M):
        return min(M, tuple((p - x) % p for x in M))
    return canon


def _cyclic(k):
    return _from_op(k, lambda x, y: (x + y) % k, f"Z{k}")


def _semidirect(m, k, r):
    order, mul, _ = lib.semidirect_group(m, k, r)
    return _from_op(order, mul, f"Z{m}x|Z{k}r{r}")


def _product(A, B):
    """Direct product of two group dicts; element x = a*|B| + b."""
    G1, G2 = A["order"], B["order"]
    TA, TB = A["T"], B["T"]

    def op(x, y):
        a1, b1 = divmod(x, G2)
        a2, b2 = divmod(y, G2)
        return TA[a1 * G1 + a2] * G2 + TB[b1 * G2 + b2]

    return _from_op(G1 * G2, op, f"{A['name']}x{B['name']}")


def _named_groups(limit):
    """Named nonabelian groups (and a few cyclic-free classics) with order <= limit."""
    out = []

    def add(g):
        if g is not None:
            out.append(g)

    def perm(gens, n, name):
        return _from_closure(gens, _pmul, tuple(range(n)), name, limit)

    add(perm([(1, 0, 2), (1, 2, 0)], 3, "S3"))
    add(perm([(1, 2, 0, 3), (1, 0, 3, 2)], 4, "A4"))
    add(perm([(1, 0, 2, 3), (1, 2, 3, 0)], 4, "S4"))
    add(perm([(1, 2, 0, 3, 4), (0, 1, 3, 4, 2)], 5, "A5"))
    add(perm([(1, 0, 2, 3, 4), (1, 2, 3, 4, 0)], 5, "S5"))

    p = 5
    add(_from_closure([(1, 1, 0, 1), (0, p - 1, 1, 0)], _mat_mul(p, lambda M: M),
                      (1, 0, 0, 1), "SL25", limit))

    p = 7
    ident_sl = (1, 0, 0, 1)
    add(_from_closure([(1, 1, 0, 1), (0, p - 1, 1, 0)], _mat_mul(p, lambda M: M),
                      ident_sl, "SL27", limit))
    cpsl = _psl_canon(p)
    add(_from_closure([cpsl((1, 1, 0, 1)), cpsl((0, p - 1, 1, 0))],
                      _mat_mul(p, cpsl), cpsl(ident_sl), "PSL27", limit))
    cpgl = _pgl_canon(p)
    add(_from_closure([cpgl((1, 1, 0, 1)), cpgl((0, p - 1, 1, 0)), cpgl((3, 0, 0, 1))],
                      _mat_mul(p, cpgl), cpgl(ident_sl), "PGL27", limit))
    return out


def _select_pool(lo, hi, seed, entry_budget=220000, max_groups=14):
    """Groups with orders in [lo, hi], chosen by priority, total table size capped."""
    rng = random.Random(seed)
    allnamed = _named_groups(hi)
    specs = []
    for g in allnamed:
        if lo <= g["order"] <= hi:
            specs.append((g["order"], (lambda g=g: g)))

    prods = []
    for base in allnamed:
        G1 = base["order"]
        if G1 < 2 or G1 > hi // 2:
            continue
        ks = [k for k in range(2, hi // G1 + 1) if lo <= G1 * k <= hi]
        rng.shuffle(ks)
        for k in ks[:2]:
            prods.append((G1 * k, (lambda A=base, k=k: _product(A, _cyclic(k)))))
    rng.shuffle(prods)

    semis = []
    seen = set()
    for _ in range(80):
        if hi < lo:
            break
        G = rng.randint(lo, hi)
        divs = [m for m in range(3, G) if G % m == 0 and G // m >= 2]
        if not divs:
            continue
        m = rng.choice(divs)
        k = G // m
        r = None
        for _t in range(40):
            cand = rng.randrange(1, m)
            if math.gcd(cand, m) == 1 and pow(cand, k, m) == 1 % m:
                r = cand
                break
        if r is None or (m, k, r) in seen:
            continue
        seen.add((m, k, r))
        semis.append((G, (lambda m=m, k=k, r=r: _semidirect(m, k, r))))

    G0 = rng.randint(max(lo, 2), max(lo, hi))
    cyc = [(G0, (lambda G0=G0: _cyclic(G0)))] if G0 <= hi else []

    chosen = []
    used = 0
    for order, thunk in specs + prods + semis + cyc:
        if len(chosen) >= max_groups:
            break
        if used + order * order > entry_budget:
            continue
        try:
            g = thunk()
        except (ValueError, RuntimeError):
            continue
        chosen.append(g)
        used += g["order"] * g["order"]
    if not chosen:
        chosen.append(_from_op(1, lambda x, y: 0, "trivial"))
    return chosen


def _emit_groups(groups):
    """C definitions for the group pool: NGRP, GORD_, GIDN, and one table per group."""
    lines = [f"#define NGRP {len(groups)}"]
    lines.append("static const int GORD_[NGRP] = {"
                 + ", ".join(str(g["order"]) for g in groups) + "};")
    lines.append("static const int GIDN[NGRP] = {"
                 + ", ".join(str(g["e"]) for g in groups) + "};")
    for i, g in enumerate(groups):
        vals = ",".join(map(str, g["T"]))
        lines.append(f"static const unsigned short GT{i}[] = {{{vals}}};")
    lines.append("static const unsigned short *const GTAB[NGRP] = {"
                 + ", ".join(f"GT{i}" for i in range(len(groups))) + "};")
    return "\n".join(lines) + "\n"


# ------------------------------------------------------------ constructions

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


# ------------------------------------------------------------ entry point

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

    deadline = t0 + 0.90 * time_limit - 1.0
    hi = min(moore // 2, 340)
    for rnd_i in range(3):
        remaining = deadline - time.monotonic()
        if remaining < 8.0:
            break
        lo = max(3, best[0] // 6 + 1)
        if lo > hi:
            break
        share = remaining if rnd_i == 2 else remaining * 0.5
        budget = share - 3.0
        if budget < 3.0:
            break
        try:
            pool = _select_pool(lo, hi, seed * 1009 + rnd_i)
            src = C_SOURCE.replace("/*@GROUPS@*/", _emit_groups(pool))
            text = lib.run_c(src, [d, D, seed + rnd_i, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 10)
            n, edges = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except (RuntimeError, ValueError, OSError, IndexError, ZeroDivisionError):
            pass
    return best
