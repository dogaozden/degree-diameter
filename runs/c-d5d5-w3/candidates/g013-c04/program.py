"""Cayley-lift search over explicit finite groups, with a grow-by-two repair phase.

Python builds a pool of finite groups as multiplication tables (SL(2,p), A5 and S5 with
cyclic factors, SL(2,3) x Z_k, and sampled semidirect products Z_m x| Z_k). Each table
has identity 0. C runs a voltage-lift search over all of them: a base with kb <= 3 vertices
per side, d darts per base vertex, and voltages in the chosen group. Left multiplication
is an automorphism, so the diameter check needs only 2kb BFS runs. The best lift is then
grown by two vertices per step and repaired by annealing (2-switch and bridge moves).

Fallback: K_{d,d}, or a known construction for D = 3 or 4. Every result is checked with
lib.is_valid before it is returned.
"""
import hashlib
import itertools
import math
import os
import random
import subprocess
import tempfile
import time

import lib

C_SOURCE = r'''
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
#define MAXK 3
#define MAXDART (MAXD * MAXK)
#define MAXGR 64
#define MAXORD 340
#define BIGCOST 1000000000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

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

/* ---------------------------------------------------------- graph basics */

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

/* ---------------------------------------------------------- distance check */

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

/* ---------------------------------------------------------- input / output */

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

/* ---------------------------------------------------------- group tables */

static int NG = 0;
static int GO[MAXGR], GID[MAXGR];
static int *GT[MAXGR];

/* Format: "ng", then per group "order identity" and order*order table entries. */
static int read_groups(void) {
    int ng;
    if (scanf("%d", &ng) != 1 || ng < 0 || ng > MAXGR) return 0;
    for (int gi = 0; gi < ng; gi++) {
        int o, e;
        if (scanf("%d %d", &o, &e) != 2 || o < 1 || o > MAXORD || e < 0 || e >= o) return 0;
        GT[gi] = malloc(sizeof(int) * (size_t)o * (size_t)o);
        if (!GT[gi]) return 0;
        for (long x = 0; x < (long)o * o; x++) {
            int v;
            if (scanf("%d", &v) != 1 || v < 0 || v >= o) return 0;
            GT[gi][x] = v;
        }
        GO[gi] = o;
        GID[gi] = e;
        NG = gi + 1;
    }
    return 1;
}

static int G, GIDN;
static int *M;

/* ---------------------------------------------------------- voltage lifts */

static int KB, ND;
static int DI[MAXDART], DJ[MAXDART], DS[MAXDART];
static int DPERM[MAXDART][MAXN];
static int LADJ[MAXN][MAXD];
static int LDEG[MAXN];
static int VIS[MAXN], VST = 0;
static int QU[MAXN];

static void set_dart(int t) {
    for (int g = 0; g < G; g++) DPERM[t][g] = M[g * G + DS[t]];
}

static int has_dup(void) {
    for (int t1 = 0; t1 < ND; t1++)
        for (int t2 = t1 + 1; t2 < ND; t2++)
            if (DI[t1] == DI[t2] && DJ[t1] == DJ[t2] && DS[t1] == DS[t2]) return 1;
    return 0;
}

static void build_ladj(void) {
    int N = 2 * KB * G;
    for (int v = 0; v < N; v++) LDEG[v] = 0;
    for (int t = 0; t < ND; t++)
        for (int g = 0; g < G; g++) {
            int a = DI[t] * G + g;
            int b = (KB + DJ[t]) * G + DPERM[t][g];
            LADJ[a][LDEG[a]++] = b;
            LADJ[b][LDEG[b]++] = a;
        }
}

/* Unreached (representative, vertex) pairs over the 2KB class representatives. */
static long orbit_cost(void) {
    if (has_dup()) return BIGCOST;
    build_ladj();
    int N = 2 * KB * G;
    long total = 0;
    for (int rep = 0; rep < 2 * KB; rep++) {
        int src = rep * G + GIDN;
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
    int N = 2 * KB * G;
    g->n = N;
    for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = v >= KB * G; }
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < G; x++)
            add_edge(g, DI[t] * G + x, (KB + DJ[t]) * G + DPERM[t][x]);
}

static int lift_climb(int kb, int gi, long steps, Graph *out) {
    KB = kb;
    ND = d * kb;
    G = GO[gi];
    M = GT[gi];
    GIDN = GID[gi];
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
            set_dart(t);
        }
    }
    long cost = orbit_cost();
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 31) == 0 && now() > t_end) return 0;
        double T = 2.0 * (1.0 - (double)s / (double)steps) + 0.05;
        if (rnd01() < 0.7) {
            int t = rndint(ND);
            int old = DS[t];
            int nv = rndint(G);
            if (nv == old) continue;
            DS[t] = nv;
            set_dart(t);
            long c2 = orbit_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else { DS[t] = old; set_dart(t); }
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
    static int cg[MAXGR * MAXK], ck[MAXGR * MAXK];
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        int nc = 0, bestpick = -1;
        long bestn = -1;
        for (int gi = 0; gi < NG; gi++)
            for (int kb = 1; kb <= MAXK; kb++) {
                long nn = 2L * kb * GO[gi];
                if (nn <= best->n || nn > moore || nn > MAXN) continue;
                cg[nc] = gi;
                ck[nc] = kb;
                if (nn > bestn) { bestn = nn; bestpick = nc; }
                nc++;
            }
        if (nc == 0) return;
        int pick = (fails > 30 && rnd01() < 0.5) ? bestpick : rndint(nc);
        long steps = 3000 + rndint(9000) + (long)(fails / 20) * 4000;
        if (steps > 60000) steps = 60000;
        int before = best->n;
        if (lift_climb(ck[pick], cg[pick], steps, &LCAND) &&
            LCAND.n > best->n && is_valid(&LCAND))
            copy_graph(best, &LCAND);
        fails = best->n > before ? 0 : fails + 1;
    }
}

/* ---------------------------------------------------------- grow by two */

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

/* ---------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < input\n", argv[0]);
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

    read_groups();
    static Graph best, start;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    copy_graph(&start, &best);

    if (best.n < moore_bound()) {
        lift_search(&best, t0 + (t_end - t0) * 0.75);
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
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    if D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q) and q + 1 <= d:
                return _gq_w(q)
    return None


# ---------------------------------------------------------- finite groups as tables
# A group is (order, flat) where flat[x*order + y] = index of x*y, and the identity is index 0.

def _table(elems, index, mul):
    flat = []
    for x in elems:
        for y in elems:
            flat.append(index[mul(x, y)])
    return len(elems), flat


def _closure_group(identity, gens, mul):
    elems = [identity]
    index = {identity: 0}
    stack = [identity]
    while stack:
        x = stack.pop()
        for g in gens:
            y = mul(x, g)
            if y not in index:
                index[y] = len(elems)
                elems.append(y)
                stack.append(y)
    return _table(elems, index, mul)


def _sl2_group(p):
    def mul(x, y):
        a, b, c, d = x
        e, f, g, h = y
        return ((a * e + b * g) % p, (a * f + b * h) % p,
                (c * e + d * g) % p, (c * f + d * h) % p)
    gens = [(0, p - 1, 1, 0), (1, 1, 0, 1)]
    return _closure_group((1, 0, 0, 1), gens, mul)


def _perm_group(gens, n):
    def mul(x, y):
        return tuple(x[y[i]] for i in range(n))
    return _closure_group(tuple(range(n)), gens, mul)


def _cyclic_group(k):
    return k, [(i + j) % k for i in range(k) for j in range(k)]


def _product_group(A, B):
    na, ta = A
    nb, tb = B
    n = na * nb
    flat = [0] * (n * n)
    for x1 in range(na):
        for x2 in range(nb):
            row = (x1 * nb + x2) * n
            base_b = x2 * nb
            for y1 in range(na):
                z1 = ta[x1 * na + y1] * nb
                col = row + y1 * nb
                for y2 in range(nb):
                    flat[col + y2] = z1 + tb[base_b + y2]
    return n, flat


def _semidirect_group(m, k, r):
    order, mul, _inv = lib.semidirect_group(m, k, r)
    return _table(list(range(order)), {i: i for i in range(order)}, mul)


def _group_pool(seed):
    rng = random.Random(seed)
    specs = [_sl2_group(7), _sl2_group(5), _product_group(_sl2_group(5), _cyclic_group(2))]
    a5 = _perm_group([(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)], 5)
    s5 = _perm_group([(1, 0, 2, 3, 4), (1, 2, 3, 4, 0)], 5)
    specs += [a5, s5, _product_group(s5, _cyclic_group(2))]
    for k in (3, 4, 5):
        specs.append(_product_group(a5, _cyclic_group(k)))
    sl23 = _sl2_group(3)
    for k in (5, 7, 10, 13):
        specs.append(_product_group(sl23, _cyclic_group(k)))
    cands = []
    for m in range(3, 171):
        for k in range(2, 340 // m + 1):
            n = m * k
            if n < 60 or n > 340:
                continue
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    cands.append((m, k, r))
    for m, k, r in rng.sample(cands, min(8, len(cands))):
        specs.append(_semidirect_group(m, k, r))
    return [g for g in specs if 2 <= g[0] <= 340]


def _groups_text(groups):
    parts = [f"{len(groups)}\n"]
    for n, flat in groups:
        parts.append(f"{n} 0\n")
        parts.append(" ".join(map(str, flat)) + "\n")
    return "".join(parts)


# ---------------------------------------------------------- compile and run

def _exe_for(source):
    cache = os.path.join(tempfile.gettempdir(), "evolve-c-cache")
    os.makedirs(cache, exist_ok=True)
    exe = os.path.join(cache, "grp-" + hashlib.sha256(source.encode()).hexdigest()[:20])
    if not os.path.exists(exe):
        src = f"{exe}.{os.getpid()}.c"
        tmp = f"{exe}.{os.getpid()}.tmp"
        with open(src, "w") as f:
            f.write(source)
        cc = os.environ.get("CC", "cc")
        r = subprocess.run([cc, "-O2", "-std=c11", "-o", tmp, src, "-lm"],
                           capture_output=True, text=True, timeout=120)
        os.remove(src)
        if r.returncode != 0:
            raise RuntimeError("C compile failed:\n" + r.stderr[-2000:])
        os.replace(tmp, exe)
    return exe


def _run_c(source, args, stdin_text, timeout):
    exe = _exe_for(source)
    try:
        r = subprocess.run([exe, *map(str, args)], input=stdin_text, capture_output=True,
                           text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        raise RuntimeError("C program timed out") from None
    if r.returncode != 0:
        raise RuntimeError(f"C program exited with code {r.returncode}:\n" + r.stderr[-2000:])
    return r.stdout


# ---------------------------------------------------------- entry point

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

    try:
        text = _groups_text(_group_pool(seed)) + lib.graph_to_text(*best)
    except Exception:
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 3.0
    if budget < 1.0:
        return best
    try:
        out = _run_c(C_SOURCE, [d, D, seed, round(budget, 2)], text, timeout=budget + 5)
        n, edges = lib.parse_graph_text(out)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except Exception:
        pass
    return best
