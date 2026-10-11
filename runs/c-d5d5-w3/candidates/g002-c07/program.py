"""Bold variant: lifts over many small and non-abelian groups, searched in C, then grow-by-two.

Main change from the parent: the C engine no longer draws its own semidirect groups. Python
supplies a full multiplication table for each candidate group (symmetric and alternating groups,
PSL(2,7), PGL(2,7), direct products with cyclic groups, and random semidirect products). C then
searches for a bi-Cayley lift with kb base vertices per side, with d darts per base vertex.
Left multiplication is an automorphism, so the diameter is checked by 2*kb BFS runs.

Candidates are ordered by vertex count and probed with a binary search: each probe is a short
C anneal that returns immediately on success. The last part of the budget goes to a grow-by-two
search (C mode 1) on the best graph. Every returned graph is checked with lib.is_valid, and
K_{d,d} or the known construction is kept as the fallback.
"""
import itertools
import math
import random
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core, group-lift version.
 *
 * Usage: prog d D seed time_limit mode kb
 *   mode 0: stdin = group table. Line "N M" (M = N*N) then M lines "u v" with
 *           u = a*N+b and v = a*b (group multiplication). Searches a bi-Cayley lift with
 *           kb base vertices per side and d darts per base vertex. Returns on first success,
 *           otherwise prints K_{d,d}.
 *   mode 1: stdin = a valid graph "n m" + edges. Grows it by two vertices at a time.
 * stdout: "n m" then m lines "u v".
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
#define MAXG 512
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

/* ------------------------------------------------------------ group */

static int G;
static int MUL[MAXG][MAXG];

static int read_group(void) {
    int N = 0, M = 0;
    if (scanf("%d %d", &N, &M) != 2) return 0;
    if (N < 1 || N > MAXG || M != N * N) return 0;
    for (int i = 0; i < M; i++) {
        long u, v;
        if (scanf("%ld %ld", &u, &v) != 2) return 0;
        if (u < 0 || u >= (long)N * N || v < 0 || v >= N) return 0;
        MUL[u / N][u % N] = (int)v;
    }
    G = N;
    return 1;
}

/* ------------------------------------------------------------ bi-Cayley lifts */

static int KB, ND;
static int DI[MAXDART], DJ[MAXDART], DS[MAXDART];
static int DPERM[MAXDART][MAXG];   /* DPERM[t][x] = x * DS[t] */
static int LADJ[MAXN][MAXD];
static int LDEG[MAXN];
static int VIS[MAXN], VST = 0;
static int QU[MAXN];

static void set_dart(int t) {
    for (int x = 0; x < G; x++) DPERM[t][x] = MUL[x][DS[t]];
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
        for (int x = 0; x < G; x++) {
            int a = DI[t] * G + x;
            int b = (KB + DJ[t]) * G + DPERM[t][x];
            LADJ[a][LDEG[a]++] = b;
            LADJ[b][LDEG[b]++] = a;
        }
}

/* Unreached (representative, vertex) pairs over the 2KB base-vertex representatives. */
static long orbit_cost(void) {
    if (has_dup()) return BIGCOST;
    build_ladj();
    int N = 2 * KB * G;
    long total = 0;
    for (int rep = 0; rep < 2 * KB; rep++) {
        int src = rep * G;
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

/* One annealing run over voltages and layer swaps. On success, out holds the full lift. */
static int lift_try(int kb, long steps, double deadline, Graph *out) {
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
            DS[t] = rndint(G);
            set_dart(t);
        }
    }
    long cost = orbit_cost();
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 31) == 0 && now() > deadline) return 0;
        double T = 2.5 * (1.0 - (double)s / (double)steps) + 0.05;
        int swap = (kb >= 2) && rnd01() < 0.3;
        if (!swap) {
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

static int lift_search(int kb, Graph *out, double until) {
    int tries = 0;
    while (now() < until) {
        tries++;
        long steps = 6000 + (long)(tries % 4) * 6000;
        if (lift_try(kb, steps, until, out)) return 1;
    }
    return 0;
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
    if (argc < 7) {
        fprintf(stderr, "usage: %s d D seed time_limit mode kb\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int mode = atoi(argv[5]);
    int kb = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.94;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (d == 1 || D < 2) { printf("2 1\n0 1\n"); return 0; }

    static Graph best, found;
    if (mode == 1) {
        read_start(&best);
        if (best.n == 0) complete_bipartite(&best);
        grow_search(&best, t_end);
    } else {
        complete_bipartite(&best);
        if (read_group() && kb >= 1 && kb <= MAXK && 2 * kb * G <= MAXN &&
            2L * kb * G <= moore_bound()) {
            if (lift_search(kb, &found, t_end) && found.n > best.n && is_valid(&found))
                copy_graph(&best, &found);
        }
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''

_PER_TRY = 4.0      # seconds per lift probe (a failed probe uses all of it)
_MAX_G = 512        # group order cap in the C engine


# ------------------------------------------------------------ group tables

def _perm_table(gens, npts, limit=400):
    """Multiplication table of the permutation group generated by gens (identity is index 0)."""
    ident = tuple(range(npts))
    elems = [ident]
    index = {ident: 0}
    frontier = [ident]
    while frontier:
        nxt = []
        for e in frontier:
            for s in gens:
                f = tuple(e[i] for i in s)
                if f not in index:
                    if len(elems) >= limit:
                        return None
                    index[f] = len(elems)
                    elems.append(f)
                    nxt.append(f)
        frontier = nxt
    tab = [[index[tuple(ea[i] for i in eb)] for eb in elems] for ea in elems]
    return len(elems), tab


def _sym(n):
    gens = [tuple([1, 0] + list(range(2, n))), tuple((i + 1) % n for i in range(n))]
    return _perm_table(gens, n)


def _alt(n):
    cyc3 = tuple([1, 2, 0] + list(range(3, n)))
    if n == 4:
        gens = [cyc3, (1, 0, 3, 2)]
    else:
        gens = [cyc3, tuple((i + 1) % n for i in range(n))]
    return _perm_table(gens, n)


def _primitive_root(p):
    for g in range(2, p):
        x, order = g, 1
        while x != 1:
            x = x * g % p
            order += 1
        if order == p - 1:
            return g
    return 1


def _pgl2(p, psl):
    """PGL(2,p) (or PSL(2,p) when psl) acting on the p+1 points of the projective line (p = infinity)."""
    g = _primitive_root(p)
    if psl:
        g = g * g % p
    translate = tuple([(x + 1) % p for x in range(p)] + [p])
    scale = tuple([(g * x) % p for x in range(p)] + [p])
    invert = [p] + [(-pow(x, p - 2, p)) % p for x in range(1, p)] + [0]
    return _perm_table([translate, scale, tuple(invert)], p + 1)


def _cyc(k):
    return k, [[(a + b) % k for b in range(k)] for a in range(k)]


def _direct(A, B):
    n1, t1 = A
    n2, t2 = B
    N = n1 * n2
    tab = [[0] * N for _ in range(N)]
    for a1 in range(n1):
        for a2 in range(n2):
            row = tab[a1 * n2 + a2]
            for b1 in range(n1):
                r = t1[a1][b1] * n2
                for b2 in range(n2):
                    row[b1 * n2 + b2] = r + t2[a2][b2]
    return N, tab


def _semi_options(G):
    """All (m, k, r) with G = m*k, m >= 2, k >= 2, Z_m x|_r Z_k valid."""
    opts = []
    for m in range(2, G + 1):
        if G % m or G // m < 2:
            continue
        k = G // m
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


def _semi_table(m, k, r):
    N, mul, _ = lib.semidirect_group(m, k, r)
    return N, [[mul(a, b) for b in range(N)] for a in range(N)]


def _candidates(lo, hi, rng):
    """Sorted list of (vertices, label, kb, builder) with lo < vertices <= hi.

    vertices = 2 * kb * |G|. builder() returns (|G|, table) or None.
    """
    floor_g = max(2, lo // 6)
    cap = min(hi // 2, _MAX_G)
    if cap < floor_g:
        return []

    named = [
        (6, "S3", lambda: _sym(3)),
        (12, "A4", lambda: _alt(4)),
        (24, "S4", lambda: _sym(4)),
        (36, "S3xS3", lambda: _direct(_sym(3), _sym(3))),
        (60, "A5", lambda: _alt(5)),
        (120, "S5", lambda: _sym(5)),
        (144, "S4xS3", lambda: _direct(_sym(4), _sym(3))),
        (144, "A4xA4", lambda: _direct(_alt(4), _alt(4))),
        (168, "PSL27", lambda: _pgl2(7, True)),
        (288, "S4xA4", lambda: _direct(_sym(4), _alt(4))),
        (336, "PGL27", lambda: _pgl2(7, False)),
    ]
    bases = [
        (12, "A4", lambda: _alt(4)),
        (24, "S4", lambda: _sym(4)),
        (60, "A5", lambda: _alt(5)),
        (120, "S5", lambda: _sym(5)),
        (168, "PSL27", lambda: _pgl2(7, True)),
    ]
    for order, label, b in bases:
        for k in range(2, 30):
            named.append((order * k, f"{label}xZ{k}",
                          lambda b=b, k=k: _direct(b(), _cyc(k))))

    out = []
    for order, label, builder in named:
        for kb in (1, 2, 3):
            nv = 2 * kb * order
            if lo < nv <= hi and order <= _MAX_G:
                out.append((nv, label, kb, builder))

    for G in range(floor_g, cap + 1):
        opts = _semi_options(G)
        if opts:
            m, k, r = rng.choice(opts)
            builder = (lambda m=m, k=k, r=r: _semi_table(m, k, r))
            label = f"semi{m}x{k}r{r}"
        else:
            builder = (lambda G=G: _cyc(G))
            label = f"cyc{G}"
        for kb in (1, 2, 3):
            nv = 2 * kb * G
            if lo < nv <= hi:
                out.append((nv, label, kb, builder))

    out.sort(key=lambda c: c[0])
    return out


# ------------------------------------------------------------ C calls

def _lift_call(d, D, seed, budget, N, tab, kb):
    pairs = [(a * N + b, tab[a][b]) for a in range(N) for b in range(N)]
    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), 0, kb],
                     stdin_graph=(N, pairs), timeout=budget + 2.5)
    return lib.parse_graph_text(text)


def _grow_call(d, D, seed, budget, graph):
    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), 1, 0],
                     stdin_graph=graph, timeout=budget + 2.5)
    return lib.parse_graph_text(text)


# ------------------------------------------------------------ known constructions

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


# ------------------------------------------------------------ build

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))              # K_{d,d}: valid for D >= 2
    try:
        start = known_start(d, D)
    except (ValueError, RuntimeError):
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    ladder_end = t0 + 0.78 * time_limit - 1.0
    final_end = t0 + 0.92 * time_limit - 2.0
    if final_end - time.monotonic() < 1.5:
        return best

    rng = random.Random(seed * 7919 + d * 131 + D)
    try:
        cands = _candidates(best[0], min(moore, 4000), rng)
    except Exception:  # candidate generation must never break the case
        cands = []

    # Binary search for the largest candidate order the group-lift engine can hit.
    lo_i, hi_i = 0, len(cands) - 1
    while lo_i <= hi_i:
        remaining = ladder_end - time.monotonic()
        if remaining < 1.0:
            break
        mid = (lo_i + hi_i) // 2
        nv, _label, kb, builder = cands[mid]
        if nv <= best[0]:
            lo_i = mid + 1
            continue
        ok = False
        try:
            built = builder()
            if built is not None:
                N, tab = built
                if 2 * kb * N == nv:
                    n, edges = _lift_call(d, D, seed, min(_PER_TRY, remaining), N, tab, kb)
                    if n > best[0] and lib.is_valid(n, edges, d, D):
                        best = (n, edges)
                        ok = True
        except (RuntimeError, ValueError, OSError):
            ok = False
        if ok:
            lo_i = mid + 1
        else:
            hi_i = mid - 1

    # Grow the best graph by two vertices for the remaining time.
    remaining = final_end - time.monotonic()
    if remaining > 1.5:
        try:
            n, edges = _grow_call(d, D, seed, remaining - 1.0, best)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except (RuntimeError, ValueError, OSError):
            pass
    return best
