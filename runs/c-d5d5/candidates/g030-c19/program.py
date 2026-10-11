"""Non-metacyclic group lift search: bi-Cayley and orbit lifts over tabulated groups, then grow-by-two.

Python builds a pool of finite groups as multiplication tables (direct products of small
nonabelian groups such as A4, S4, SL(2,3), A5, Heisenberg, and cyclic groups). The pool is
packed into the stdin stream, and the C engine searches voltage lifts over these groups.
Left multiplication is an automorphism, so the diameter is checked by BFS from 2*kb class
representatives. Successful lifts are grown by two and repaired by annealing.

Valid fallbacks are kept throughout: K_{d,d}, known constructions for D = 3 and 4, and every
C output is re-checked in Python with lib.is_valid before it is returned.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Orbit-lift search over tabulated finite groups, then grow-by-two annealing.
 *
 * Usage:   prog d D seed time_limit   < stream
 * stdin:   "0 M" header, then 2M integers forming the stream:
 *            P                       number of group entries
 *            per entry: g < 0 means cyclic group of order -g (table built here);
 *                       g >= 2 means a group of order g, followed by g*g table entries
 *                       (mul[x*g+y], identity = 0)
 *            sn sm                    start graph order and edge count
 *            sm pairs u v            start graph edges (may be 0 0 if none)
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Lift: kb base vertices per side, d darts out of each base vertex. Dart (i, j, s) joins
 * A_{i,g} to B_{j,g*s}. Left multiplication is an automorphism, so a BFS of depth D from
 * each of the 2kb class representatives decides the diameter.
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
#define MAXK 4
#define MAXDART (MAXD * MAXK)
#define MAXG 400
#define MAXP 1024
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

static int *BUF = NULL;
static long BLEN = 0;

static void read_input(void) {
    long n0, m0;
    BLEN = 0;
    if (scanf("%ld %ld", &n0, &m0) != 2 || m0 < 0 || m0 > 20000000L) return;
    long want = 2 * m0;
    BUF = malloc(sizeof(int) * (size_t)(want + 1));
    if (!BUF) return;
    long k = 0;
    for (; k < want; k++)
        if (scanf("%d", &BUF[k]) != 1) break;
    BLEN = k;
}

/* Group pool. */
static int NGR = 0;
static int GORD[MAXP];
static int GCYC[MAXP];
static int *GTAB[MAXP];
static int SCR[MAXG * MAXG];
static int G;      /* current group order */
static int *MT;    /* current multiplication table, identity = 0 */

/* Parse the group pool from BUF; returns the stream position after it. */
static long parse_groups(void) {
    long p = 0;
    if (BLEN < 1) return 0;
    long np = BUF[p++];
    for (long i = 0; i < np && p < BLEN; i++) {
        long g = BUF[p++];
        if (g < 0) {
            g = -g;
            if (g < 2 || g > MAXG || NGR >= MAXP) continue;
            GORD[NGR] = (int)g;
            GCYC[NGR] = 1;
            GTAB[NGR] = NULL;
            NGR++;
        } else {
            if (g < 2 || g > MAXG || p + g * g > BLEN) break;
            if (NGR >= MAXP) { p += g * g; continue; }
            int *t = malloc(sizeof(int) * (size_t)(g * g));
            if (!t) break;
            memcpy(t, BUF + p, sizeof(int) * (size_t)(g * g));
            p += g * g;
            int ok = 1;
            for (long y = 0; y < g && ok; y++)
                if (t[y] != y || t[y * g] != y) ok = 0;
            if (!ok) { free(t); continue; }
            GORD[NGR] = (int)g;
            GCYC[NGR] = 0;
            GTAB[NGR] = t;
            NGR++;
        }
    }
    return p;
}

static void select_group(int gi) {
    G = GORD[gi];
    if (GCYC[gi]) {
        for (int x = 0; x < G; x++)
            for (int y = 0; y < G; y++)
                SCR[x * G + y] = (x + y) % G;
        MT = SCR;
    } else {
        MT = GTAB[gi];
    }
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

static void read_start(Graph *g, long p) {
    g->n = 0;
    if (p + 2 > BLEN) return;
    long sn = BUF[p], sm = BUF[p + 1];
    p += 2;
    if (sn <= 0 || sn > MAXN || sm < 0 || p + 2 * sm > BLEN) return;
    g->n = (int)sn;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (long e = 0; e < sm; e++) {
        int u = BUF[p + 2 * e], v = BUF[p + 2 * e + 1];
        if (u < 0 || v < 0 || u >= g->n || v >= g->n || u == v ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    static int queue[MAXN];
    for (int s = 0; s < g->n; s++) {
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

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ orbit lifts */

static int KB, ND;
static int DI[MAXDART], DJ[MAXDART], DS[MAXDART];
static int DPERM[MAXDART][MAXG];   /* DPERM[t][g] = g * DS[t] */
static int LADJ[MAXN][MAXD];
static int LDEG[MAXN];
static int VIS[MAXN], VST = 0;
static int QU[MAXN];

static void set_dart_perm(int t) {
    for (int g = 0; g < G; g++) DPERM[t][g] = MT[g * G + DS[t]];
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

/* One annealing run over voltages and layer permutations for group gi. */
static int lift_climb(int kb, int gi, long steps, Graph *out) {
    select_group(gi);
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

/* Pick a pool group whose lift order 2*kb*G lies in [lo, hi]. Prefers nonabelian
 * groups and small orders (the smallest eligible lift beats the current best most often). */
static int pick_group(int kb, long lo, long hi) {
    static int all[MAXP], nonab[MAXP];
    int na = 0, nn = 0;
    for (int gi = 0; gi < NGR; gi++) {
        long N2 = 2L * kb * GORD[gi];
        if (N2 < lo || N2 > hi) continue;
        all[na++] = gi;
        if (!GCYC[gi]) nonab[nn++] = gi;
    }
    if (na == 0) return -1;
    int *src = all;
    int cnt = na;
    if (nn > 0 && rndint(10) < 8) { src = nonab; cnt = nn; }
    int gi = src[rndint(cnt)];
    for (int k = 0; k < 2; k++) {
        int g2 = src[rndint(cnt)];
        if (GORD[g2] < GORD[gi]) gi = g2;
    }
    return gi;
}

static void lift_search(Graph *best, double until) {
    long cap = moore_bound();
    if (cap > MAXN) cap = MAXN;
    int fails = 0;
    while (now() < until) {
        if (best->n + 2 > cap) return;
        int kb = 0, gi = -1;
        int k0 = rndint(3);
        for (int t = 0; t < 3 && gi < 0; t++) {
            kb = 1 + (k0 + t) % 3;
            gi = pick_group(kb, best->n + 2, cap);
        }
        if (gi < 0) return;
        long extra = (long)(fails / 20) * 4000;
        if (extra > 60000) extra = 60000;
        long steps = 3000 + rndint(9000) + extra;
        int before = best->n;
        if (lift_climb(kb, gi, steps, &LCAND) && LCAND.n > best->n && is_valid(&LCAND))
            copy_graph(best, &LCAND);
        fails = best->n > before ? 0 : fails + 1;
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
        fprintf(stderr, "usage: %s d D seed time_limit < stream\n", argv[0]);
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

    read_input();
    long p = parse_groups();
    static Graph best, start;
    read_start(&best, p);
    if (best.n == 0) complete_bipartite(&best);
    copy_graph(&start, &best);

    if (best.n < moore_bound()) {
        if (NGR > 0) lift_search(&best, t0 + (t_end - t0) * 0.85);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) copy_graph(&best, &start);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''

MAXG = 340  # largest group order passed to C (the C side accepts up to 400)


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


# ------------------------------------------------------------ group pool

def _perm_mul(p, q):
    return tuple(p[i] for i in q)


def _mat_mul(p):
    def mul(A, B):
        a, b, c, e = A
        f, g, h, k = B
        return ((a * f + b * h) % p, (a * g + b * k) % p,
                (c * f + e * h) % p, (c * g + e * k) % p)
    return mul


def _heis(p):
    def mul(a, b):
        return ((a[0] + b[0]) % p, (a[1] + b[1]) % p, (a[2] + b[2] + a[0] * b[1]) % p)
    return mul


def _generate(gens, mul, ident, cap=MAXG):
    """Closure of ident under right multiplication by gens; returns (elems, index) or None."""
    elems = [ident]
    index = {ident: 0}
    frontier = [ident]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = mul(x, g)
                if y not in index:
                    if len(elems) >= cap:
                        return None
                    index[y] = len(elems)
                    elems.append(y)
                    nxt.append(y)
        frontier = nxt
    return elems, index


def _table_of(elems, index, mul):
    G = len(elems)
    return G, [index[mul(a, b)] for a in elems for b in elems]


def _cyc(k):
    return k, [(x + y) % k for x in range(k) for y in range(k)]


def _dprod(A, B):
    G1, t1 = A
    G2, t2 = B
    G = G1 * G2
    out = [0] * (G * G)
    for a in range(G1):
        for b in range(G2):
            row = (a * G2 + b) * G
            for c in range(G1):
                ac = t1[a * G1 + c] * G2
                base = c * G2
                for e in range(G2):
                    out[row + base + e] = ac + t2[b * G2 + e]
    return G, out


def _pspec(gens):
    return gens, _perm_mul, tuple(range(len(gens[0])))


def _base_groups(deadline):
    specs = [
        _pspec([(1, 0, 2), (1, 2, 0)]),                    # S3
        _pspec([(1, 2, 3, 0), (0, 3, 2, 1)]),              # D4
        _pspec([(1, 2, 3, 4, 0), (0, 4, 3, 2, 1)]),        # D5
        _pspec([(1, 2, 3, 4, 5, 0), (0, 5, 4, 3, 2, 1)]),  # D6
        _pspec([(1, 2, 0, 3), (1, 0, 3, 2)]),              # A4
        _pspec([(1, 0, 2, 3), (1, 2, 3, 0)]),              # S4
        _pspec([(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)]),        # A5
        _pspec([(1, 2, 0, 3, 4, 5), (0, 1, 2, 4, 5, 3), (3, 4, 5, 0, 1, 2)]),  # Z3 wr Z2
        _pspec([(1, 2, 3, 4, 0), (0, 2, 4, 1, 3)]),        # F20 = AGL(1,5)
        _pspec([(1, 2, 3, 4, 5, 6, 0), (0, 2, 4, 6, 1, 3, 5)]),  # F21 = AGL(1,7) part
        ([(1, 1, 0, 1), (0, 2, 1, 0)], _mat_mul(3), (1, 0, 0, 1)),            # SL(2,3)
        ([(1, 1, 0, 1), (0, 1, 1, 0), (2, 0, 0, 1)], _mat_mul(3), (1, 0, 0, 1)),  # GL(2,3)
        ([(1, 1, 0, 1), (0, 4, 1, 0)], _mat_mul(5), (1, 0, 0, 1)),            # SL(2,5)
        ([(1, 0, 0), (0, 1, 0)], _heis(3), (0, 0, 0)),                        # Heisenberg mod 3
        ([(1, 0, 0), (0, 1, 0)], _heis(5), (0, 0, 0)),                        # Heisenberg mod 5
    ]
    bases = []
    for gens, mul, ident in specs:
        if time.monotonic() > deadline:
            break
        r = _generate(gens, mul, ident)
        if r is not None:
            bases.append(_table_of(r[0], r[1], mul))
    return bases


def _pool(deadline, budget_ints=500_000):
    """Group pool for C: ("T", G, table) entries and ("C", k) cyclic entries."""
    bases = _base_groups(deadline)
    pool = [("T", G, t) for G, t in bases if 2 <= G <= MAXG]
    used = sum(G * G for G, _ in bases)

    cands = []
    for i, (G1, _) in enumerate(bases):
        for k in (2, 3, 4, 5, 6, 7, 8, 9, 10, 12):
            if 24 <= G1 * k <= MAXG:
                cands.append((G1 * k, ("BC", i, k)))
        for j in range(i + 1, len(bases)):
            G2 = bases[j][0]
            if 24 <= G1 * G2 <= MAXG:
                cands.append((G1 * G2, ("BB", i, j)))
    cands.sort()
    for order, spec in cands:
        if time.monotonic() > deadline or used + order * order > budget_ints:
            continue
        if spec[0] == "BC":
            G, t = _dprod(bases[spec[1]], _cyc(spec[2]))
        else:
            G, t = _dprod(bases[spec[1]], bases[spec[2]])
        pool.append(("T", G, t))
        used += G * G

    for k in range(6, MAXG + 1):
        pool.append(("C", k))
    return pool


def _stream(pool, start):
    """Pack pool and start graph into the (n, pairs) stdin format read by the C engine."""
    n0, edges0 = start
    flat = [len(pool)]
    for e in pool:
        if e[0] == "C":
            flat.append(-e[1])
        else:
            flat.append(e[1])
            flat.extend(e[2])
    flat.append(n0)
    flat.append(len(edges0))
    for u, v in edges0:
        flat.extend((u, v))
    if len(flat) % 2:
        flat.append(0)
    return [(flat[i], flat[i + 1]) for i in range(0, len(flat), 2)]


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

    if best[0] >= lib.moore_bound(d, D):
        return best

    try:
        pool = _pool(time.monotonic() + min(3.0, 0.1 * time_limit))
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
        if budget < 0.5 or not pool:
            return best
        pairs = _stream(pool, best)
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=(0, pairs), timeout=budget + 5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except Exception:
        pass
    return best
