"""Explicit matrix-group bi-Cayley lifts (SL/GL over F_p), searched in C.

Change of construction for d=5, D=5: instead of semidirect products Z_m x| Z_k, the C engine
builds finite linear groups G = {M in GL(2,p) : det(M)^e = 1} by enumerating matrices. These
include non-metabelian groups such as SL(2,5) (order 120) and SL(2,7) (order 336). A base with
KB vertices per side (KB <= 4) and d darts per base vertex is lifted over G with right
multiplication: dart (i, j, s) joins A_{i,x} to B_{j,x*s}. Left multiplication by G is an
automorphism, so the diameter is <= D iff BFS of depth D from the 2*KB class representatives
reaches every vertex. Darts and layer permutations are annealed on the number of unreached
pairs. Candidates (group, KB) are tried in order of decreasing order, round robin, with
steps growing per pass. Every output is re-checked in C and Python.

Fallbacks: the start graph is always valid (K_{d,d}, or a known construction for D = 3 or 4),
and the output is returned only after lib.is_valid passes.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley / group-lift search over matrix groups GL(2,p) with det^e = 1.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
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
#define MAXG 800
#define MAXCAND 256
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

/* ------------------------------------------------------------ matrix groups */

/* G = {M in GL(2,p) : det(M)^e = 1}, elements stored as (a,b,c,d) with index in 0..GN-1. */
static int IDX[14641];            /* p^4 for p <= 11, code = ((a*p+b)*p+c)*p+dd */
static int EL[MAXG][4];
static int GN, GID;
static int GMT[MAXG][MAXG];       /* GMT[x][y] = index of x*y */
static int CUR_P = -1, CUR_E = -1;

static int count_group(int p, int e) {
    int cnt = 0;
    for (int a = 0; a < p; a++)
        for (int b = 0; b < p; b++)
            for (int c = 0; c < p; c++)
                for (int dd = 0; dd < p; dd++) {
                    int det = ((a * dd - b * c) % p + p) % p;
                    if (det && powmod(det, e, p) == 1 % p) cnt++;
                }
    return cnt;
}

static int build_group(int p, int e) {
    if (CUR_P == p && CUR_E == e) return 1;
    CUR_P = CUR_E = -1;
    int P4 = p * p * p * p;
    for (int k = 0; k < P4; k++) IDX[k] = -1;
    int cnt = 0;
    for (int a = 0; a < p; a++)
        for (int b = 0; b < p; b++)
            for (int c = 0; c < p; c++)
                for (int dd = 0; dd < p; dd++) {
                    int det = ((a * dd - b * c) % p + p) % p;
                    if (!det || powmod(det, e, p) != 1 % p) continue;
                    if (cnt >= MAXG) return 0;
                    IDX[((a * p + b) * p + c) * p + dd] = cnt;
                    EL[cnt][0] = a; EL[cnt][1] = b; EL[cnt][2] = c; EL[cnt][3] = dd;
                    cnt++;
                }
    GN = cnt;
    if (GN < 2) return 0;
    int idcode = ((1 * p + 0) * p + 0) * p + 1;
    GID = IDX[idcode];
    if (GID < 0) return 0;
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++) {
            int a1 = EL[x][0], b1 = EL[x][1], c1 = EL[x][2], d1 = EL[x][3];
            int a2 = EL[y][0], b2 = EL[y][1], c2 = EL[y][2], d2 = EL[y][3];
            int a = (a1 * a2 + b1 * c2) % p;
            int b = (a1 * b2 + b1 * d2) % p;
            int c = (c1 * a2 + d1 * c2) % p;
            int dd = (c1 * b2 + d1 * d2) % p;
            int z = IDX[((a * p + b) * p + c) * p + dd];
            if (z < 0) return 0;
            GMT[x][y] = z;
        }
    CUR_P = p;
    CUR_E = e;
    return 1;
}

typedef struct { int p, e, kb, N; } Cand;
static Cand CAND[MAXCAND];
static int NC = 0;

static void make_candidates(int cap) {
    static const int primes[5] = {2, 3, 5, 7, 11};
    NC = 0;
    for (int pi = 0; pi < 5; pi++) {
        int p = primes[pi];
        for (int e = 1; e <= p - 1; e++) {
            if ((p - 1) % e) continue;
            int g = count_group(p, e);
            if (g < 2 || g > MAXG) continue;
            for (int kb = 1; kb <= MAXK; kb++) {
                int N = 2 * kb * g;
                if (N > cap) break;
                if (NC < MAXCAND) {
                    CAND[NC].p = p;
                    CAND[NC].e = e;
                    CAND[NC].kb = kb;
                    CAND[NC].N = N;
                    NC++;
                }
            }
        }
    }
    for (int i = 1; i < NC; i++) {       /* insertion sort, largest N first */
        Cand c = CAND[i];
        int j = i - 1;
        while (j >= 0 && CAND[j].N < c.N) { CAND[j + 1] = CAND[j]; j--; }
        CAND[j + 1] = c;
    }
}

/* ------------------------------------------------------------ bi-Cayley lifts */

/* Base: KB vertices per side, ND = d*KB darts. Dart t = (DI, DJ, DS) joins
 * A_{DI,x} to B_{DJ,x*DS}. Vertex index: A_{i,x} = i*GN + x, B_{j,y} = (KB+j)*GN + y. */
static int KB, ND;
static int DI[MAXDART], DJ[MAXDART], DS[MAXDART];
static int LADJ[MAXN][MAXD];
static int LDEG[MAXN];
static int VIS[MAXN], VST = 0;
static int QU[MAXN];

static int has_dup(void) {
    for (int t1 = 0; t1 < ND; t1++)
        for (int t2 = t1 + 1; t2 < ND; t2++)
            if (DI[t1] == DI[t2] && DJ[t1] == DJ[t2] && DS[t1] == DS[t2]) return 1;
    return 0;
}

static void build_ladj(void) {
    int N = 2 * KB * GN;
    for (int v = 0; v < N; v++) LDEG[v] = 0;
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < GN; x++) {
            int a = DI[t] * GN + x;
            int b = (KB + DJ[t]) * GN + GMT[x][DS[t]];
            LADJ[a][LDEG[a]++] = b;
            LADJ[b][LDEG[b]++] = a;
        }
}

/* Unreached (representative, vertex) pairs over the 2KB class representatives. */
static long orbit_cost(void) {
    if (has_dup()) return BIGCOST;
    build_ladj();
    int N = 2 * KB * GN;
    long total = 0;
    for (int rep = 0; rep < 2 * KB; rep++) {
        int src = rep * GN + GID;
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
    int N = 2 * KB * GN;
    g->n = N;
    for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = v >= KB * GN; }
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < GN; x++)
            add_edge(g, DI[t] * GN + x, (KB + DJ[t]) * GN + GMT[x][DS[t]]);
}

/* One annealing run for base size kb over the currently loaded group. */
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
            DS[t] = rndint(GN);
        }
    }
    long cost = orbit_cost();
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 31) == 0 && now() > t_end) return 0;
        double T = 2.0 * (1.0 - (double)s / (double)steps) + 0.05;
        if (rnd01() < 0.7) {
            int t = rndint(ND);
            int old = DS[t];
            int nv = rndint(GN);
            if (nv == old) continue;
            DS[t] = nv;
            long c2 = orbit_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else DS[t] = old;
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
    t_end = t0 + limit * 0.93;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (d == 1 || D < 2) { printf("2 1\n0 1\n"); return 0; }

    static Graph best, start, LCAND;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    copy_graph(&start, &best);

    long moore = moore_bound();
    long cap = moore < MAXN ? moore : MAXN;
    make_candidates((int)cap);

    int pass = 0;
    while (now() < t_end) {
        int progress = 0;
        for (int c = 0; c < NC && now() < t_end; c++) {
            if (CAND[c].N <= best.n) continue;
            if (!build_group(CAND[c].p, CAND[c].e)) continue;
            progress = 1;
            long steps = 2000 + 1500L * pass + rndint(3000);
            if (steps > 150000) steps = 150000;
            if (lift_climb(CAND[c].kb, steps, &LCAND) &&
                LCAND.n > best.n && is_valid(&LCAND))
                copy_graph(&best, &LCAND);
        }
        if (!progress) break;
        pass++;
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

    # Leave a margin for compilation, process startup and the final Python check.
    budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 3)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
