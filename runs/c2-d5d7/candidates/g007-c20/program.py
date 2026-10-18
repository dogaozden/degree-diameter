"""Bi-Cayley group-lift search, followed by edge-switch vertex-insertion growth.

Phase 1 (lift): for a semidirect group G = Z_m x|_r Z_k of order N, take vertices a_x, b_x
(x in G) and join a_x to b_{x*g_t} for d distinct voltages g_t (g_0 = identity). Left
multiplication by G is transitive on each side, so the diameter check needs only two BFS runs.
The C engine hill-climbs the voltages and raises N while a valid lift exists.

Phase 2 (growth, new in this version): starting from the best valid graph (lift or algebraic
start), repeatedly insert a pair of new vertices a', b'. Pick d edges (u_i, v_i) with distinct
endpoints, replace each by (u_i, b') and (a', v_i). Every old vertex keeps its degree, and the
new vertices have degree d. The diameter defect is then reduced by simulated annealing over
degree-preserving 2-switches (a,b),(c,e) -> (a,e),(c,b). Each state is scored by the number of
vertex pairs at distance > D, computed with bitset BFS. A successful attempt (defect 0) becomes
the new base. A failed attempt is discarded.

The output is always a valid graph: either the grown graph, or the start graph unchanged.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Bi-Cayley lift search over semidirect groups, then edge-switch vertex-insertion growth.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0".
 * stdout:  the best valid graph found (grown or lifted if it beats the start, else the start).
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXH 2048
#define MAXD 16
#define MAXE 40000
#define MAXN 4200
#define MAXW ((MAXN + 63) / 64)
#define MAXCAND 512
#define STEPS 8000
#define SPAN 40
#define ATTEMPT_STEPS 800

typedef struct { int m, k, r; } Grp;

typedef struct {
    int n, ne;
    int deg[MAXN];
    int nb[MAXN][MAXD];
    int side[MAXN];
    int EU[MAXE], EV[MAXE];   /* EU = side-0 endpoint, EV = side-1 endpoint */
} G;

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

/* Enumerate Z_m x|_r Z_k with m*k = N, gcd(r,m)=1, r^k = 1 mod m. */
static int enum_groups(int N, Grp *out) {
    int cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (cnt < MAXCAND) { out[cnt].m = 1; out[cnt].k = k; out[cnt].r = 0; cnt++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (cnt < MAXCAND) { out[cnt].m = m; out[cnt].k = k; out[cnt].r = r; cnt++; }
        }
    }
    return cnt;
}

static Grp pick_group(const Grp *c, int cnt) {
    for (int tries = 0; tries < 8; tries++) {
        Grp g = c[rndint(cnt)];
        if (g.m > 1 && g.r != 1) return g;
    }
    return c[rndint(cnt)];
}

/* Multiplication table and inverses for the current group. */
static int MTAB[MAXH * MAXH];
static int INVT[MAXH];
static int RP[MAXH];
static int NN;

static void setup_group(int N, Grp G0) {
    NN = N;
    int m = G0.m, k = G0.k;
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * G0.r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            row[y] = (int)((((long)a + (long)RP[b] * c) % m) * k + (b + e) % k);
        }
    }
    for (int x = 0; x < N; x++) {
        const int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++)
            if (row[y] == 0) { INVT[x] = y; break; }
    }
}

static int used_upto(const int *gv, int cnt, int v) {
    for (int i = 0; i < cnt; i++)
        if (gv[i] == v) return 1;
    return 0;
}

static int dist_[2 * MAXH], seen_[2 * MAXH], q_[2 * MAXH];
static int stamp_ = 0;

/* Number of (source, vertex) pairs at distance > D, sources a_e and b_e. */
static long eval_bad(const int *gv) {
    int N = NN, V = 2 * N;
    int gi[MAXD];
    for (int t = 0; t < d; t++) gi[t] = INVT[gv[t]];
    long total = 0;
    for (int s = 0; s < 2; s++) {
        int src = s ? N : 0;
        int head = 0, tail = 0;
        stamp_++;
        seen_[src] = stamp_;
        dist_[src] = 0;
        q_[tail++] = src;
        while (head < tail) {
            int v = q_[head++];
            int dv = dist_[v];
            if (dv >= D) continue;
            if (v < N) {
                const int *row = MTAB + (size_t)v * N;
                for (int t = 0; t < d; t++) {
                    int u = N + row[gv[t]];
                    if (seen_[u] != stamp_) {
                        seen_[u] = stamp_;
                        dist_[u] = dv + 1;
                        q_[tail++] = u;
                    }
                }
            } else {
                const int *row = MTAB + (size_t)(v - N) * N;
                for (int t = 0; t < d; t++) {
                    int u = row[gi[t]];
                    if (seen_[u] != stamp_) {
                        seen_[u] = stamp_;
                        dist_[u] = dv + 1;
                        q_[tail++] = u;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

/* Annealed voltage hill-climb; gv[0] = 0 is kept fixed. */
static long climb(int *gv, double until) {
    long bad = eval_bad(gv);
    double T = 2.0;
    for (long s = 0; s < STEPS && bad > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        int t = 1 + rndint(d - 1);
        int old = gv[t], nv;
        do { nv = rndint(NN); } while (used_upto(gv, d, nv));
        gv[t] = nv;
        long nb = eval_bad(gv);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else gv[t] = old;
        T *= 0.9995;
        if (T < 0.2) T = 0.2;
    }
    return bad;
}

/* ---------------- general graph state, bitset diameter check, growth ---------------- */

static uint64_t RA[(size_t)MAXN * MAXW], RB[(size_t)MAXN * MAXW];

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered vertex pairs at distance > D (bitset BFS with D rounds). */
static long eval_G(const G *g) {
    int n = g->n;
    int W = (n + 63) >> 6;
    uint64_t *A = RA, *B = RB;
    memset(A, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) A[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *bv = B + (size_t)v * W;
            const uint64_t *av = A + (size_t)v * W;
            memcpy(bv, av, sizeof(uint64_t) * (size_t)W);
            for (int t = 0; t < g->deg[v]; t++) {
                const uint64_t *au = A + (size_t)g->nb[v][t] * W;
                for (int w = 0; w < W; w++) bv[w] |= au[w];
            }
        }
        uint64_t *tmp = A; A = B; B = tmp;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *av = A + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(av[w]);
        total += n - c;
    }
    return total / 2;
}

static void replace_nb(G *g, int v, int old, int nw) {
    for (int t = 0; t < g->deg[v]; t++)
        if (g->nb[v][t] == old) { g->nb[v][t] = nw; return; }
}

static int has_nb(const G *g, int v, int w) {
    for (int t = 0; t < g->deg[v]; t++)
        if (g->nb[v][t] == w) return 1;
    return 0;
}

/* Edge i = (a,b), edge j = (c,e) (a,c side 0; b,e side 1). Valid if the switch stays simple. */
static int switch_ok(const G *g, int i, int j) {
    if (i == j) return 0;
    int a = g->EU[i], b = g->EV[i], c = g->EU[j], e = g->EV[j];
    if (a == c || b == e) return 0;
    if (has_nb(g, a, e) || has_nb(g, c, b)) return 0;
    return 1;
}

/* (a,b),(c,e) -> (a,e),(c,b). Applying it twice to the same (i,j) restores the original. */
static void switch_edges(G *g, int i, int j) {
    int a = g->EU[i], b = g->EV[i], c = g->EU[j], e = g->EV[j];
    replace_nb(g, a, b, e);
    replace_nb(g, b, a, c);
    replace_nb(g, c, e, b);
    replace_nb(g, e, c, a);
    g->EV[i] = e;
    g->EU[j] = c;
    g->EV[j] = b;
}

static int stU[MAXN], stV[MAXN];
static int stamp_ins = 0;

/* Insert a new pair (a' side 0, b' side 1). Choose d edges (u_i,v_i) with distinct endpoints:
 * edge i becomes (u_i, b'), and the new edge (a', v_i) is appended. Degrees of old vertices are
 * unchanged, and a', b' get degree d. */
static int insert_pair(G *g) {
    if (g->ne + d > MAXE || g->n + 2 > MAXN) return 0;
    if (g->ne < d) return 0;
    int a = g->n, b = g->n + 1;
    int chosen[MAXD], cu[MAXD], cv[MAXD];
    int cnt = 0;
    stamp_ins++;
    for (int tries = 0; tries < 4000 && cnt < d; tries++) {
        int i = rndint(g->ne);
        int u = g->EU[i], v = g->EV[i];
        if (stU[u] == stamp_ins || stV[v] == stamp_ins) continue;
        stU[u] = stamp_ins;
        stV[v] = stamp_ins;
        cu[cnt] = u;
        cv[cnt] = v;
        chosen[cnt] = i;
        cnt++;
    }
    if (cnt < d) return 0;
    for (int k = 0; k < cnt; k++) {
        int i = chosen[k], u = cu[k], v = cv[k];
        g->EV[i] = b;
        replace_nb(g, u, v, b);
        int ni = g->ne++;
        g->EU[ni] = a;
        g->EV[ni] = v;
        replace_nb(g, v, u, a);
    }
    g->side[a] = 0;
    g->side[b] = 1;
    g->deg[a] = cnt;
    g->deg[b] = cnt;
    for (int k = 0; k < cnt; k++) {
        g->nb[a][k] = cv[k];
        g->nb[b][k] = cu[k];
    }
    g->n += 2;
    return 1;
}

/* Load a raw graph; returns 0 unless it is simple, bipartite, with max degree <= d. */
static int load_G(G *g, int n, int m, const int *U, const int *V) {
    if (d < 1 || d > MAXD) return 0;
    if (n <= 0 || n > MAXN - 2 || m < 0 || m > MAXE) return 0;
    g->n = n;
    g->ne = 0;
    for (int v = 0; v < n; v++) g->deg[v] = 0;
    for (int e = 0; e < m; e++) {
        int u = U[e], v = V[e];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (g->deg[u] >= d || g->deg[v] >= d) return 0;
        g->nb[u][g->deg[u]++] = v;
        g->nb[v][g->deg[v]++] = u;
    }
    for (int v = 0; v < n; v++)
        for (int s = 0; s < g->deg[v]; s++)
            for (int t = 0; t < s; t++)
                if (g->nb[v][s] == g->nb[v][t]) return 0;
    static int col[MAXN], qq[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        int head = 0, tail = 0;
        col[s] = 0;
        qq[tail++] = s;
        while (head < tail) {
            int u = qq[head++];
            for (int t = 0; t < g->deg[u]; t++) {
                int w = g->nb[u][t];
                if (col[w] == -1) { col[w] = 1 - col[u]; qq[tail++] = w; }
                else if (col[w] == col[u]) return 0;
            }
        }
    }
    for (int v = 0; v < n; v++) g->side[v] = col[v];
    for (int e = 0; e < m; e++) {
        int u = U[e], v = V[e];
        if (col[u] == 0) { g->EU[g->ne] = u; g->EV[g->ne] = v; }
        else { g->EU[g->ne] = v; g->EV[g->ne] = u; }
        g->ne++;
    }
    return 1;
}

static G BEST, CUR;

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
    double t_lift = t0 + limit * 0.9 * 0.4;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static int SU[MAXE], SV[MAXE];
    int sn = 0, sm = 0;
    if (scanf("%d %d", &sn, &sm) != 2) { sn = 0; sm = 0; }
    if (sn < 0 || sm < 0 || sm > MAXE) { sn = 0; sm = 0; }
    int got = 0;
    for (int e = 0; e < sm; e++) {
        if (scanf("%d %d", &SU[e], &SV[e]) != 2) break;
        got++;
    }
    if (got != sm) { sn = 0; sm = 0; }

    static int OU[MAXH * MAXD], OV[MAXH * MAXD];
    int found = 0, bestN = 0, ne = 0;

    /* Phase 1: bi-Cayley voltage lifts. */
    if (d >= 3 && d <= MAXD && D >= 2) {
        long moore = moore_bound();
        long Nlo_l = sn / 2 + 1;
        if (Nlo_l < d + 1) Nlo_l = d + 1;
        long Nmax_l = moore / 2;
        if (Nmax_l > MAXH) Nmax_l = MAXH;
        int Nlo = (int)Nlo_l, Nmax = (int)Nmax_l;
        static Grp cand[MAXCAND];
        int gv[MAXD];

        while (now() < t_lift && Nlo <= Nmax) {
            int span = Nmax - Nlo + 1;
            if (span > SPAN) span = SPAN;
            int N = Nlo + rndint(span);
            int cnt = enum_groups(N, cand);
            if (cnt <= 0) continue;
            Grp Gr = pick_group(cand, cnt);
            setup_group(N, Gr);
            gv[0] = 0;
            for (int t = 1; t < d; t++) {
                do { gv[t] = rndint(N); } while (used_upto(gv, t, gv[t]));
            }
            long bad = climb(gv, t_lift);
            if (bad == 0) {
                found = 1;
                bestN = N;
                Nlo = N + 1;
                ne = 0;
                for (int x = 0; x < N; x++)
                    for (int t = 0; t < d; t++) {
                        OU[ne] = x;
                        OV[ne] = N + MTAB[(size_t)x * N + gv[t]];
                        ne++;
                    }
            }
        }
    }

    /* Choose the base: the lift if it loads and checks valid, else the start graph. */
    int have_base = 0;
    if (found && bestN > 0) {
        if (load_G(&BEST, 2 * bestN, ne, OU, OV) && eval_G(&BEST) == 0) have_base = 1;
    }
    if (!have_base) {
        if (load_G(&BEST, sn, sm, SU, SV) && eval_G(&BEST) == 0) have_base = 1;
    }

    /* Phase 2: edge-switch vertex-insertion growth from the best valid graph. */
    if (have_base) {
        while (now() < t_end) {
            CUR = BEST;
            if (!insert_pair(&CUR)) break;
            long bad = eval_G(&CUR);
            double T = 0.8;
            for (int step = 0; bad > 0 && step < ATTEMPT_STEPS; step++) {
                if ((step & 31) == 0 && now() > t_end) break;
                int i = rndint(CUR.ne), j = rndint(CUR.ne);
                if (!switch_ok(&CUR, i, j)) continue;
                switch_edges(&CUR, i, j);
                long nb = eval_G(&CUR);
                if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
                else switch_edges(&CUR, i, j);
                T *= 0.997;
                if (T < 0.15) T = 0.15;
            }
            if (bad == 0) BEST = CUR;
        }
    }

    if (have_base && BEST.n > sn) {
        printf("%d %d\n", BEST.n, BEST.ne);
        for (int e = 0; e < BEST.ne; e++) printf("%d %d\n", BEST.EU[e], BEST.EV[e]);
    } else {
        printf("%d %d\n", sn, sm);
        for (int e = 0; e < sm; e++) printf("%d %d\n", SU[e], SV[e]);
    }
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
    Points: points of the quadric X0X4 + X1X5 + X2X6 = X3^2. Lines: quadric lines whose Grassmann
    coordinates satisfy p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31.
    Characteristic 2, so signs are irrelevant. The caller validates the result with lib.is_valid.
    """
    F = lib.GF(q)
    MT, AT = F.mul_table, F.add_table
    pts = []
    for v in itertools.product(range(q), repeat=7):
        if any(v) and next(c for c in v if c) == 1:
            s = AT[AT[MT[v[0], v[4]], MT[v[1], v[5]]], AT[MT[v[2], v[6]], MT[v[3], v[3]]]]
            if s == 0:
                pts.append(tuple(int(c) for c in v))
    N = len(pts)
    index = {v: i for i, v in enumerate(pts)}
    P = np.array(pts, dtype=np.int64)
    lines = set()
    for i in range(N - 1):
        x = P[i]
        Y = P[i + 1:]

        def pp(a, b):
            """Grassmann coordinate p_ab = x_a y_b - x_b y_a, for all y in Y."""
            return AT[MT[x[a], Y[:, b]], MT[x[b], Y[:, a]]]

        # Collinearity on the quadric: polar form B(x, y) = 0 (char 2 has no 2*x3*y3 term).
        s = np.zeros(len(Y), dtype=np.int64)
        for a, b in ((0, 4), (1, 5), (2, 6)):
            s = AT[s, AT[MT[x[a], Y[:, b]], MT[Y[:, a], x[b]]]]
        ok = (s == 0)
        ok &= pp(1, 2) == pp(3, 4)
        ok &= pp(5, 4) == pp(3, 2)
        ok &= pp(2, 0) == pp(3, 5)
        ok &= pp(6, 5) == pp(3, 0)
        ok &= pp(0, 1) == pp(3, 6)
        ok &= pp(4, 6) == pp(3, 1)
        for jj in np.nonzero(ok)[0]:
            y = Y[jj]
            # Points of the line: x, and t*x + y for t in GF(q).
            vecs = [tuple(int(c) for c in x)]
            for t in range(q):
                vecs.append(tuple(int(AT[MT[t, x[k]], y[k]]) for k in range(7)))
            idx = []
            for v in vecs:
                c = next(e for e in v if e)
                inv = F.inv(c)
                idx.append(index[tuple(F.mul(inv, e) for e in v)])
            lines.add(tuple(sorted(idx)))
    lines = sorted(lines)
    edges = [(pt, N + k) for k, L in enumerate(lines) for pt in L]
    return 2 * N, edges


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates (may be empty); build() keeps only those that pass lib.is_valid."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 6 and d - 1 in (2, 4):
        try:
            out.append(_hexagon_incidence(d - 1))
        except Exception:
            pass
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 16 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
