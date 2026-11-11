"""Multi-orbit bi-lift search for the weakest case (d = 5, D = 7 is the target).

New idea in this version: a generalised bi-Cayley lift with K orbits on each side. Take a group G of
order N (semidirect product Z_m x|_r Z_k), vertices A_i,x and B_j,x for i, j < K, x in G, and a K x K
base multigraph with cell counts c_ij whose rows and columns each sum to d. Each dart g in cell (i,j)
joins A_i,x to B_j,x*g. The graph has 2KN vertices and is bipartite and d-regular.

Left multiplication by G is an automorphism, so a diameter check needs only the 2K BFS runs from the
identity vertices of each orbit. K = 2 gives 4N vertices, so it reaches new orders that the K = 1 lift
(the parent's construction) misses. Voltages and the cell-count pattern are annealed together. The
C engine chooses K per trial and keeps the largest valid graph. The hexagon start (2730 vertices for
d = 5, D = 7) is the fallback, and build() validates every output with lib.is_valid.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-orbit bi-lift search over semidirect groups Z_m x|_r Z_k.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0".
 * stdout:  the best valid graph found (a bi-lift if it beats the start, else the start).
 *
 * Vertices: A_{i,x} = i*N + x, B_{j,x} = (K+j)*N + x, for i,j < K and x in G, |G| = N.
 * Edges:    for each cell (i,j) and each voltage g in that cell, A_{i,x} -- B_{j, x*g}.
 * Cell counts: row and column sums are d. For K = 1 the single cell holds d voltages.
 *              For K = 2 the counts are c, d-c, d-c, c with 1 <= c <= d-1.
 * Left multiplication by G is an automorphism, transitive on each side orbit, so the diameter
 * check is BFS from the 2K identity vertices A_{i,e} and B_{j,e}.
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
#define MAXV 8192
#define MAXE 40000
#define MAXOUT 200000
#define MAXCAND 512
#define STEPS 20000
#define SPAN 40
#define NCELL 4

typedef struct { int m, k, r; } Grp;
typedef struct { int K; int cnt[NCELL]; int V[NCELL][MAXD]; } State;

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

/* Current group: element (a,b) coded as a*k+b, product (a,b)(c,e) = (a + r^b c, b + e). */
static int NN, GM, GK;
static int RP[MAXH];

static void setup_group(int N, Grp G) {
    NN = N;
    GM = G.m;
    GK = G.k;
    RP[0] = 1 % GM;
    for (int b = 1; b < GK; b++) RP[b] = (int)((long)RP[b - 1] * G.r % GM);
}

static int gmul(int x, int y) {
    int k = GK, m = GM;
    int a = x / k, b = x % k, c = y / k, e = y % k;
    int t = (int)(((long)a + (long)RP[b] * c) % m);
    return t * k + (b + e) % k;
}

static int in_cell(const State *S, int cell, int upto, int v) {
    for (int t = 0; t < upto; t++)
        if (S->V[cell][t] == v) return 1;
    return 0;
}

/* Fill voltages [from, to) of a cell with fresh distinct random group elements. */
static void fill_cell(State *S, int cell, int from, int to) {
    for (int t = from; t < to; t++) {
        int nv;
        do { nv = rndint(NN); } while (in_cell(S, cell, t, nv));
        S->V[cell][t] = nv;
    }
}

static void init_state(State *S, int K) {
    S->K = K;
    for (int c = 0; c < NCELL; c++) S->cnt[c] = 0;
    if (K == 1) {
        S->cnt[0] = d;
    } else {
        int c = 1 + rndint(d - 1);
        S->cnt[0] = c;
        S->cnt[3] = c;
        S->cnt[1] = d - c;
        S->cnt[2] = d - c;
    }
    for (int c = 0; c < K * K; c++) fill_cell(S, c, 0, S->cnt[c]);
}

static void set_cnt(State *S, int cell, int nc) {
    int old = S->cnt[cell];
    if (nc > old) fill_cell(S, cell, old, nc);
    S->cnt[cell] = nc;
}

static int ADJ[MAXV * MAXD];
static int DEG[MAXV];
static int SEEN[MAXV];
static int DIST[MAXV];
static int QUE[MAXV];
static int stamp_ = 0;

/* Build the explicit adjacency of the lift. Returns the vertex count 2KN. */
static int build_adj(const State *S) {
    int N = NN, K = S->K, V = 2 * K * N;
    for (int v = 0; v < V; v++) DEG[v] = 0;
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++) {
            int cell = i * K + j;
            for (int t = 0; t < S->cnt[cell]; t++) {
                int g = S->V[cell][t];
                for (int x = 0; x < N; x++) {
                    int a = i * N + x;
                    int b = (K + j) * N + gmul(x, g);
                    ADJ[a * MAXD + DEG[a]++] = b;
                    ADJ[b * MAXD + DEG[b]++] = a;
                }
            }
        }
    return V;
}

/* Number of (source, vertex) pairs at distance > D over the 2K identity sources. */
static long eval_bad(const State *S) {
    int V = build_adj(S);
    int K = S->K;
    long total = 0;
    for (int s = 0; s < 2 * K; s++) {
        int src = s * NN;
        int head = 0, tail = 0;
        stamp_++;
        SEEN[src] = stamp_;
        DIST[src] = 0;
        QUE[tail++] = src;
        while (head < tail) {
            int v = QUE[head++];
            int dv = DIST[v];
            if (dv >= D) continue;
            for (int t = 0; t < DEG[v]; t++) {
                int u = ADJ[v * MAXD + t];
                if (SEEN[u] != stamp_) {
                    SEEN[u] = stamp_;
                    DIST[u] = dv + 1;
                    QUE[tail++] = u;
                }
            }
        }
        total += V - tail;
    }
    return total;
}

/* Simulated annealing over voltages and, for K = 2, the cell-count pattern. */
static long climb(State *S, double until) {
    long bad = eval_bad(S);
    double T = 2.0;
    State saved;
    for (long s = 0; s < STEPS && bad > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        saved = *S;
        if (S->K == 2 && rnd01() < 0.03) {
            int c = S->cnt[0];
            int nc = c + ((rnd() & 1) ? 1 : -1);
            if (nc < 1 || nc > d - 1) continue;
            set_cnt(S, 0, nc);
            set_cnt(S, 3, nc);
            set_cnt(S, 1, d - nc);
            set_cnt(S, 2, d - nc);
        } else {
            int cell = rndint(S->K * S->K);
            int t = rndint(S->cnt[cell]);
            int nv;
            do { nv = rndint(NN); } while (in_cell(S, cell, S->cnt[cell], nv));
            S->V[cell][t] = nv;
        }
        long nb = eval_bad(S);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else *S = saved;
        T *= 0.9995;
        if (T < 0.2) T = 0.2;
    }
    return bad;
}

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

    static int OU[MAXOUT], OV[MAXOUT];
    int found = 0, ne = 0;
    int bestV = sn;

    if (d >= 3 && d <= MAXD && D >= 2) {
        long moore = moore_bound();
        static Grp cand[MAXCAND];
        State S;
        while (now() < t_end) {
            int K = ((int)(rnd() % 10) < 7) ? 2 : 1;
            long lo = bestV / (2 * K) + 1;
            if (lo < d + 1) lo = d + 1;
            long hi = moore / (2 * K);
            if (hi > MAXH) hi = MAXH;
            if (lo > hi) {
                K = 3 - K;
                lo = bestV / (2 * K) + 1;
                if (lo < d + 1) lo = d + 1;
                hi = moore / (2 * K);
                if (hi > MAXH) hi = MAXH;
                if (lo > hi) break;
            }
            long span = hi - lo + 1;
            if (span > SPAN) span = SPAN;
            int N = (int)(lo + rndint((int)span));
            int cnt = enum_groups(N, cand);
            if (cnt <= 0) continue;
            Grp G = pick_group(cand, cnt);
            setup_group(N, G);
            init_state(&S, K);
            long bad = climb(&S, t_end);
            if (bad == 0) {
                found = 1;
                bestV = 2 * K * N;
                ne = 0;
                for (int i = 0; i < K; i++)
                    for (int j = 0; j < K; j++) {
                        int cell = i * K + j;
                        for (int t = 0; t < S.cnt[cell]; t++) {
                            int g = S.V[cell][t];
                            for (int x = 0; x < N; x++) {
                                if (ne >= MAXOUT) break;
                                OU[ne] = i * N + x;
                                OV[ne] = (K + j) * N + gmul(x, g);
                                ne++;
                            }
                        }
                    }
            }
        }
    }

    if (found) {
        printf("%d %d\n", bestV, ne);
        for (int i = 0; i < ne; i++) printf("%d %d\n", OU[i], OV[i]);
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
    The caller validates the result with lib.is_valid.
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
