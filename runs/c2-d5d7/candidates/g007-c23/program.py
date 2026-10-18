"""Multi-orbit bi-Cayley voltage-lift search for the d = 5, D = 7 target.

New idea (not in the parent): a lift with K orbits per side instead of one. Take a group G of
order N and vertices A(i,x), B(j,y) for orbits i, j in 0..K-1 and x, y in G. Each layer t of a
d-layer base is a permutation sig[t] of the K orbits, with a voltage volt[i][t] in G. The edges are
A(i,x) -- B(sig[t][i], x*volt[i][t]) for all t. This gives 2KN vertices, all of degree d. Because
the base is a union of d permutations, every B-orbit also receives d darts. Duplicate edges
(same target and same voltage from one orbit) are penalised.

Left multiplication by G is an automorphism that is transitive on each orbit, so diameter <= D
reduces to BFS from A(i,e) and B(j,e) for all i, j (2K BFS runs). The C engine anneals over voltage
changes and target swaps. Orders 2KN are reachable in steps of 2N for every K = 1..6, so the search
can land just above the current best (for example 3110 = 10 * 311, and many nearby values).

Build order: known algebraic starts (hexagon, PG(2,q), W(q)) are checked with lib.is_valid. The C
engine then searches for larger lifts and returns the start graph if none is found.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-orbit bi-Cayley lift search over semidirect groups Z_m x|_r Z_kk.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0".
 * stdout:  the best valid graph found (a lift if it beats the start, else the start).
 *
 * Group G of order N. Vertices: A(i,x) = i*N + x, B(j,y) = (K+j)*N + y, orbits i,j < K.
 * Base:  for each layer t < d, a permutation sig[t] of the K orbits and voltages volt[i][t].
 * Edges: A(i,x) -- B(sig[t][i], x * volt[i][t]).  Every vertex has degree d.
 * Left multiplication by G is transitive on each orbit, so diameter <= D is checked by BFS from
 * A(i,e) and B(j,e) for all i, j (2K sources).
 * Cost = (pairs at distance > D from the sources) + DUPW * (duplicate edges).
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXK 8
#define KSEL 6
#define MAXKN 6000
#define MAXV 12000
#define MAXD 16
#define MAXE 200000
#define MAXCAND 4096
#define STEPS 4000
#define SPAN 24
#define DUPW 1000000L

typedef struct { int m, kk, r; } Grp;

static int d, D, K, NN;
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

/* Groups Z_m x|_r Z_kk with m*kk = N, gcd(r,m) = 1, r^kk = 1 mod m. */
static int enum_groups(int N, Grp *out) {
    int cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int kk = N / m;
        if (m == 1) {
            if (cnt < MAXCAND) { out[cnt].m = 1; out[cnt].kk = kk; out[cnt].r = 0; cnt++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, kk, m) != 1 % m) continue;
            if (cnt < MAXCAND) { out[cnt].m = m; out[cnt].kk = kk; out[cnt].r = r; cnt++; }
        }
    }
    return cnt;
}

static int MTAB[MAXN * MAXN];
static int INVT[MAXN];
static int RP[MAXN];

static void setup_group(int N, Grp G) {
    NN = N;
    int m = G.m, kk = G.kk;
    RP[0] = 1 % m;
    for (int b = 1; b < kk; b++) RP[b] = (int)((long)RP[b - 1] * G.r % m);
    for (int x = 0; x < N; x++) {
        int a = x / kk, b = x % kk;
        int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++) {
            int c = y / kk, e = y % kk;
            row[y] = (int)((((long)a + (long)RP[b] * c) % m) * kk + (b + e) % kk);
        }
    }
    for (int x = 0; x < N; x++) {
        const int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++)
            if (row[y] == 0) { INVT[x] = y; break; }
    }
}

static int sig[MAXD][MAXK];
static int invsig[MAXD][MAXK];
static int volt[MAXK][MAXD];

static int dist_[MAXV], seen_[MAXV], q_[MAXV];
static int stamp_ = 0;

/* Number of vertices at distance > D from source src (a vertex A(i,e) or B(j,e)). */
static long bfs_bad(int src) {
    const int N = NN, kN = K * N, V = 2 * kN;
    int head = 0, tail = 0;
    stamp_++;
    seen_[src] = stamp_;
    dist_[src] = 0;
    q_[tail++] = src;
    while (head < tail) {
        int v = q_[head++];
        int dv = dist_[v];
        if (dv >= D) continue;
        if (v < kN) {
            int i = v / N, x = v - i * N;
            const int *row = MTAB + (size_t)x * N;
            for (int t = 0; t < d; t++) {
                int u = kN + sig[t][i] * N + row[volt[i][t]];
                if (seen_[u] != stamp_) {
                    seen_[u] = stamp_;
                    dist_[u] = dv + 1;
                    q_[tail++] = u;
                }
            }
        } else {
            int w = v - kN, j = w / N, y = w - j * N;
            const int *row = MTAB + (size_t)y * N;
            for (int t = 0; t < d; t++) {
                int i = invsig[t][j];
                int u = i * N + row[INVT[volt[i][t]]];
                if (seen_[u] != stamp_) {
                    seen_[u] = stamp_;
                    dist_[u] = dv + 1;
                    q_[tail++] = u;
                }
            }
        }
    }
    return (long)(V - tail);
}

static long eval_cost(void) {
    long dup = 0;
    for (int i = 0; i < K; i++)
        for (int t = 0; t < d; t++)
            for (int s = t + 1; s < d; s++)
                if (sig[t][i] == sig[s][i] && volt[i][t] == volt[i][s]) dup++;
    long bad = 0;
    for (int s = 0; s < 2 * K; s++) bad += bfs_bad(s * NN);  /* sources A(s,e) or B(s-K,e) */
    return bad + dup * DUPW;
}

/* Swap the targets of orbits i1 and i2 in layer t; applying it twice restores the state. */
static void swap_targets(int t, int i1, int i2) {
    int a = sig[t][i1], b = sig[t][i2];
    sig[t][i1] = b;
    sig[t][i2] = a;
    invsig[t][b] = i1;
    invsig[t][a] = i2;
}

static long climb(double until) {
    long cur = eval_cost();
    double T = 2.0;
    for (long s = 0; s < STEPS && cur > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        if (K >= 2 && rndint(100) < 35) {
            int t = rndint(d), i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            swap_targets(t, i1, i2);
            long nc = eval_cost();
            if (nc <= cur || rnd01() < exp((double)(cur - nc) / T)) cur = nc;
            else swap_targets(t, i1, i2);
        } else {
            int i = rndint(K), t = rndint(d);
            int old = volt[i][t];
            int nv = rndint(NN);
            if (nv != old) {
                volt[i][t] = nv;
                long nc = eval_cost();
                if (nc <= cur || rnd01() < exp((double)(cur - nc) / T)) cur = nc;
                else volt[i][t] = old;
            }
        }
        T *= 0.9995;
        if (T < 0.25) T = 0.25;
    }
    return cur;
}

static void init_state(void) {
    int p[MAXK];
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            sig[t][i] = p[i];
            invsig[t][p[i]] = i;
        }
    }
    for (int i = 0; i < K; i++)
        for (int t = 0; t < d; t++)
            volt[i][t] = rndint(NN);
}

/* Feasible lift orders for K orbits: 2KN > Tbest, N in [d, MAXN], K*N <= MAXKN, 2KN <= moore. */
static int range_for(int k, long Tbest, long moore, long *lo, long *hi) {
    long l = Tbest / (2L * k) + 1;
    if (l < d) l = d;
    long h = MAXN;
    if (h > MAXKN / k) h = MAXKN / k;
    if (h > moore / (2L * k)) h = moore / (2L * k);
    *lo = l;
    *hi = h;
    return l <= h;
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

    static int OU[MAXKN * MAXD], OV[MAXKN * MAXD];
    int found = 0, bestV = 0, ne = 0;
    long Tbest = sn;

    if (d >= 3 && d <= MAXD && D >= 2) {
        long moore = moore_bound();
        static Grp cand[MAXCAND];
        while (now() < t_end) {
            int ks[KSEL], nks = 0;
            long lo = 0, hi = 0;
            for (int k = 1; k <= KSEL; k++)
                if (range_for(k, Tbest, moore, &lo, &hi)) ks[nks++] = k;
            if (nks == 0) break;
            K = ks[rndint(nks)];
            range_for(K, Tbest, moore, &lo, &hi);
            long span = hi - lo + 1;
            if (span > SPAN) span = SPAN;
            int N = (int)(lo + rndint((int)span));
            int cnt = enum_groups(N, cand);
            if (cnt <= 0) continue;
            setup_group(N, cand[rndint(cnt)]);
            init_state();
            if (climb(t_end) == 0) {
                found = 1;
                Tbest = 2L * K * N;
                bestV = (int)Tbest;
                ne = 0;
                for (int i = 0; i < K; i++)
                    for (int x = 0; x < N; x++)
                        for (int t = 0; t < d; t++) {
                            OU[ne] = i * N + x;
                            OV[ne] = (K + sig[t][i]) * N + MTAB[(size_t)x * N + volt[i][t]];
                            ne++;
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
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
