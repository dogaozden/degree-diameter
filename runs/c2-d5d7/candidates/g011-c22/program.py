"""Bi-Cayley voltage search v2: ascending hill-climb over group order, with a Python-side rebuild.

Construction: for a group G of order N (semidirect product Z_m x|_r Z_k), vertices a_x and b_x
(x in G) with a_x adjacent to b_{x*g_t} for d distinct voltages g_0 = e, ..., g_{d-1}.
Left multiplication by G is an automorphism, transitive on each side, so the diameter is <= D
iff BFS from a_e and from b_e reaches everything within D.

Differences from v1: the C engine emits only (order, m, k, r, voltages), not a full graph. Python
rebuilds the lift with lib.semidirect_group and lib.group_lift, then checks it with lib.is_valid.
The order N climbs by small random steps above the best success so far, and each order gets a
few random groups with annealed voltage search. The start graph is the fallback, so every case
returns a valid graph.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Bi-Cayley voltage search with an ascending group-order hill climb.
 * Usage: prog d D seed time_limit Nstart Nmax
 * stdout: "ORDER m k r" then d voltages on one line, or "0 0 0 0" if nothing was found.
 * Vertices of the lift: a_x = x, b_x = N + x. Edge a_x -- b_{x*g_t}.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXD 16
#define MAXCAND 4096
#define CLIMB_STEPS 12000
#define GROUP_TRIES 6
#define N_SPAN 4

typedef struct { int m, k, r; } Grp;

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static Grp CAND[MAXCAND];
static int NCAND = 0;

/* All semidirect products Z_m x|_r Z_k with m*k = N, gcd(r, m) = 1, r^k = 1 mod m. */
static void enum_groups(int N) {
    NCAND = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (NCAND < MAXCAND) {
                CAND[NCAND].m = 1; CAND[NCAND].k = k; CAND[NCAND].r = 0; NCAND++;
            }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1 % m) continue;
            if (NCAND < MAXCAND) {
                CAND[NCAND].m = m; CAND[NCAND].k = k; CAND[NCAND].r = r; NCAND++;
            }
        }
    }
}

static int *MT = NULL;
static int INV[MAXN];
static int RP[MAXN];
static int NN;

static void setup_group(Grp G) {
    int m = G.m, k = G.k, N = m * k;
    NN = N;
    if (!MT) MT = (int *)malloc(sizeof(int) * (size_t)MAXN * MAXN);
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * G.r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        int *row = MT + (size_t)x * N;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            row[y] = (int)((((long)a + (long)RP[b] * c) % m) * k + (b + e) % k);
        }
    }
    for (int x = 0; x < N; x++) {
        const int *row = MT + (size_t)x * N;
        for (int y = 0; y < N; y++)
            if (row[y] == 0) { INV[x] = y; break; }
    }
}

static int used_in(const int *gv, int cnt, int v) {
    for (int i = 0; i < cnt; i++)
        if (gv[i] == v) return 1;
    return 0;
}

static int dist_[2 * MAXN], seen_[2 * MAXN], q_[2 * MAXN];
static int stamp_ = 0;

/* Number of (source, vertex) pairs unreached within D, sources a_e and b_e. */
static long eval_bad(const int *gv) {
    int N = NN, V = 2 * N;
    int gi[MAXD];
    for (int t = 0; t < d; t++) gi[t] = INV[gv[t]];
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
                const int *row = MT + (size_t)v * N;
                for (int t = 0; t < d; t++) {
                    int u = N + row[gv[t]];
                    if (seen_[u] != stamp_) {
                        seen_[u] = stamp_;
                        dist_[u] = dv + 1;
                        q_[tail++] = u;
                    }
                }
            } else {
                const int *row = MT + (size_t)(v - N) * N;
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

/* Annealed voltage search; gv[0] = identity is kept fixed (WLOG by right translation). */
static long climb(int *gv, int steps) {
    long bad = eval_bad(gv);
    double T = 1.5;
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 63) == 0 && now() > t_end) break;
        int t = 1 + rndint(d - 1);
        int old = gv[t], nv;
        do { nv = rndint(NN); } while (used_in(gv, d, nv));
        gv[t] = nv;
        long nb = eval_bad(gv);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else gv[t] = old;
        T *= 0.9997;
        if (T < 0.15) T = 0.15;
    }
    return bad;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: %s d D seed time_limit Nstart Nmax\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int Nstart = atoi(argv[5]);
    int Nmax = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    int bestN = 0, bestm = 0, bestk = 0, bestr = 0;
    int bestgv[MAXD];

    if (d >= 3 && d <= MAXD && D >= 2) {
        if (Nmax > MAXN) Nmax = MAXN;
        int lo = Nstart;
        if (lo < d + 1) lo = d + 1;
        while (now() < t_end) {
            int base = bestN ? bestN : lo - 1;
            if (base >= Nmax) break;
            int N = base + 1 + rndint(N_SPAN);
            if (N > Nmax) N = Nmax;
            if (N < lo) N = lo;
            enum_groups(N);
            if (NCAND <= 0) continue;
            int ok = 0;
            for (int g = 0; g < GROUP_TRIES && !ok && now() < t_end; g++) {
                Grp G = CAND[rndint(NCAND)];
                setup_group(G);
                int gv[MAXD];
                gv[0] = 0;
                for (int t = 1; t < d; t++) {
                    do { gv[t] = rndint(N); } while (used_in(gv, t, gv[t]));
                }
                if (climb(gv, CLIMB_STEPS) == 0) {
                    ok = 1;
                    bestN = N;
                    bestm = G.m;
                    bestk = G.k;
                    bestr = G.r;
                    memcpy(bestgv, gv, sizeof(int) * (size_t)d);
                }
            }
        }
    }

    if (bestN > 0) {
        printf("%d %d %d %d\n", bestN, bestm, bestk, bestr);
        for (int t = 0; t < d; t++) printf("%d ", bestgv[t]);
        printf("\n");
    } else {
        printf("0 0 0 0\n");
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
            try:
                out.append(_gq_w(q))
            except Exception:
                pass
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib.moore_bound(d, D)
    if d > 16 or D < 2 or best[0] >= moore:
        return best

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best

    nmax = min(moore // 2, 2048)
    nstart = best[0] // 2 + 1
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), nstart, nmax],
                         timeout=budget + 5.0)
        toks = [int(x) for x in text.split()]
        if len(toks) >= 4 + d and toks[0] > 0:
            order, m, k, r = toks[:4]
            gs = toks[4:4 + d]
            if m * k == order and len(set(gs)) == d:
                _, mul, _ = lib.semidirect_group(m, k, r)
                n, edges = lib.group_lift(2, [(0, 1, g) for g in gs], order, mul)
                if n > best[0] and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
    except Exception:
        pass
    return best
