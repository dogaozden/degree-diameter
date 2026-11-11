"""Multi-base voltage-lift search over semidirect groups, for the weakest cases (d = 5, D = 7 is the target).

Construction: a base multigraph on K vertices per side (K in {1,2,3}), built from d random perfect
matchings between the sides, so every base vertex has degree d. Each dart t (from A_i to B_j) gets a
voltage g_t in a group G of order N, with G = Z_m x|_r Z_q. The lift has vertices (block, x), x in G,
and edges (A_i, x) -- (B_j, x*g_t). Darts sharing a base pair need distinct voltages, which keeps the
lift simple. Left multiplication by G is an automorphism that is transitive on each block, so the
diameter check needs only one BFS per block. The C engine simulated-anneals the voltages until every
pair is within distance D, and it keeps raising the order target. The start graph (the best algebraic
graph in Python) is the fallback. If no lift beats it, the fallback is returned.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-base voltage lift search over semidirect groups Z_m x|_r Z_q.
 * Usage:  prog d D seed time_limit start_n
 * Output: "V E" plus E edges of the best lift with V > start_n, or "0 0" if none was found.
 * Vertices: block b in [0, 2K) with b < K meaning A_b and b >= K meaning B_{b-K};
 *           vertex id = b * N + x, x in G.
 * Edges:    for each dart t = s*K + i (from A_i to B_{sigma_s(i)}) and each x:
 *           (A_i, x) -- (B_j, x * g_t), with j = sigma_s(i).
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1600
#define MAXK 3
#define MAXD 16
#define MAXE (MAXD * MAXK)
#define MAXV (2 * MAXK * MAXN)
#define MAXOUT (MAXE * MAXN)
#define MAXCAND 256
#define STEPS 5000
#define SPANK 24

typedef struct { int m, q, r; } Grp;

static int d, D, K, NN;
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

/* Groups Z_m x|_r Z_q with m*q = N. */
static int enum_groups(int N, Grp *out) {
    int cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int q = N / m;
        if (m == 1) {
            if (cnt < MAXCAND) { out[cnt].m = 1; out[cnt].q = q; out[cnt].r = 0; cnt++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, q, m) != 1 % m) continue;
            if (cnt < MAXCAND) { out[cnt].m = m; out[cnt].q = q; out[cnt].r = r; cnt++; }
        }
    }
    return cnt;
}

static int MT[MAXN * MAXN];
static int INVT[MAXN];
static int RP[MAXN];

static void setup_group(int N, Grp G) {
    NN = N;
    int m = G.m, q = G.q;
    RP[0] = 1 % m;
    for (int b = 1; b < q; b++) RP[b] = (int)((long)RP[b - 1] * G.r % m);
    for (int x = 0; x < N; x++) {
        int a = x / q, b = x % q;
        int *row = MT + (size_t)x * N;
        for (int y = 0; y < N; y++) {
            int c = y / q, e = y % q;
            row[y] = (int)((((long)a + (long)RP[b] * c) % m) * q + (b + e) % q);
        }
        int nb = (q - b) % q;
        int cinv = (int)((m - ((long)RP[nb] * a) % m) % m);
        INVT[x] = cinv * q + nb;
    }
}

/* Base multigraph: d random perfect matchings between K A-vertices and K B-vertices. */
static int sigma[MAXD][MAXK];
static int dA[MAXE], dB[MAXE], pairv[MAXE], gv[MAXE];
static int bl[MAXK][MAXD];

static void new_base(int k) {
    K = k;
    for (int s = 0; s < d; s++) {
        for (int i = 0; i < K; i++) sigma[s][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = sigma[s][i];
            sigma[s][i] = sigma[s][j];
            sigma[s][j] = tmp;
        }
    }
    for (int s = 0; s < d; s++)
        for (int i = 0; i < K; i++) {
            int t = s * K + i;
            dA[t] = i;
            dB[t] = sigma[s][i];
            pairv[t] = i * K + dB[t];
        }
    int cnt[MAXK];
    for (int j = 0; j < MAXK; j++) cnt[j] = 0;
    for (int t = 0; t < d * K; t++) {
        int j = dB[t];
        bl[j][cnt[j]++] = t;
    }
}

/* Darts with the same base pair need distinct voltages (else duplicate edges). */
static int volt_ok(int t, int val) {
    int nd = d * K;
    for (int u = 0; u < nd; u++)
        if (u != t && pairv[u] == pairv[t] && gv[u] == val) return 0;
    return 1;
}

static int init_volts(void) {
    int nd = d * K;
    for (int t = 0; t < nd; t++) gv[t] = -1;
    for (int t = 0; t < nd; t++) {
        int ok = 0;
        for (int tr = 0; tr < 2000 && !ok; tr++) {
            int c = rndint(NN);
            if (volt_ok(t, c)) { gv[t] = c; ok = 1; }
        }
        if (!ok) return 0;
    }
    return 1;
}

static int seen_[MAXV], dist_[MAXV], Q_[MAXV];
static int stamp_ = 0;

/* Total number of (source, vertex) pairs at distance > D, over one source per block. */
static long eval_bad(void) {
    int N = NN, V = 2 * K * N;
    long bad = 0;
    for (int src = 0; src < 2 * K; src++) {
        int s0 = src * N;
        int head = 0, tail = 0;
        stamp_++;
        seen_[s0] = stamp_;
        dist_[s0] = 0;
        Q_[tail++] = s0;
        while (head < tail) {
            int v = Q_[head++];
            int dv = dist_[v];
            if (dv >= D) continue;
            int b = v / N;
            int x = v - b * N;
            const int *row = MT + (size_t)x * N;
            if (b < K) {
                for (int s = 0; s < d; s++) {
                    int t = s * K + b;
                    int u = (K + dB[t]) * N + row[gv[t]];
                    if (seen_[u] != stamp_) {
                        seen_[u] = stamp_;
                        dist_[u] = dv + 1;
                        Q_[tail++] = u;
                    }
                }
            } else {
                int j = b - K;
                for (int c = 0; c < d; c++) {
                    int t = bl[j][c];
                    int u = dA[t] * N + row[INVT[gv[t]]];
                    if (seen_[u] != stamp_) {
                        seen_[u] = stamp_;
                        dist_[u] = dv + 1;
                        Q_[tail++] = u;
                    }
                }
            }
        }
        bad += V - tail;
    }
    return bad;
}

static long climb(void) {
    int nd = d * K;
    long bad = eval_bad();
    double T = 2.0;
    for (long s = 0; s < STEPS && bad > 0; s++) {
        if ((s & 63) == 0 && now() > t_end) break;
        int t = rndint(nd);
        int old = gv[t], nv = -1;
        for (int tr = 0; tr < 64; tr++) {
            int c = rndint(NN);
            if (c != old && volt_ok(t, c)) { nv = c; break; }
        }
        if (nv < 0) continue;
        gv[t] = nv;
        long nb = eval_bad();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else gv[t] = old;
        T *= 0.9993;
        if (T < 0.3) T = 0.3;
    }
    return bad;
}

static int OU[MAXOUT], OV[MAXOUT];

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit start_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long start_n = atol(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    long moore = moore_bound();
    long best_order = start_n;
    int found = 0, bestV = 0, bestE = 0;
    static Grp cand[MAXCAND];

    while (now() < t_end) {
        long target = best_order + 1;
        if (target > moore) break;
        int k = 1 + rndint(MAXK);
        long Nmin = (target + 2L * k - 1) / (2L * k);
        if (Nmin < d) Nmin = d;
        if (Nmin > MAXN) continue;
        long N = Nmin + rndint(SPANK);
        if (N > MAXN || 2L * k * N > moore) N = Nmin;
        if (N > MAXN || 2L * k * N > moore) continue;

        int cnt = enum_groups((int)N, cand);
        if (cnt <= 0) continue;
        Grp G = cand[rndint(cnt)];
        setup_group((int)N, G);
        new_base(k);
        if (!init_volts()) continue;

        long bad = climb();
        if (bad == 0) {
            int nd = d * K;
            int ne = 0;
            for (int t = 0; t < nd; t++)
                for (int x = 0; x < NN; x++) {
                    OU[ne] = dA[t] * NN + x;
                    OV[ne] = (K + dB[t]) * NN + MT[(size_t)x * NN + gv[t]];
                    ne++;
                }
            found = 1;
            bestV = 2 * K * NN;
            bestE = ne;
            best_order = bestV;
        }
    }

    if (found) {
        printf("%d %d\n", bestV, bestE);
        for (int i = 0; i < bestE; i++) printf("%d %d\n", OU[i], OV[i]);
    } else {
        printf("0 0\n");
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
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 3), best[0]],
                         timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
