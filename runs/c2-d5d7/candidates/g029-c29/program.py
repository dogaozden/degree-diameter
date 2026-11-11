"""d=5, D=7 target, new construction: non-abelian bi-Cayley lifts searched by tabu search.

The parent annealed voltage sets over groups Z_m x| Z_k. This version changes the search in
two ways.

1. The C engine uses tabu search with sampled best-improvement moves. Each step samples
   SAMPLE single-voltage moves, takes the best non-tabu one (aspiration allows a tabu move
   that beats the best so far), and bans the replaced voltage for a short tenure. Restarts
   come after a stall, with a fresh group and fresh voltages.
2. The order N is drawn from a window above the incumbent, biased low. Each order gets a
   time slice that cycles through random admissible groups. Non-abelian groups are preferred,
   with a fallback to any group when none is admissible.

Starts: the split Cayley hexagon H(q), q = d-1 in {2, 4}, for D >= 6 (order 2730 for d=5),
the projective plane for D >= 3, and the Araujo-Pardo--Lopez graph for D = 3. The best valid
start is the fallback. The C engine receives the start order as an argument, so it does not
read the graph from stdin. Every returned graph is re-checked with lib.is_valid.

Whether this beats the record 3110 is not guaranteed. The bi-Cayley family is the same one
the parent uses, so the gain depends on the search.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Tabu search over bi-Cayley voltage sets for Z_m x|_r Z_k.
 * Vertices: A_x = x, B_y = N + y (x, y in G). Edges A_x -- B_{x*g_t}, t = 0..d-1, g_0 = e,
 * g_t distinct. Left multiplication is transitive on each side, so BFS from A_e and B_e
 * decides diameter <= D.
 * Usage:  prog d D seed time_limit n_start
 * stdout: "n m" then the edges of the best graph found, or "0 0".
 */

#define MAXNN 3200
#define MAXD 16
#define SAMPLE 120
#define TENURE 10
#define STALL 400
#define SPAN 120
#define SLICE 3.0

static int d, D;
static double t_deadline;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
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

/* Current group: element x = a*GK + b, (a,b)(c,e) = (a + r^b c mod GM, b + e mod GK). */
static int GM, GK, GR, NN;
static int *MT;               /* MT[x*NN + y] = x*y */
static int INVT[MAXNN];
static int XA[MAXNN], XB[MAXNN];
static int rpw[MAXNN];

/* Uniform random admissible semidirect product of order N (optionally non-abelian). */
static int sample_group(int N, int *mo, int *ko, int *ro, int nonab) {
    long count = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (nonab && (m == 1 || k == 1 || r == 1)) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (!count) return 0;
    *mo = bm; *ko = bk; *ro = br;
    return 1;
}

static void setup_group(int N, int m, int k, int r) {
    GM = m; GK = k; GR = r; NN = N;
    rpw[0] = 1 % m;
    for (int b = 1; b < k; b++) rpw[b] = (int)((long)rpw[b - 1] * r % m);
    for (int x = 0; x < N; x++) { XA[x] = x / k; XB[x] = x % k; }
    for (int x = 0; x < N; x++) {
        int a = XA[x], b = XB[x];
        int *row = MT + (size_t)x * N;
        for (int y = 0; y < N; y++) {
            int c = XA[y], e = XB[y];
            row[y] = (int)(((long)a + (long)rpw[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++) {
        const int *row = MT + (size_t)x * N;
        for (int y = 0; y < N; y++)
            if (row[y] == 0) { INVT[x] = y; break; }
    }
}

static int gv[MAXD], gi[MAXD];
static long tabu_until[MAXD][MAXNN];
static int stv[2 * MAXNN], dv_[2 * MAXNN], qv[2 * MAXNN];
static int stamp_ctr = 0;

static int in_list(const int *vals, int cnt, int v) {
    for (int i = 0; i < cnt; i++)
        if (vals[i] == v) return 1;
    return 0;
}

/* Number of (source, vertex) pairs at distance > D, sources A_e and B_e. */
static long eval_bad(void) {
    int N = NN, V = 2 * N;
    for (int t = 0; t < d; t++) gi[t] = INVT[gv[t]];
    long total = 0;
    for (int s = 0; s < 2; s++) {
        int src = s ? N : 0;
        int h = 0, tl = 0;
        stamp_ctr++;
        stv[src] = stamp_ctr;
        dv_[src] = 0;
        qv[tl++] = src;
        while (h < tl) {
            int v = qv[h++];
            int dv = dv_[v];
            if (dv >= D) continue;
            if (v < N) {
                const int *row = MT + (size_t)v * N;
                for (int t = 0; t < d; t++) {
                    int u = N + row[gv[t]];
                    if (stv[u] != stamp_ctr) { stv[u] = stamp_ctr; dv_[u] = dv + 1; qv[tl++] = u; }
                }
            } else {
                const int *row = MT + (size_t)(v - N) * N;
                for (int t = 0; t < d; t++) {
                    int u = row[gi[t]];
                    if (stv[u] != stamp_ctr) { stv[u] = stamp_ctr; dv_[u] = dv + 1; qv[tl++] = u; }
                }
            }
        }
        total += V - tl;
    }
    return total;
}

/* Tabu search over voltages of the current group. Returns 1 and copies the voltages to
 * found when the lift has diameter <= D. */
static int search_group(double until, int *found) {
    int N = NN;
    memset(tabu_until, 0, sizeof(tabu_until));
    gv[0] = 0;
    for (int t = 1; t < d; t++) {
        int v;
        do { v = rndint(N); } while (in_list(gv, t, v));
        gv[t] = v;
    }
    long cur = eval_bad();
    long best = cur;
    int stall = 0;
    for (long it = 1; now() < until; it++) {
        if (cur == 0) {
            memcpy(found, gv, sizeof(int) * d);
            return 1;
        }
        if (stall > STALL) return 0;
        int bt = -1, bv = -1;
        long bobj = 0;
        for (int s = 0; s < SAMPLE; s++) {
            int t = 1 + rndint(d - 1), nv;
            do { nv = rndint(N); } while (in_list(gv, d, nv));
            int old = gv[t];
            gv[t] = nv;
            long obj = eval_bad();
            gv[t] = old;
            if (tabu_until[t][nv] > it && obj >= best) continue;
            if (bt < 0 || obj < bobj || (obj == bobj && rndint(2))) {
                bt = t; bv = nv; bobj = obj;
            }
        }
        if (bt < 0) { stall++; continue; }
        tabu_until[bt][gv[bt]] = it + TENURE + rndint(TENURE);
        gv[bt] = bv;
        cur = bobj;
        if (cur < best) { best = cur; stall = 0; }
        else stall++;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit n_start\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long nstart = atol(argv[5]);
    double t0 = now();
    t_deadline = t0 + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    MT = malloc(sizeof(int) * (size_t)MAXNN * MAXNN);
    if (!MT) { printf("0 0\n"); return 0; }

    long moore = moore_bound();
    long Nmax_l = moore / 2;
    if (Nmax_l > MAXNN) Nmax_l = MAXNN;
    int Nmax = (int)Nmax_l;
    long Nlo_l = nstart / 2 + 1;
    if (Nlo_l < d + 1) Nlo_l = d + 1;
    int Nlo = (int)Nlo_l;

    int bestN = 0, bm = 0, bk = 0, br = 0, bgv[MAXD], found[MAXD];
    while (now() < t_deadline && Nlo <= Nmax) {
        int span = Nmax - Nlo + 1;
        if (span > SPAN) span = SPAN;
        double u = rnd01();
        int N = Nlo + (int)(u * sqrt(u) * span);
        if (N > Nmax) N = Nmax;
        double slice_end = now() + SLICE;
        if (slice_end > t_deadline) slice_end = t_deadline;
        int ok = 0;
        while (!ok && now() < slice_end) {
            int m, k, r;
            int nonab = rndint(10) < 7;
            if (!sample_group(N, &m, &k, &r, nonab) && !sample_group(N, &m, &k, &r, 0)) break;
            setup_group(N, m, k, r);
            if (search_group(slice_end, found)) {
                ok = 1;
                bestN = N; bm = m; bk = k; br = r;
                memcpy(bgv, found, sizeof(int) * d);
            }
        }
        if (ok) Nlo = N + 1;
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    setup_group(bestN, bm, bk, br);
    printf("%d %d\n", 2 * bestN, bestN * d);
    for (int x = 0; x < bestN; x++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", x, bestN + MT[(size_t)x * bestN + bgv[t]]);
    return 0;
}
'''


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so valid for D = 6 and D = 7.
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
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 15 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         stdin_graph=None, timeout=budget + 8)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
