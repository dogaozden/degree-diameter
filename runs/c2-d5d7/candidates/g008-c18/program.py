"""Bi-Cayley group-lift search for the weakest cases (d = 5, D = 7 is the target).

Construction: for a group G of order N, take K base vertices per side (K = 1 or 2). Vertices are
A_{i,x} and B_{j,y} for x, y in G. A dart (i, j, g) joins A_{i,x} to B_{j,x*g}. Row i has d darts,
and the B-side degree is also d.

New in this version: the K = 2 shape. The 2x2 multiplicity matrix [[x, d-x], [d-x, x]] gives a
2-base-vertex-per-side lift of order 4N, with 2d voltages to tune, instead of d. Left multiplication
by G is an automorphism that is transitive on each of the four base classes, so the diameter check
needs four BFS runs, from A_{0,e}, A_{1,e}, B_{0,e} and B_{1,e}. K = 1 is the older bi-Cayley case.

The C engine hill-climbs the voltages on a random (K, N, G) sample. Each sample gets several
annealing runs from fresh voltages, and K = 2 is tried with probability 0.6 when it is feasible.
Orders are compared globally, so both shapes compete for the same improvement. G is a semidirect
product Z_m x|_r Z_k. The start graph (the H(q) hexagon incidence graph, or a smaller algebraic
graph) is the fallback, and the start graph is returned if nothing beats it.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-base bi-Cayley lift search over semidirect groups Z_m x|_r Z_k.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0".
 * stdout:  the best valid graph found (lift if it beats the start, else the start).
 *
 * Shape K in {1, 2} base vertices per side. Vertices: A_{i,x} = i*N + x, B_{j,y} = K*N + j*N + y.
 * Dart t = i*DEG + s goes from A_i to B_{DJ[t]} with voltage DG[t]: A_{i,x} ~ B_{j, x*g}.
 * Row i has DEG darts; each B_j receives DEG darts. For K = 2, DJ follows [[x, DEG-x], [DEG-x, x]].
 * Darts from the same row to the same target need distinct voltages (simple graph).
 * Left multiplication by G is transitive on each base class, so BFS from A_{i,e} and B_{j,e} for
 * all i, j < K decides diameter <= DIAM.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2800
#define MAXDEG 16
#define MAXT 32
#define MAXE 100000
#define MAXCAND 512
#define STEPS 8000
#define SPAN 40
#define RESTARTS 4
#define PK2 0.6

typedef struct { int m, k, r; } Grp;

static int DEG, DIAM;
static int KK = 1;
static int NN;
static double t_end;
static int *MTAB = NULL;
static int INVT[MAXN];
static int RP[MAXN];

static int DJ[MAXT], DG[MAXT], IN_[MAXT];

static int dist_[4 * MAXN], seen_[4 * MAXN], q_[4 * MAXN];
static int stamp_ = 0;

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
    if (DIAM <= 0 || DEG <= 0) return 1;
    if (DEG == 1) return 2;
    if (DEG == 2) return 2L * DIAM;
    long s = 0, p = 1;
    for (int i = 0; i < DIAM; i++) {
        s += p;
        p *= (DEG - 1);
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

static void setup_group(int N, Grp G) {
    NN = N;
    int m = G.m, k = G.k;
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * G.r % m);
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

/* Row i: darts s < DEG. K = 1: all to B_0. K = 2: [[x, DEG-x], [DEG-x, x]]. */
static void set_shape(int K, int x) {
    KK = K;
    if (K == 1) {
        for (int s = 0; s < DEG; s++) DJ[s] = 0;
        return;
    }
    for (int s = 0; s < DEG; s++) DJ[s] = (s < x) ? 0 : 1;
    for (int s = 0; s < DEG; s++) DJ[DEG + s] = (s < DEG - x) ? 0 : 1;
}

/* True if dart t's voltage v clashes with an earlier-indexed (u < upto) dart in the same row and cell. */
static int conflict(int t, int v, int upto) {
    int i = t / DEG;
    for (int s = 0; s < DEG; s++) {
        int u = i * DEG + s;
        if (u != t && u < upto && DJ[u] == DJ[t] && DG[u] == v) return 1;
    }
    return 0;
}

static void init_voltages(int N) {
    int T = KK * DEG;
    DG[0] = 0;
    for (int t = 1; t < T; t++) {
        int v;
        do { v = rndint(N); } while (conflict(t, v, t));
        DG[t] = v;
    }
}

/* Number of (source, vertex) pairs at distance > DIAM, sources A_{i,e} and B_{j,e}. */
static long eval_bad(void) {
    const int N = NN, K = KK, NK = K * N, V = 2 * NK, T = K * DEG;
    int cntj[2] = {0, 0};
    int gi[MAXT];
    for (int t = 0; t < T; t++) {
        int j = DJ[t];
        IN_[j * DEG + cntj[j]++] = t;
        gi[t] = INVT[DG[t]];
    }
    long total = 0;
    for (int src_idx = 0; src_idx < 2 * K; src_idx++) {
        int src = (src_idx < K) ? src_idx * N : NK + (src_idx - K) * N;
        int head = 0, tail = 0;
        stamp_++;
        seen_[src] = stamp_;
        dist_[src] = 0;
        q_[tail++] = src;
        while (head < tail) {
            int v = q_[head++];
            int dv = dist_[v];
            if (dv >= DIAM) continue;
            if (v < NK) {
                int i = v / N, x = v - i * N;
                const int *row = MTAB + (size_t)x * N;
                for (int s = 0; s < DEG; s++) {
                    int t = i * DEG + s;
                    int u = NK + DJ[t] * N + row[DG[t]];
                    if (seen_[u] != stamp_) {
                        seen_[u] = stamp_;
                        dist_[u] = dv + 1;
                        q_[tail++] = u;
                    }
                }
            } else {
                int w = v - NK;
                int j = w / N, y = w - j * N;
                const int *row = MTAB + (size_t)y * N;
                for (int s = 0; s < DEG; s++) {
                    int t = IN_[j * DEG + s];
                    int u = (t / DEG) * N + row[gi[t]];
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

/* Annealed voltage hill-climb; the dart 0 voltage (identity) is kept fixed. */
static long climb(double until, double T0) {
    int T = KK * DEG;
    long bad = eval_bad();
    double Temp = T0;
    for (long s = 0; s < STEPS && bad > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        int t = 1 + rndint(T - 1);
        int old = DG[t], nv;
        do { nv = rndint(NN); } while (conflict(t, nv, T));
        DG[t] = nv;
        long nb = eval_bad();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / Temp)) bad = nb;
        else DG[t] = old;
        Temp *= 0.9995;
        if (Temp < 0.2) Temp = 0.2;
    }
    return bad;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
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

    static int OU[MAXE], OV[MAXE];
    int ne = 0, found = 0;
    long bestV = sn;

    if (DEG >= 3 && DEG <= MAXDEG && DIAM >= 2) {
        MTAB = malloc(sizeof(int) * (size_t)MAXN * MAXN);
    }
    if (MTAB) {
        long moore = moore_bound();
        static Grp cand[MAXCAND];
        while (now() < t_end) {
            long Nlo_k[3] = {0, 0, 0}, Nmax_k[3] = {0, 0, 0};
            int nk = 0, Kopt[2] = {1, 2};
            for (int K = 1; K <= 2; K++) {
                long lo = bestV / (2L * K) + 1;
                if (lo < DEG + 1) lo = DEG + 1;
                long hi = moore / (2L * K);
                if (hi > MAXN) hi = MAXN;
                Nlo_k[K] = lo;
                Nmax_k[K] = hi;
                if (lo <= hi) Kopt[nk++] = K;
            }
            if (nk == 0) break;
            int K = (nk == 2 && rnd01() < PK2) ? 2 : Kopt[0];

            long lo = Nlo_k[K], hi = Nmax_k[K];
            long span = hi - lo + 1;
            if (span > SPAN) span = SPAN;
            int N = (int)(lo + rndint((int)span));
            int cnt = enum_groups(N, cand);
            if (cnt <= 0) continue;
            Grp G = pick_group(cand, cnt);
            setup_group(N, G);

            long bad = 1;
            for (int rs = 0; rs < RESTARTS && bad > 0 && now() < t_end; rs++) {
                int x = (K == 2) ? 1 + rndint(DEG - 1) : 0;
                set_shape(K, x);
                init_voltages(N);
                bad = climb(t_end, rs == 0 ? 2.0 : 1.0);
            }
            if (bad == 0) {
                found = 1;
                bestV = 2L * K * N;
                ne = 0;
                int NK = K * N;
                for (int i = 0; i < K; i++)
                    for (int x = 0; x < N; x++)
                        for (int s = 0; s < DEG; s++) {
                            int t = i * DEG + s;
                            OU[ne] = i * N + x;
                            OV[ne] = NK + DJ[t] * N + MTAB[(size_t)x * N + DG[t]];
                            ne++;
                        }
            }
        }
        free(MTAB);
        MTAB = NULL;
    }

    if (found) {
        printf("%ld %d\n", bestV, ne);
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
