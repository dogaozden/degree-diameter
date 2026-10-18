"""Multi-orbit bi-Cayley lift search for the weakest cases (d = 5, D = 7 is the target).

New construction: a side has K base orbits (K = 1, 2 or 3). Each orbit is a copy of a group G of
order N, with a_{i,x} = i*N + x and b_{j,x} = K*N + j*N + x. The base multigraph is the sum of d
random permutation matrices on K points, so every orbit has degree d. Dart (i, t) joins a_{i,x} to
b_{j,x*g}, where j = sigma_t(i) and g is a voltage. Darts from the same orbit to the same target
get distinct voltages, so the graph is simple. Left multiplication by G preserves each orbit, so
diameter <= D only needs BFS from one identity vertex per orbit (2K BFS runs).

G is a semidirect product Z_m x|_r Z_k. Voltages are hill-climbed with annealing to minimise the
number of pairs at distance > D. K = 1 reproduces the single-orbit lift; K = 2 and 3 are new.

The start graph (hexagon, projective plane, Araujo-Lopez, GQ, or K_{d,d}) is the fallback, and
build() only returns graphs that pass lib.is_valid.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-orbit bi-Cayley lift search over semidirect groups Z_m x|_r Z_k.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0".
 * stdout:  the best valid graph found (a lift if it beats the start, else the start).
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXH 2048
#define MAXK 3
#define MAXD 16
#define MAXV (2 * MAXK * MAXH)
#define MAXE 200000
#define MAXCAND 4096
#define STEPS 5000
#define SPAN 3

typedef struct { int m, k, r; } Grp;

static int d, D, K;
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
        int a = x / k, b = x % k;
        int nb = (k - b) % k;
        long ap = ((long)m - ((long)RP[nb] * a) % m) % m;
        INVT[x] = (int)(ap * k + nb);
    }
}

/* Base structure: dart (i, t) goes from a-orbit i to b-orbit PA[i][t] with voltage PG[i][t]. */
static int PA[MAXK][MAXD], PG[MAXK][MAXD];
static int BIi[MAXK][MAXD], BIg[MAXK][MAXD];
static int distv[MAXV], seenv[MAXV], qv[MAXV];
static int stamp_ = 0;

/* Number of (source, vertex) pairs at distance > D over the 2K orbit identities. */
static long eval_bad(void) {
    int N = NN, V = 2 * K * N, BO = K * N;
    int cnt[MAXK];
    for (int j = 0; j < K; j++) cnt[j] = 0;
    for (int i = 0; i < K; i++)
        for (int t = 0; t < d; t++) {
            int j = PA[i][t];
            BIi[j][cnt[j]] = i;
            BIg[j][cnt[j]] = INVT[PG[i][t]];
            cnt[j]++;
        }
    long total = 0;
    for (int s = 0; s < 2 * K; s++) {
        int src = (s < K) ? s * N : BO + (s - K) * N;
        int head = 0, tail = 0;
        stamp_++;
        seenv[src] = stamp_;
        distv[src] = 0;
        qv[tail++] = src;
        while (head < tail) {
            int v = qv[head++];
            int dv = distv[v];
            if (dv >= D) continue;
            if (v < BO) {
                int i = v / N, x = v % N;
                const int *row = MTAB + (size_t)x * N;
                for (int t = 0; t < d; t++) {
                    int j = PA[i][t];
                    int u = BO + j * N + row[PG[i][t]];
                    if (seenv[u] != stamp_) {
                        seenv[u] = stamp_;
                        distv[u] = dv + 1;
                        qv[tail++] = u;
                    }
                }
            } else {
                int w = v - BO;
                int j = w / N, y = w % N;
                const int *row = MTAB + (size_t)y * N;
                for (int c = 0; c < d; c++) {
                    int i = BIi[j][c];
                    int u = i * N + row[BIg[j][c]];
                    if (seenv[u] != stamp_) {
                        seenv[u] = stamp_;
                        distv[u] = dv + 1;
                        qv[tail++] = u;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

/* Distinct voltages among darts from the same orbit to the same target (full check). */
static int volt_ok(int i, int t, int v) {
    for (int s = 0; s < d; s++)
        if (s != t && PA[i][s] == PA[i][t] && PG[i][s] == v) return 0;
    return 1;
}

/* Same check during initialisation: only darts s < t are already placed. */
static int volt_ok_init(int i, int t, int v) {
    for (int s = 0; s < t; s++)
        if (PA[i][s] == PA[i][t] && PG[i][s] == v) return 0;
    return 1;
}

static void rand_perm(int *p, int n) {
    for (int i = 0; i < n; i++) p[i] = i;
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
    }
}

/* Annealed voltage hill-climb on the current base structure. */
static long climb(void) {
    long bad = eval_bad();
    double T = 6.0;
    for (long s = 0; s < STEPS && bad > 0; s++) {
        if ((s & 63) == 0 && now() > t_end) break;
        int i = rndint(K), t = rndint(d);
        int old = PG[i][t];
        int nv = -1;
        for (int tries = 0; tries < 50; tries++) {
            int v = rndint(NN);
            if (v != old && volt_ok(i, t, v)) { nv = v; break; }
        }
        if (nv < 0) continue;
        PG[i][t] = nv;
        long nb = eval_bad();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else PG[i][t] = old;
        T *= 0.9985;
        if (T < 0.5) T = 0.5;
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
    t_end = t0 + limit * 0.95;
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

    int found = 0, BK = 0, BN = 0;
    Grp BG = {1, 1, 0};
    static int BPA[MAXK][MAXD], BPG[MAXK][MAXD];
    long best_total = sn;

    if (d >= 3 && d <= MAXD && D >= 2) {
        long moore = moore_bound();
        int spins = 0;
        static Grp cand[MAXCAND];
        while (now() < t_end && best_total < moore && spins < 20000) {
            int r = rndint(100);
            int kk = (r < 50) ? 2 : (r < 80 ? 1 : 3);
            long Nlo = best_total / (2L * kk) + 1;
            if (Nlo < d) Nlo = d;
            long Nhi = moore / (2L * kk);
            if (Nhi > MAXH) Nhi = MAXH;
            if (Nlo > Nhi) { spins++; continue; }
            long span = Nhi - Nlo + 1;
            if (span > SPAN) span = SPAN;
            int N = (int)(Nlo + rndint((int)span));
            int cnt = enum_groups(N, cand);
            if (cnt <= 0) { spins++; continue; }
            Grp G = pick_group(cand, cnt);
            setup_group(N, G);
            K = kk;

            int sig[MAXK];
            for (int t = 0; t < d; t++) {
                rand_perm(sig, K);
                for (int i = 0; i < K; i++) PA[i][t] = sig[i];
            }
            int ok = 1;
            for (int i = 0; i < K && ok; i++)
                for (int t = 0; t < d && ok; t++) {
                    int placed = 0;
                    for (int tr = 0; tr < 4000 && !placed; tr++) {
                        int v = rndint(N);
                        PG[i][t] = v;
                        if (volt_ok_init(i, t, v)) placed = 1;
                    }
                    if (!placed) ok = 0;
                }
            if (!ok) { spins++; continue; }
            spins = 0;

            long bad = climb();
            if (bad == 0) {
                found = 1;
                best_total = 2L * K * N;
                BK = K;
                BN = N;
                BG = G;
                for (int i = 0; i < K; i++)
                    for (int t = 0; t < d; t++) {
                        BPA[i][t] = PA[i][t];
                        BPG[i][t] = PG[i][t];
                    }
            }
        }
    }

    if (found) {
        setup_group(BN, BG);
        int n = 2 * BK * BN;
        long ne = (long)BK * d * BN;
        printf("%d %ld\n", n, ne);
        for (int i = 0; i < BK; i++)
            for (int x = 0; x < BN; x++)
                for (int t = 0; t < d; t++) {
                    int u = i * BN + x;
                    int v = BK * BN + BPA[i][t] * BN + MTAB[(size_t)x * BN + BPG[i][t]];
                    printf("%d %d\n", u, v);
                }
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    try:
        starts = known_starts(d, D)
    except Exception:
        starts = []
    for cand in starts:
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 16 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.80 * time_limit - 2.0 - (time.monotonic() - t0)
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
