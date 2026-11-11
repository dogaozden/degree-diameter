"""Multi-base bi-Cayley lift search for the weakest case (d = 5, D = 7 is the target).

Construction: a group G of order N (semidirect Z_m x| Z_k) and K base vertices on each side.
Vertices are A(i,x) and B(j,y), with i, j in 0..K-1 and x, y in G. Each A-base vertex i has d darts
(j, g), which join A(i,x) to B(j, x*g). Each B-base vertex receives exactly d darts, so the graph is
d-regular and bipartite. Left multiplication by G is an automorphism, transitive on each side's
orbits, so diameter <= D needs BFS only from A(i,e) and B(j,e), 2K sources in total.

K = 1 is the previous single-orbit lift. K = 2..5 is a new family: total order 2KN, and the orders
the record needs (e.g. 3110 = 10 * 311) are reachable with several orbits. The C engine hill-climbs
dart targets and voltages at random (K, N, G) choices. The start graph (hexagon H(q) or another
algebraic graph) is the fallback, and Python validates every result with lib.is_valid.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-base bi-Cayley lift search over semidirect groups Z_m x|_r Z_k.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0".
 * stdout:  the best valid graph found (a lift if it beats the start, else the start).
 *
 * Vertices: A(i,x) = i*N + x, B(j,y) = K*N + j*N + y, with K bases per side and |G| = N.
 * Darts:    for each A-base i, d darts (DJ[i][t], DG[i][t]) joining A(i,x) to B(DJ, x*DG).
 *           Each B-base j receives exactly d darts (balance kept by swaps). Within a row, the
 *           pairs (j, g) are distinct, so the graph is simple and d-regular.
 * Diameter: left translation by G is an automorphism, so BFS from A(i,e) and B(j,e) for all
 *           bases suffices.
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
#define MAXK 5
#define MAXV (2 * MAXK * MAXH)
#define MAXE 40000
#define MAXCAND 512
#define STEPS 6000
#define SPAN 30
#define RESTARTS 4

typedef struct { int m, k, r; } Grp;

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
static int MT[MAXH * MAXH];
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
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            MT[x * N + y] = (int)((((long)a + (long)RP[b] * c) % m) * k + (b + e) % k);
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INVT[x] = y; break; }
}

/* Current lift state. */
static int K;
static int KN;
static int DJ[MAXK][MAXD], DG[MAXK][MAXD];
static int RI[MAXK][MAXD], RG[MAXK][MAXD];   /* reverse darts per B-base */

static int dist_[MAXV], seen_[MAXV], q_[MAXV];
static int stamp_ = 0;

static void build_reverse(void) {
    int cnt[MAXK];
    memset(cnt, 0, sizeof cnt);
    for (int i = 0; i < K; i++)
        for (int t = 0; t < d; t++) {
            int j = DJ[i][t];
            RI[j][cnt[j]] = i;
            RG[j][cnt[j]] = INVT[DG[i][t]];
            cnt[j]++;
        }
}

/* Number of (source, vertex) pairs at distance > D over all 2K base sources. */
static long eval_bad(void) {
    build_reverse();
    int V = 2 * KN;
    long total = 0;
    for (int s = 0; s < 2 * K; s++) {
        int src = (s < K) ? s * NN : KN + (s - K) * NN;
        int head = 0, tail = 0;
        stamp_++;
        seen_[src] = stamp_;
        dist_[src] = 0;
        q_[tail++] = src;
        while (head < tail) {
            int v = q_[head++];
            int dv = dist_[v];
            if (dv >= D) continue;
            if (v < KN) {
                int i = v / NN, x = v - i * NN;
                for (int t = 0; t < d; t++) {
                    int u = KN + DJ[i][t] * NN + MT[x * NN + DG[i][t]];
                    if (seen_[u] != stamp_) {
                        seen_[u] = stamp_;
                        dist_[u] = dv + 1;
                        q_[tail++] = u;
                    }
                }
            } else {
                int w = v - KN, j = w / NN, y = w - j * NN;
                for (int s2 = 0; s2 < d; s2++) {
                    int u = RI[j][s2] * NN + MT[y * NN + RG[j][s2]];
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

/* Row i has distinct (j, g) pairs. */
static int row_ok(int i) {
    for (int t = 0; t < d; t++)
        for (int s2 = 0; s2 < t; s2++)
            if (DJ[i][t] == DJ[i][s2] && DG[i][t] == DG[i][s2]) return 0;
    return 1;
}

/* Fresh random darts: balanced targets, random voltages, distinct pairs per row. */
static void init_darts(void) {
    int tot = K * d;
    static int arr[MAXK * MAXD];
    for (int idx = 0; idx < tot; idx++) arr[idx] = idx % K;
    for (int idx = tot - 1; idx > 0; idx--) {
        int r = rndint(idx + 1);
        int tmp = arr[idx]; arr[idx] = arr[r]; arr[r] = tmp;
    }
    for (int i = 0; i < K; i++)
        for (int t = 0; t < d; t++) {
            DJ[i][t] = arr[i * d + t];
            int ok;
            do {
                DG[i][t] = rndint(NN);
                ok = 1;
                for (int s2 = 0; s2 < t; s2++)
                    if (DJ[i][s2] == DJ[i][t] && DG[i][s2] == DG[i][t]) { ok = 0; break; }
            } while (!ok);
        }
}

/* Annealed hill-climb over dart voltages and B-target swaps. */
static long climb(double until, double T0) {
    static int SJ[MAXK][MAXD], SG[MAXK][MAXD];
    long bad = eval_bad();
    double T = T0;
    for (long s = 0; s < STEPS && bad > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        memcpy(SJ, DJ, sizeof DJ);
        memcpy(SG, DG, sizeof DG);
        if (rnd01() < 0.5) {
            int i = rndint(K), t = rndint(d);
            DG[i][t] = rndint(NN);
            if (!row_ok(i)) { memcpy(DJ, SJ, sizeof DJ); memcpy(DG, SG, sizeof DG); continue; }
        } else {
            int i1 = rndint(K), t1 = rndint(d), i2 = rndint(K), t2 = rndint(d);
            if (DJ[i1][t1] == DJ[i2][t2]) continue;
            int tmp = DJ[i1][t1]; DJ[i1][t1] = DJ[i2][t2]; DJ[i2][t2] = tmp;
            if (!row_ok(i1) || (i2 != i1 && !row_ok(i2))) {
                memcpy(DJ, SJ, sizeof DJ); memcpy(DG, SG, sizeof DG); continue;
            }
        }
        long nb = eval_bad();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            memcpy(DJ, SJ, sizeof DJ);
            memcpy(DG, SG, sizeof DG);
        }
        T *= 0.9995;
        if (T < 0.2) T = 0.2;
    }
    return bad;
}

/* Could a K-base lift on the target side still beat best_total? */
static int range_ok(int k, long best_total, long moore) {
    long lo = best_total / (2L * k) + 1;
    if (lo < d + 1) lo = d + 1;
    long hi = moore / (2L * k);
    if (hi > MAXH) hi = MAXH;
    return lo <= hi;
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

    long best_total = sn;
    int found = 0;
    static Grp cand[MAXCAND];
    static int bestDJ[MAXK][MAXD], bestDG[MAXK][MAXD];
    int bestK = 0, bestN = 0;
    Grp bestG = {1, 1, 0};

    if (d >= 3 && d <= MAXD && D >= 2) {
        long MOORE = moore_bound();
        while (now() < t_end && best_total < MOORE) {
            int anyf = 0;
            for (int kk = 1; kk <= MAXK; kk++)
                if (range_ok(kk, best_total, MOORE)) anyf = 1;
            if (!anyf) break;

            int Kc = 1 + rndint(MAXK);
            if (!range_ok(Kc, best_total, MOORE)) continue;
            long Nlo = best_total / (2L * Kc) + 1;
            if (Nlo < d + 1) Nlo = d + 1;
            long Nmax = MOORE / (2L * Kc);
            if (Nmax > MAXH) Nmax = MAXH;
            int span = (int)(Nmax - Nlo + 1);
            if (span > SPAN) span = SPAN;
            int N = (int)Nlo + rndint(span);

            int cnt = enum_groups(N, cand);
            if (cnt <= 0) continue;
            Grp G = pick_group(cand, cnt);
            setup_group(N, G);
            K = Kc;
            KN = K * N;

            long bad = 1;
            for (int rs = 0; rs < RESTARTS && bad > 0 && now() < t_end; rs++) {
                init_darts();
                bad = climb(t_end, rs == 0 ? 2.0 : 1.0);
            }
            if (bad == 0) {
                found = 1;
                best_total = 2L * K * N;
                bestK = K;
                bestN = N;
                bestG = G;
                memcpy(bestDJ, DJ, sizeof DJ);
                memcpy(bestDG, DG, sizeof DG);
            }
        }
    }

    if (found) {
        setup_group(bestN, bestG);
        int V = 2 * bestK * bestN;
        int E = bestK * bestN * d;
        int KB = bestK * bestN;
        printf("%d %d\n", V, E);
        for (int i = 0; i < bestK; i++)
            for (int x = 0; x < bestN; x++)
                for (int t = 0; t < d; t++) {
                    int a = i * bestN + x;
                    int b = KB + bestDJ[i][t] * bestN + MT[x * bestN + bestDG[i][t]];
                    printf("%d %d\n", a, b);
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
