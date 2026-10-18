"""Multi-orbit bi-Cayley lift search for the weakest cases (d = 5, D = 7 is the target).

Construction: a group G of order N (semidirect product Z_m x|_r Z_k) and a base bipartite graph
with p "A" orbits and p "B" orbits, each of degree d. Vertex (A_i, x) is joined to (B_j, x*g) for
every dart (i, j, g). Each A orbit has d darts, and each B orbit receives exactly d darts, so the
lift is d-regular and bipartite. The parent is the special case p = 1.

New in this version: the base graph is searched as well as the voltages. Moves change a dart's
voltage, or swap the B-targets of two darts, which keeps every B orbit at degree d. Left
multiplication by G is an automorphism, so the diameter check needs one BFS from each of the 2p
orbit representatives (u, e). Larger p gives orders 2pN, so smaller groups can reach the target
order. The start graph is the fallback.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-orbit base lift search over semidirect groups Z_m x|_r Z_k.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0".
 * stdout:  the best valid graph found (lift if it beats the start, else the start).
 *
 * Base: p A-orbits and p B-orbits, each vertex of degree d. Darts k = 0..p*d-1 belong to
 * A-orbit i = k / d and go to B-orbit dj[k] with voltage dg[k]. Every B-orbit receives d darts.
 * Vertices: A-orbit i, element x -> i*N + x. B-orbit j, element y -> (p + j)*N + y.
 * Edges: (A_i, x) -- (B_{dj[k]}, x * dg[k]) for each dart k of orbit i.
 * Left multiplication by G is an automorphism, so diameter <= D iff BFS from (u, e) for each of
 * the 2p orbit representatives reaches everything within D.
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
#define MAXP 3
#define MAXDART (MAXP * MAXD)
#define MAXV (2 * MAXP * MAXH)
#define MAXOUT (MAXDART * MAXH)
#define MAXE 40000
#define MAXCAND 512
#define STEPS 8000
#define SPAN 40
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
        const int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++)
            if (row[y] == 0) { INVT[x] = y; break; }
    }
}

/* Base lift state. */
static int P_;                 /* orbits per side */
static int ntot;               /* number of darts = P_ * d */
static int dj[MAXDART];        /* B-orbit target of dart k; A-orbit is k / d */
static int dg[MAXDART];        /* voltage of dart k */
static int bA[MAXDART];        /* for B-orbit j: list of its darts' A-orbits at j*d + t */
static int bG[MAXDART];        /* and the inverse voltages */

static int dist_[MAXV], seen_[MAXV], q_[MAXV];
static int stamp_ = 0;

/* 1 if dart k does not duplicate another dart of its A-orbit (same target and voltage). */
static int dart_ok(int k) {
    int base = (k / d) * d;
    for (int t = 0; t < d; t++) {
        int k2 = base + t;
        if (k2 != k && dj[k2] == dj[k] && dg[k2] == dg[k]) return 0;
    }
    return 1;
}

/* Random dart targets (each B-orbit gets exactly d darts) and repaired voltages. */
static int init_base(void) {
    int N = NN;
    int slot[MAXDART];
    for (int s = 0; s < ntot; s++) slot[s] = s / d;
    for (int s = ntot - 1; s > 0; s--) {
        int r = rndint(s + 1);
        int tmp = slot[s]; slot[s] = slot[r]; slot[r] = tmp;
    }
    for (int k = 0; k < ntot; k++) { dj[k] = slot[k]; dg[k] = rndint(N); }
    for (int round = 0; round < 2000; round++) {
        int clash = 0;
        for (int k = 0; k < ntot; k++)
            if (!dart_ok(k)) { dg[k] = rndint(N); clash = 1; }
        if (!clash) return 1;
    }
    return 0;
}

/* Number of (source, vertex) pairs at distance > D over the 2p orbit representatives. */
static long eval_bad(void) {
    int N = NN, p = P_, V = 2 * p * N;
    int cntB[MAXP];
    for (int j = 0; j < p; j++) cntB[j] = 0;
    for (int k = 0; k < ntot; k++) {
        int j = dj[k], i = k / d;
        bA[j * d + cntB[j]] = i;
        bG[j * d + cntB[j]] = INVT[dg[k]];
        cntB[j]++;
    }
    long total = 0;
    for (int s = 0; s < 2 * p; s++) {
        int src = (s < p) ? s * N : p * N + (s - p) * N;
        int head = 0, tail = 0;
        stamp_++;
        seen_[src] = stamp_;
        dist_[src] = 0;
        q_[tail++] = src;
        while (head < tail) {
            int v = q_[head++];
            int dv = dist_[v];
            if (dv >= D) continue;
            if (v < p * N) {
                int i = v / N, x = v - i * N;
                const int *row = MTAB + (size_t)x * N;
                for (int t = 0; t < d; t++) {
                    int k = i * d + t;
                    int u = (p + dj[k]) * N + row[dg[k]];
                    if (seen_[u] != stamp_) {
                        seen_[u] = stamp_;
                        dist_[u] = dv + 1;
                        q_[tail++] = u;
                    }
                }
            } else {
                int rel = v - p * N;
                int j = rel / N, y = rel - j * N;
                const int *row = MTAB + (size_t)y * N;
                for (int t = 0; t < d; t++) {
                    int u = bA[j * d + t] * N + row[bG[j * d + t]];
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

/* Annealed search over voltages (moves a) and B-target swaps (moves b). */
static long climb(double until, double T0) {
    long bad = eval_bad();
    double T = T0;
    int N = NN;
    for (long s = 0; s < STEPS && bad > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        int kind = rndint(3);
        if (kind < 2) {
            int k = rndint(ntot);
            int oldg = dg[k];
            int ng = rndint(N);
            if (ng == oldg) continue;
            dg[k] = ng;
            if (!dart_ok(k)) { dg[k] = oldg; continue; }
            long nb = eval_bad();
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
            else dg[k] = oldg;
        } else {
            int k1 = rndint(ntot), k2 = rndint(ntot);
            if (dj[k1] == dj[k2]) continue;
            int tmp = dj[k1]; dj[k1] = dj[k2]; dj[k2] = tmp;
            if (!dart_ok(k1) || !dart_ok(k2)) {
                tmp = dj[k1]; dj[k1] = dj[k2]; dj[k2] = tmp;
                continue;
            }
            long nb = eval_bad();
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
            else { tmp = dj[k1]; dj[k1] = dj[k2]; dj[k2] = tmp; }
        }
        T *= 0.9995;
        if (T < 0.2) T = 0.2;
    }
    return bad;
}

static int OU[MAXOUT], OV[MAXOUT];
static const int PSEL[5] = {2, 2, 3, 3, 1};

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

    int found = 0, bestP = 0, bestN = 0, ne = 0;
    long best_n = sn;

    if (d >= 3 && d <= MAXD && D >= 2) {
        long moore = moore_bound();
        static Grp cand[MAXCAND];

        while (now() < t_end) {
            int anyalive = 0;
            for (int p = 1; p <= MAXP; p++) {
                long lo = best_n / (2L * p) + 1;
                if (lo < d + 1) lo = d + 1;
                long hi = moore / (2L * p);
                if (hi > MAXH) hi = MAXH;
                if (lo <= hi) anyalive = 1;
            }
            if (!anyalive) break;

            int p = PSEL[rndint(5)];
            long lo = best_n / (2L * p) + 1;
            if (lo < d + 1) lo = d + 1;
            long hi = moore / (2L * p);
            if (hi > MAXH) hi = MAXH;
            if (lo > hi) continue;
            long span = hi - lo + 1;
            if (span > SPAN) span = SPAN;
            int N = (int)(lo + rndint((int)span));

            int cnt = enum_groups(N, cand);
            if (cnt <= 0) continue;
            Grp G = pick_group(cand, cnt);
            P_ = p;
            ntot = p * d;
            setup_group(N, G);

            long bad = 1;
            for (int rs = 0; rs < RESTARTS && bad > 0 && now() < t_end; rs++) {
                if (!init_base()) { bad = 1; continue; }
                bad = climb(t_end, rs == 0 ? 2.0 : 1.0);
            }
            if (bad == 0) {
                found = 1;
                bestP = p;
                bestN = N;
                best_n = 2L * p * N;
                ne = 0;
                for (int k = 0; k < ntot; k++) {
                    int i = k / d;
                    for (int x = 0; x < N; x++) {
                        OU[ne] = i * N + x;
                        OV[ne] = (p + dj[k]) * N + MTAB[(size_t)x * N + dg[k]];
                        ne++;
                    }
                }
            }
        }
    }

    if (found) {
        printf("%d %d\n", 2 * bestP * bestN, ne);
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
