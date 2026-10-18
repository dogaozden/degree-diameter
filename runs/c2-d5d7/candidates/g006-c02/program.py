"""Multi-orbit bi-Cayley lift search for the weakest cases (d = 5, D = 7 is the target).

New idea: a multi-orbit lift. Take a semidirect group G = Z_m x|_r Z_k of order N and a base
graph with P vertices per side. Each A-side base vertex i has d darts to B-side base vertices
sig_t(i) with voltages vol_t(i) in G, where sig_0 is the identity with zero voltage. The lift has
2*P*N vertices, is d-regular and bipartite, and gives order 2PN. The parent's single-orbit lift
is the case P = 1.

Left multiplication by G is an automorphism that is transitive on each fiber, so the diameter
check needs only 2P BFS runs, one from each base vertex's identity lift. C hill-climbs the
voltages and the base permutations sig_t (t >= 1) to reach diameter D, with duplicate-edge
penalties. Orders above the start graph's total are targeted, with P chosen at random in 1..6.

The start graph (the H(q) hexagon incidence graph, or a smaller algebraic graph) is the fallback.
Every candidate is checked with lib.is_valid before it is returned.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-orbit bi-Cayley lift search over semidirect groups Z_m x|_r Z_k.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0".
 * stdout:  the best valid graph found (lift if it beats the start, else the start).
 *
 * Base: P vertices per side. Side index s in 0..2P-1: A_i = i, B_j = P + j.
 * Vertex (s, x) has id s*N + x, x in G with |G| = N, total 2PN vertices.
 * Darts: for t = 0..d-1 and i in 0..P-1, A_{i,x} -- B_{sig_t(i), x * vol_t(i)}.
 * sig_0 = identity and vol_0 = identity, and sig_t are permutations of 0..P-1.
 * Left multiplication by G is an automorphism, transitive on each fiber, so diameter <= D
 * is equivalent to BFS from A_{i,e} and B_{j,e} for all i, j reaching everything within D.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1600
#define MAXP 6
#define MAXD 16
#define MAXV (2 * MAXP * MAXN)
#define MAXE 40000
#define MAXOUT (MAXP * MAXD * MAXN)
#define MAXCAND 512
#define STEPS 30000
#define SPAN 24
#define PEN 1000000L

typedef struct { int m, k, r; } Grp;

static int d, D, P, NN;
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
static int MTAB[MAXN * MAXN];
static int INVT[MAXN];
static int RP[MAXN];

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

/* Base structure: sig[t][i] = B-index of dart t from A_i; vol[t][i] = voltage of that dart. */
static int sig[MAXD][MAXP], vol[MAXD][MAXP];
static int sinv[MAXD][MAXP];   /* sinv[t][j] = i with sig[t][i] = j */
static int gB[MAXD][MAXP];     /* gB[t][j] = inverse of vol[t][sinv[t][j]] */

static void refresh(void) {
    for (int t = 0; t < d; t++)
        for (int i = 0; i < P; i++) sinv[t][sig[t][i]] = i;
    for (int t = 0; t < d; t++)
        for (int j = 0; j < P; j++) gB[t][j] = INVT[vol[t][sinv[t][j]]];
}

/* Number of duplicate (same neighbour) darts from the same A-base vertex. */
static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < P; i++)
        for (int t = 0; t < d; t++)
            for (int u = t + 1; u < d; u++)
                if (sig[t][i] == sig[u][i] && vol[t][i] == vol[u][i]) c++;
    return c;
}

static int dist_[MAXV], seen_[MAXV], q_[MAXV];
static int stamp_ = 0;

/* Total number of (source, vertex) pairs at distance > D, sources = identity of each fiber. */
static long eval_bad(void) {
    int N = NN, V = 2 * P * N;
    refresh();
    long total = PEN * dup_count();
    for (int s = 0; s < 2 * P; s++) {
        int src = s * N;
        int head = 0, tail = 0;
        stamp_++;
        seen_[src] = stamp_;
        dist_[src] = 0;
        q_[tail++] = src;
        while (head < tail) {
            int v = q_[head++];
            int dv = dist_[v];
            if (dv >= D) continue;
            int k = v / N, x = v - k * N;
            const int *row = MTAB + (size_t)x * N;
            if (k < P) {
                for (int t = 0; t < d; t++) {
                    int u = (P + sig[t][k]) * N + row[vol[t][k]];
                    if (seen_[u] != stamp_) {
                        seen_[u] = stamp_;
                        dist_[u] = dv + 1;
                        q_[tail++] = u;
                    }
                }
            } else {
                int j = k - P;
                for (int t = 0; t < d; t++) {
                    int u = sinv[t][j] * N + row[gB[t][j]];
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

/* Annealed hill-climb over voltages (t >= 1) and base permutations (t >= 1). */
static long climb(double until) {
    long bad = eval_bad();
    double T = 2.0;
    for (long s = 0; s < STEPS && bad > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        if (P > 1 && rnd01() < 0.3) {
            int t = 1 + rndint(d - 1);
            int i = rndint(P), i2 = rndint(P);
            if (i == i2) continue;
            int a = sig[t][i], b = sig[t][i2];
            sig[t][i] = b;
            sig[t][i2] = a;
            long nb = eval_bad();
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
            else { sig[t][i] = a; sig[t][i2] = b; }
        } else {
            int t = 1 + rndint(d - 1);
            int i = rndint(P);
            int old = vol[t][i];
            vol[t][i] = rndint(NN);
            long nb = eval_bad();
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
            else vol[t][i] = old;
        }
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
    static Grp cand[MAXCAND];
    int found = 0, bestP = 0, bestN = 0, ne = 0;
    long best_total = sn;

    if (d >= 3 && d <= MAXD && D >= 2) {
        long moore = moore_bound();
        double attempt_len = limit * 0.9 * 0.2;
        if (attempt_len < 1.0) attempt_len = 1.0;
        while (now() < t_end) {
            int Pt = 1 + rndint(MAXP);
            long Nlo = best_total / (2L * Pt) + 1;
            if (Nlo < d) Nlo = d;
            long Nhi = moore / (2L * Pt);
            if (Nhi > MAXN) Nhi = MAXN;
            if (Nlo > Nhi) continue;
            long span = Nhi - Nlo + 1;
            if (span > SPAN) span = SPAN;
            int N = (int)(Nlo + rndint((int)span));
            int cnt = enum_groups(N, cand);
            if (cnt <= 0) continue;
            Grp G = pick_group(cand, cnt);
            setup_group(N, G);
            P = Pt;
            for (int i = 0; i < P; i++) { sig[0][i] = i; vol[0][i] = 0; }
            for (int t = 1; t < d; t++) {
                for (int i = 0; i < P; i++) sig[t][i] = i;
                for (int i = P - 1; i > 0; i--) {
                    int j = rndint(i + 1);
                    int tmp = sig[t][i];
                    sig[t][i] = sig[t][j];
                    sig[t][j] = tmp;
                }
                for (int i = 0; i < P; i++) vol[t][i] = rndint(NN);
            }
            double until = now() + attempt_len;
            if (until > t_end) until = t_end;
            long bad = climb(until);
            if (bad == 0) {
                found = 1;
                bestP = P;
                bestN = N;
                best_total = 2L * P * N;
                ne = 0;
                for (int t = 0; t < d; t++)
                    for (int i = 0; i < P; i++)
                        for (int x = 0; x < N; x++) {
                            OU[ne] = i * N + x;
                            OV[ne] = (P + sig[t][i]) * N + MTAB[(size_t)x * N + vol[t][i]];
                            ne++;
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
