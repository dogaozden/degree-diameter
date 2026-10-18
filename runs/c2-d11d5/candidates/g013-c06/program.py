"""Bi-Cayley voltage-lift search over semidirect products Z_m x| Z_k2, run entirely in C.

The C engine samples a group, a base size k, random layer permutations and voltages, then
anneals the voltages so that every pair is within distance D. Left-translation is an
automorphism of the lift, so it is enough to check reachability from the 2k block
representatives, using 64-bit bitsets per vertex.

Exact constructions (projective planes, Araujo-Pardo-Lopez, W(q)) are used where they apply.
K_{d,d} is the fallback. Every returned graph is checked with lib.is_valid.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 24576
#define MAXD 32
#define MAXK 32
#define KMAX 8
#define PEN 64

static int d, D;
static uint64_t rs = 88172645463325252ULL;
static double t_end;

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

static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
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

/* Group Z_M x| Z_K2 with action r; element (a,b) is coded a*K2+b. */
static int M, K2, G;
static int pw[MAXN];

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    int A = (a + pw[b] * c) % M;
    int B = (b + e) % K2;
    return A * K2 + B;
}

static void setup_group(int m, int k2, int r) {
    M = m;
    K2 = k2;
    G = m * k2;
    pw[0] = 1 % m;
    for (int t = 1; t < k2; t++) pw[t] = (int)((long)pw[t - 1] * r % m);
}

/* Lift state. A-block i vertex i*G+g; B-block p vertex (K+p)*G+x. */
static int K, NV;
static int perm[MAXD][MAXK];
static int S[MAXD][MAXK];
static int nb[MAXN * MAXD];
static uint64_t bufA[MAXN], bufB[MAXN], reachv[MAXN];
static int best_nb[MAXN * MAXD];
static int best_K = 0, best_G = 0;
static long best_N = 0;
static long trials[KMAX + 1], wins[KMAX + 1];

/* Layer l pairs A-block i with B-block perm[l][i] by A_{i,g} ~ B_{p, g*s}. */
static void set_dart(int l, int i) {
    int p = perm[l][i], s = S[l][i];
    int ub = i * G, wb = (K + p) * G;
    for (int g = 0; g < G; g++) {
        int u = ub + g;
        int w = wb + gmul(g, s);
        nb[u * d + l] = w;
        nb[w * d + l] = u;
    }
}

/* Number of (representative, vertex) pairs at distance > D. Zero iff the lift is valid. */
static int eval_cost(void) {
    int N = NV, twoK = 2 * K;
    uint64_t *c = bufA, *n = bufB;
    memset(c, 0, sizeof(uint64_t) * (size_t)N);
    for (int b = 0; b < twoK; b++) c[(size_t)b * G] = 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = c[v];
            const int *row = nb + (size_t)v * d;
            for (int l = 0; l < d; l++) x |= c[row[l]];
            n[v] = x;
            changed |= (x != c[v]);
        }
        uint64_t *t = c;
        c = n;
        n = t;
        if (!changed) break;
    }
    memcpy(reachv, c, sizeof(uint64_t) * (size_t)N);
    int cost = 0;
    for (int v = 0; v < N; v++) cost += twoK - __builtin_popcountll(c[v]);
    return cost;
}

/* Darts with the same A-block, B-block and voltage give duplicate edges. */
static int dupcount(void) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1][i] == perm[l2][i] && S[l1][i] == S[l2][i]) dup++;
    return dup;
}

static void init_lift(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = tmp;
        }
        for (int i = 0; i < K; i++) S[l][i] = rndint(G);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

/* Simulated annealing on voltages and layer permutations. Returns 1 on success. */
static int run_candidate(long iters, long patience) {
    init_lift();
    int cost = eval_cost() + PEN * dupcount();
    double c0 = cost > 0 ? (double)cost : 1.0;
    int best_cost = cost;
    long last = 0;
    for (long t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 63) == 0 && now() > t_end) break;
        double T = 0.02 * c0 * (1.0 - (double)t / (double)iters) + 0.3;
        int c2;
        if (K >= 2 && rnd01() < 0.2) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = perm[l][i1];
            perm[l][i1] = perm[l][i2];
            perm[l][i2] = tmp;
            set_dart(l, i1);
            set_dart(l, i2);
            c2 = eval_cost() + PEN * dupcount();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                tmp = perm[l][i1];
                perm[l][i1] = perm[l][i2];
                perm[l][i2] = tmp;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            int l = -1, i = -1;
            if (rnd01() < 0.5) {
                int v = -1;
                for (int tr = 0; tr < 30; tr++) {
                    int u = rndint(NV);
                    if (__builtin_popcountll(reachv[u]) < 2 * K) { v = u; break; }
                }
                if (v >= 0) {
                    int blk = v / G;
                    l = rndint(d);
                    if (blk < K) {
                        i = blk;
                    } else {
                        for (int ii = 0; ii < K; ii++)
                            if (perm[l][ii] == blk - K) { i = ii; break; }
                    }
                }
            }
            if (i < 0) {
                l = rndint(d);
                i = rndint(K);
            }
            int old = S[l][i], nw = rndint(G);
            if (nw == old) continue;
            S[l][i] = nw;
            set_dart(l, i);
            c2 = eval_cost() + PEN * dupcount();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                S[l][i] = old;
                set_dart(l, i);
            }
        }
        if (cost < best_cost) {
            best_cost = cost;
            last = t;
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long start_n = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit - 0.5;
    if (d < 3 || D < 3 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    long moore = 0, pwr = 1;
    for (int i = 0; i < D; i++) {
        moore += pwr;
        pwr *= (d - 1);
        if (pwr > 10000000L) pwr = 10000000L;
    }
    moore *= 2;

    best_N = start_n;
    if (best_N < 2L * d) best_N = 2L * d;

    while (now() < t_end) {
        if (best_N >= moore) break;
        int k;
        if (rnd01() < 0.25) {
            k = 1 + rndint(KMAX);
        } else {
            double bs = -1.0;
            k = 1;
            for (int kk = 1; kk <= KMAX; kk++) {
                double sc = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.05 * rnd01();
                if (sc > bs) { bs = sc; k = kk; }
            }
        }
        long tk = 2L * k;
        long Gmin = best_N / tk + 1;
        if (Gmin < 2) Gmin = 2;
        double stretch = 1.02 + 0.08 * rnd01();
        long Gmax = (long)((double)best_N * stretch / (double)tk) + 2;
        long cap = MAXN / tk;
        long mcap = moore / tk;
        if (mcap < cap) cap = mcap;
        if (Gmax > cap) Gmax = cap;
        if (Gmin > Gmax) continue;

        int Gc = (int)(Gmin + rndint((int)(Gmax - Gmin + 1)));
        int divs[128];
        int nd = 0;
        for (int x = 1; x * x <= Gc; x++) {
            if (Gc % x == 0) {
                divs[nd++] = x;
                if (x * x != Gc) divs[nd++] = Gc / x;
            }
        }
        int k2 = divs[rndint(nd)];
        int m = Gc / k2;

        int r = 0;
        if (m >= 2) {
            r = 1;
            if (k2 >= 2 && rnd01() >= 0.25) {
                int found = 0;
                for (int tr = 0; tr < 60 && !found; tr++) {
                    int c;
                    if (tr == 0 && rnd01() < 0.3) c = m - 1;
                    else c = (m >= 3) ? 2 + rndint(m - 2) : 1;
                    if (c >= 1 && gcd_l(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                        r = c;
                        found = 1;
                    }
                }
            }
        }

        trials[k]++;
        K = k;
        setup_group(m, k2, r);
        NV = 2 * K * G;
        int ok = run_candidate(3000, 800);
        if (ok) {
            wins[k]++;
            if (NV > best_N) {
                best_N = NV;
                best_K = K;
                best_G = G;
                memcpy(best_nb, nb, sizeof(int) * (size_t)NV * d);
            }
        }
    }

    if (best_K == 0) {
        printf("0 0\n");
        return 0;
    }
    int NA = best_K * best_G;
    printf("%d %d\n", 2 * NA, NA * d);
    for (int u = 0; u < NA; u++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", u, best_nb[u * d + l]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main search: C voltage-lift search over semidirect products.
    if d >= 3 and D >= 3:
        remaining = final - time.monotonic() - 3.0
        if remaining > 3.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), best_n],
                                 timeout=remaining + 5)
                n, e = lib.parse_graph_text(text)
                if n > 0:
                    consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
