"""Bi-Cayley voltage-lift search in C, then exact constructions and a K_{d,d} fallback.

The C engine searches bi-Cayley lifts over semidirect groups Z_m x| Z_k2. Each layer is a
permutation of the k base blocks with one voltage per (layer, block). Validity is decided
exactly by a block-representative bitmask (cost 0 implies diameter <= D). Simulated annealing
uses permutation and voltage moves, with restarts and a ratcheted order goal. Every returned
graph is checked with lib.is_valid, and K_{d,d} or a known construction is the fallback.
"""
import itertools
import math
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley lift annealer.
 * Usage:  prog d D seed time_limit
 * stdout: "n m" + edges of the best valid graph found (or "0 0").
 *
 * Group G = Z_M x|_r Z_K2, element a*K2+b, (a,b)(c,e) = (a + r^b c, b+e).
 * Base blocks: A_i (i<K) and B_j (j<K), vertex A_i*G+g and B_j*G+h.
 * Layer l pairs A_i with B_{perm[l][i]} through voltage s: A_{i,g} ~ B_{perm[l][i], g*s}.
 * Left translation is an automorphism, so a graph is valid iff every block representative
 * is within distance D of every vertex. The cost counts the misses plus duplicate penalties.
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXK 8
#define MAXN 16384
#define KMAX 8
#define PATIENCE 3000

static int d, D;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static long gcdl(long a, long b) {
    while (b) {
        long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long powmodl(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Group data. */
static long GM = 1;
static int K2 = 1, GO = 1;
static long PW[64];

/* Lift data. */
static int K = 1, NV = 2;
static int perm[MAXD][MAXK], pinv[MAXD][MAXK];
static int vol[MAXD][MAXK], ivol[MAXD][MAXK];
static int nb[MAXD][MAXN];
static uint64_t bufA[MAXN], bufB[MAXN];

static long bestN = 0, bestM = 0;
static int *bestE = NULL;

static inline int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long aa = ((long)a + PW[b] * (long)c) % GM;
    int bb = (b + e) % K2;
    return (int)aa * K2 + bb;
}

static inline int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nbb = (K2 - b) % K2;
    long aa = (GM - (PW[nbb] * (long)a) % GM) % GM;
    return (int)aa * K2 + nbb;
}

static void set_layer(int l) {
    for (int i = 0; i < K; i++) {
        int j = perm[l][i], s = vol[l][i];
        int A = i * GO, B = (K + j) * GO;
        for (int g = 0; g < GO; g++) nb[l][A + g] = B + gmul(g, s);
    }
    for (int j = 0; j < K; j++) {
        int i = pinv[l][j], is = ivol[l][i];
        int A = i * GO, B = (K + j) * GO;
        for (int h = 0; h < GO; h++) nb[l][B + h] = A + gmul(h, is);
    }
}

static long compute_cost(void) {
    int N = NV;
    int nbits = 2 * K;
    uint64_t full = (nbits >= 64) ? ~0ULL : ((1ULL << nbits) - 1);
    uint64_t *R = bufA, *R2 = bufB;
    memset(R, 0, sizeof(uint64_t) * (size_t)N);
    for (int b = 0; b < nbits; b++) R[(size_t)b * GO] = 1ULL << b;
    for (int t = 0; t < D; t++) {
        memcpy(R2, R, sizeof(uint64_t) * (size_t)N);
        for (int l = 0; l < d; l++) {
            const int *q = nb[l];
            for (int v = 0; v < N; v++) R2[v] |= R[q[v]];
        }
        uint64_t *tmp = R;
        R = R2;
        R2 = tmp;
    }
    long cost = 0;
    for (int v = 0; v < N; v++) cost += __builtin_popcountll(~R[v] & full);
    long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (perm[l][i] == perm[l2][i] && vol[l][i] == vol[l2][i]) dup++;
    return cost + dup * (long)N;
}

static void random_init(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = t;
        }
        for (int i = 0; i < K; i++) pinv[l][perm[l][i]] = i;
        for (int i = 0; i < K; i++) {
            vol[l][i] = rndint(GO);
            ivol[l][i] = ginv(vol[l][i]);
        }
        set_layer(l);
    }
}

/* Simulated annealing for the current group and block count. Returns 1 if cost reached 0. */
static int attempt(double deadline) {
    random_init();
    long cost = compute_cost();
    long best = cost;
    long last = 0;
    for (long it = 0;; it++) {
        if (cost == 0) return 1;
        if ((it & 31) == 0 && now() > deadline) return 0;
        if (it - last > PATIENCE) {
            random_init();
            cost = compute_cost();
            best = cost;
            last = it;
            continue;
        }
        double T = 0.5 + 0.01 * (double)cost;
        if (K >= 2 && rndint(100) < 25) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int j1 = perm[l][i1], j2 = perm[l][i2];
            perm[l][i1] = j2;
            perm[l][i2] = j1;
            pinv[l][j2] = i1;
            pinv[l][j1] = i2;
            set_layer(l);
            long c2 = compute_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                if (cost < best) {
                    best = cost;
                    last = it;
                }
            } else {
                perm[l][i1] = j1;
                perm[l][i2] = j2;
                pinv[l][j1] = i1;
                pinv[l][j2] = i2;
                set_layer(l);
            }
        } else {
            int l = rndint(d), i = rndint(K);
            int old = vol[l][i], oldi = ivol[l][i];
            int nw = rndint(GO);
            if (nw == old) continue;
            vol[l][i] = nw;
            ivol[l][i] = ginv(nw);
            set_layer(l);
            long c2 = compute_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                if (cost < best) {
                    best = cost;
                    last = it;
                }
            } else {
                vol[l][i] = old;
                ivol[l][i] = oldi;
                set_layer(l);
            }
        }
    }
}

static void save_best(void) {
    long M = (long)K * GO * d;
    int *E = (int *)realloc(bestE, sizeof(int) * 2 * (size_t)M);
    if (!E) return;
    bestE = E;
    long idx = 0;
    for (int v = 0; v < K * GO; v++)
        for (int l = 0; l < d; l++) {
            E[idx++] = v;
            E[idx++] = nb[l][v];
        }
    bestN = NV;
    bestM = M;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t_end = now() + limit * 0.9 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    static const int K2S[] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24};
    const int nk2 = (int)(sizeof(K2S) / sizeof(K2S[0]));
    long trials[KMAX + 1], wins[KMAX + 1];
    for (int c = 0; c <= KMAX; c++) {
        trials[c] = 0;
        wins[c] = 0;
    }

    while (now() < t_end) {
        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndint(KMAX);
        } else {
            double bs = -1.0;
            k = 1;
            for (int c = 1; c <= KMAX; c++) {
                double s = (wins[c] + 1.0) / (trials[c] + 2.0) + 0.05 * rnd01();
                if (s > bs) {
                    bs = s;
                    k = c;
                }
            }
        }

        double T = (double)bestN + 2.0 * k + rnd01() * 0.04 * (double)bestN;
        long Gt = (long)ceil(T / (2.0 * k));
        if (Gt < 2) Gt = 2;
        int k2 = K2S[rndint(nk2)];
        long m = (Gt + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (2L * k * m * k2 > MAXN) {
            m = (MAXN / (2L * k)) / k2;
            if (m < 2) continue;
        }
        long G = m * k2;
        if (2L * k * G <= bestN) continue;

        /* Pick r with r^k2 = 1 mod m and gcd(r, m) = 1; r = 1 (direct product) is the fallback. */
        long r = 1;
        if (k2 > 1 && m > 2) {
            for (int tr = 0; tr < 60; tr++) {
                long c = 2 + rndint((int)(m - 2));
                if (gcdl(c, m) == 1 && powmodl(c, k2, m) == 1 % m) {
                    r = c;
                    break;
                }
            }
        }
        GM = m;
        K2 = k2;
        GO = (int)G;
        K = k;
        NV = 2 * k * GO;
        PW[0] = 1 % GM;
        for (int b = 1; b < K2; b++) PW[b] = PW[b - 1] * r % GM;

        double slice = (t_end - now()) / 10.0;
        if (slice < 0.5) slice = 0.5;
        if (slice > 6.0) slice = 6.0;
        double deadline = now() + slice;
        if (deadline > t_end) deadline = t_end;

        trials[k]++;
        if (attempt(deadline)) {
            wins[k]++;
            if (NV > bestN) save_best();
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%ld %ld\n", bestN, bestM);
    for (long i = 0; i < bestM; i++) printf("%d %d\n", bestE[2 * i], bestE[2 * i + 1]);
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
    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main search: the C annealer over bi-Cayley lifts uses the remaining time.
    total = max(1.0, 0.8 * time_limit - 2.0)
    remaining = total - (time.monotonic() - t0)
    if remaining > 1.5 and d >= 2 and D >= 2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             timeout=remaining + 4.0)
            consider(*lib.parse_graph_text(text))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
