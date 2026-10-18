"""Bi-Cayley lift search with a C annealer over semidirect groups.

Vertices: A_{i,g} = i*G + g and B_{j,h} = (K+j)*G + h, where G = |group| and g, h are group elements.
Each layer l pairs A-block i with B-block sigma_l(i) through voltage S[l][i]: A_{i,g} ~ B_{sigma,g*s}.
Left multiplication by a group element is an automorphism, so the diameter condition reduces to
distances from the 2K block representatives. The C engine anneals sigma and S with bitset reach
over those representatives. Every returned graph is checked with lib.is_valid, and K_{d,d} (or a
known exact construction) is the fallback.
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

#define MAXD 32
#define MAXK 32
#define MAXR 256
#define MAXN 65536

/* usage: prog d D K M K2 R seed time_limit
 * Group Z_M x| Z_K2 with r = R (R^K2 = 1 mod M), element a*K2+b, identity 0.
 * Searches voltage lifts with K base vertices per side; prints the first valid lift
 * ("n m" + edges) or "0 0" when time runs out. */

static int d, D, K, M, K2, G, N;
static long long RR;
static long long powr[MAXR];
static int invt[MAXN];
static int sigma[MAXD][MAXK], isig[MAXD][MAXK], S[MAXD][MAXK];
static int nbr[MAXN][MAXD];
static uint64_t bufA[MAXN], bufB[MAXN], accm[MAXN], trial[MAXN];
static uint64_t rng_state = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long t = ((long long)a + powr[b] * (long long)c) % M;
    return (int)(t * K2 + (b + e) % K2);
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long long t = (-(powr[nb] * (long long)a)) % M;
    if (t < 0) t += M;
    return (int)(t * K2 + nb);
}

/* nbr[v][l] for every vertex v in layer l. */
static void build_layer(int l) {
    int KG = K * G;
    for (int v = 0; v < KG; v++) {
        int i = v / G;
        int g = v - i * G;
        int j = sigma[l][i];
        nbr[v][l] = (K + j) * G + gmul(g, S[l][i]);
    }
    for (int v = KG; v < N; v++) {
        int j = v / G - K;
        int h = v - (v / G) * G;
        int i = isig[l][j];
        nbr[v][l] = i * G + gmul(h, invt[S[l][i]]);
    }
}

/* Writes, per vertex, the bitmask of block representatives within distance D.
 * Returns the number of (representative, vertex) pairs at distance > D. */
static long evaluate(uint64_t *out) {
    uint64_t *c = bufA, *nx = bufB, *tmp;
    int B2 = 2 * K;
    memset(c, 0, sizeof(uint64_t) * (size_t)N);
    for (int b = 0; b < B2; b++) c[(size_t)b * G] |= 1ULL << b;
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < N; v++) {
            uint64_t x = c[v];
            for (int l = 0; l < d; l++) x |= c[nbr[v][l]];
            nx[v] = x;
        }
        tmp = c;
        c = nx;
        nx = tmp;
    }
    long un = 0;
    for (int v = 0; v < N; v++) {
        out[v] = c[v];
        un += B2 - __builtin_popcountll(c[v]);
    }
    return un;
}

static void swap_sigma(int l, int i1, int i2) {
    int t = sigma[l][i1];
    sigma[l][i1] = sigma[l][i2];
    sigma[l][i2] = t;
    isig[l][sigma[l][i1]] = i1;
    isig[l][sigma[l][i2]] = i2;
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) sigma[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = sigma[l][i];
            sigma[l][i] = sigma[l][j];
            sigma[l][j] = t;
        }
        for (int i = 0; i < K; i++) {
            isig[l][sigma[l][i]] = i;
            S[l][i] = rndint(G);
        }
        build_layer(l);
    }
}

static void print_graph(void) {
    int KG = K * G;
    long m = 0;
    for (int v = 0; v < KG; v++)
        for (int l = 0; l < d; l++) {
            int u = nbr[v][l], dup = 0;
            for (int l2 = 0; l2 < l; l2++)
                if (nbr[v][l2] == u) { dup = 1; break; }
            if (!dup) m++;
        }
    printf("%d %ld\n", N, m);
    for (int v = 0; v < KG; v++)
        for (int l = 0; l < d; l++) {
            int u = nbr[v][l], dup = 0;
            for (int l2 = 0; l2 < l; l2++)
                if (nbr[v][l2] == u) { dup = 1; break; }
            if (!dup) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: %s d D K M K2 R seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    K = atoi(argv[3]);
    M = atoi(argv[4]);
    K2 = atoi(argv[5]);
    RR = atoll(argv[6]);
    long seed = atol(argv[7]);
    double limit = atof(argv[8]);
    double deadline = now() + limit;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1 || K < 1 || K > MAXK || M < 2 || K2 < 1 || K2 >= MAXR) {
        printf("0 0\n");
        return 0;
    }
    G = M * K2;
    if ((long)2 * K * G > MAXN) { printf("0 0\n"); return 0; }
    N = 2 * K * G;
    RR %= M;
    if (RR < 0) RR += M;
    powr[0] = 1 % M;
    for (int b = 1; b < K2; b++) powr[b] = powr[b - 1] * RR % M;
    if (powr[K2 - 1] * RR % M != 1 % M) { printf("0 0\n"); return 0; }
    for (int x = 0; x < G; x++) invt[x] = ginv(x);
    for (int x = 0; x < G; x++)
        if (gmul(x, invt[x]) != 0) { printf("0 0\n"); return 0; }

    random_state();
    long cost = evaluate(accm);
    if (cost == 0) { print_graph(); return 0; }

    const long CYC = 6000;
    int B2 = 2 * K;
    long it = 0;
    while (1) {
        if ((it & 15) == 0 && now() > deadline) break;
        it++;
        double frac = (double)(it % CYC) / (double)CYC;
        double temp = 0.3 + 0.03 * (double)cost * (1.0 - frac);

        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            swap_sigma(l, i1, i2);
            build_layer(l);
            long nc = evaluate(trial);
            if (nc <= cost || rnd01() < exp((double)(cost - nc) / temp)) {
                cost = nc;
                memcpy(accm, trial, sizeof(uint64_t) * (size_t)N);
                if (cost == 0) { print_graph(); return 0; }
            } else {
                swap_sigma(l, i1, i2);
                build_layer(l);
            }
        } else {
            int l = rndint(d);
            int i = rndint(K);
            if (rnd01() < 0.6) {
                for (int tries = 0; tries < 24; tries++) {
                    int v = rndint(N);
                    if (__builtin_popcountll(accm[v]) < B2) {
                        int b = v / G;
                        i = (b < K) ? b : isig[l][b - K];
                        break;
                    }
                }
            }
            int oldv = S[l][i];
            int nv = rndint(G);
            if (nv == oldv) continue;
            S[l][i] = nv;
            build_layer(l);
            long nc = evaluate(trial);
            if (nc <= cost || rnd01() < exp((double)(cost - nc) / temp)) {
                cost = nc;
                memcpy(accm, trial, sizeof(uint64_t) * (size_t)N);
                if (cost == 0) { print_graph(); return 0; }
            } else {
                S[l][i] = oldv;
                build_layer(l);
            }
        }
    }
    printf("0 0\n");
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions.
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
# Group sampling for Z_m x| Z_k2.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


_KS = (1, 2, 3, 4, 5, 6, 8)
_MAX_LIFT_N = 65536


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.8 * time_limit - 2.0)
    final = t0 + total
    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions (calibration-style cases return immediately).
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

    # Voltage-lift search in C. Each call fixes one group and base size K. A success
    # ratchets the order goal upward quickly; failures back off toward the current best.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    goal = float(best_n) * 1.10

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    cyc = 0
    fails = 0
    while True:
        remaining = final - time.monotonic()
        slice_s = min(remaining - 1.0, max(4.0, min(12.0, total / 5.0)))
        if slice_s < 2.0:
            break
        k = pick_k()
        target = max(2, (int(goal) + 2 * k - 1) // (2 * k) + rng.randrange(0, 3))
        g = _sample_group(target, rng)
        if g is None:
            goal = max(best_n * 1.01, goal * 0.9)
            continue
        m, k2, r = g
        G = m * k2
        N = 2 * k * G
        if N <= best_n:
            goal = max(goal, best_n * 1.01)
            continue
        if N > _MAX_LIFT_N:
            goal = max(best_n * 1.01, goal * 0.9)
            continue

        trials[k] += 1
        cyc += 1
        try:
            text = lib.run_c(C_SOURCE, [d, D, k, m, k2, r, seed * 7919 + cyc, round(slice_s, 2)],
                             timeout=slice_s + 10.0)
            n_out, e_out = lib.parse_graph_text(text)
            fails = 0
        except Exception:
            n_out, e_out = 0, []
            fails += 1
            if fails >= 3:
                break

        if n_out > best_n:
            before = best_n
            consider(n_out, e_out)
            if best_n > before:
                wins[k] += 1
                goal = best_n * 1.15
                continue
        goal = max(best_n * 1.01, goal * 0.9)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
