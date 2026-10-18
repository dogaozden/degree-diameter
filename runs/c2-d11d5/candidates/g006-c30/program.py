"""Bi-Cayley voltage-lift search with a native C annealer.

New in this version: the lift annealer runs in C. Group multiplication and inversion for
Z_m x| Z_k2 are computed on the fly, so no tables are sent. Reachability is tracked as
bitmasks over the 2k block representatives. Moves focus on blocks that still have
unreached pairs. Python handles group sampling, the order ratchet, and validation.

Every returned graph is checked with lib.is_valid. K_{d,d} (or an exact construction) is the fallback.
"""
import itertools
import math
import random
import time

import lib


C_LIFT = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Bi-Cayley lift annealer over G = Z_M x| Z_K2 (element (a,b) coded a*K2+b, (a,b)(c,e) = (a+r^b c, b+e)).
 * Base: K A-blocks and K B-blocks, d layers. Layer l pairs A_i with B_{lay[l][i]} via voltage S[l][i]:
 * A_{i,g} ~ B_{p,g*s}. Each layer is a permutation, so the lift is d-regular and bipartite.
 * Usage: prog d D K M K2 R seed time_limit patience
 * stdout: "N m" + edges of a lift of diameter <= D, or "0 0".
 */

#define MAXD 32
#define MAXK 8
#define MAXN 32768
#define MAXQ 64
#define PEN 1000

static int d, D, K, M, K2, R, G, N, NB;
static long long pw[MAXQ];
static int nbr[MAXD][MAXN];
static int lay[MAXD][MAXK];
static int S[MAXD][MAXK];
static uint64_t bufA[MAXN], bufB[MAXN], cur_r[MAXN], new_r[MAXN];
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
    long long t = (a + pw[b] * (long long)c) % M;
    return (int)(t * K2 + (b + e) % K2);
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long long t = (pw[nb] * (long long)a) % M;
    t = (M - t) % M;
    return (int)(t * K2 + nb);
}

static void set_dart(int l, int i) {
    int p = lay[l][i], s = S[l][i];
    int si = ginv(s);
    int bb = (K + p) * G;
    int ab = i * G;
    for (int g = 0; g < G; g++) {
        nbr[l][ab + g] = bb + gmul(g, s);
        nbr[l][bb + g] = ab + gmul(g, si);
    }
}

static void set_all(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

/* Unreached (block-representative, vertex) pairs; res[v] = mask of representatives within D of v. */
static long reach_cost(uint64_t *res) {
    uint64_t *cur = bufA, *nx = bufB;
    for (int v = 0; v < N; v++) cur[v] = (v % G == 0) ? (1ULL << (v / G)) : 0ULL;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nx[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint64_t *t = cur; cur = nx; nx = t;
        if (!changed) break;
    }
    long unr = 0;
    for (int v = 0; v < N; v++) {
        res[v] = cur[v];
        unr += NB - __builtin_popcountll(cur[v]);
    }
    return unr;
}

static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (lay[l][i] == lay[l2][i] && S[l][i] == S[l2][i]) c++;
    return c;
}

static long total_cost(uint64_t *res) { return reach_cost(res) + PEN * dup_count(); }

static int accept(long c2, long c1, double temp) {
    if (c2 <= c1) return 1;
    return rnd01() < exp(-(double)(c2 - c1) / temp);
}

static int run(double deadline, long patience) {
    uint64_t full = (NB >= 64) ? ~0ULL : ((1ULL << NB) - 1);
    while (now() < deadline) {
        for (int l = 0; l < d; l++) {
            for (int i = 0; i < K; i++) lay[l][i] = i;
            for (int i = K - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = lay[l][i]; lay[l][i] = lay[l][j]; lay[l][j] = t;
            }
            for (int i = 0; i < K; i++) S[l][i] = rndint(G);
        }
        set_all();
        long cost = total_cost(cur_r);
        long best = cost, last = 0;
        for (long it = 0;; it++) {
            if (cost == 0) return 1;
            if ((it & 7) == 0 && now() >= deadline) return 0;
            if (it - last > patience) break;
            double temp = 0.4 + 2.0 * (1.0 - (double)(it - last) / (double)patience);

            if (K >= 2 && rnd01() < 0.25) {
                int l = rndint(d);
                int i1 = rndint(K), i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                int t = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = t;
                set_dart(l, i1); set_dart(l, i2);
                long c2 = total_cost(new_r);
                if (accept(c2, cost, temp)) {
                    cost = c2;
                    memcpy(cur_r, new_r, sizeof(uint64_t) * (size_t)N);
                    if (cost < best) { best = cost; last = it; }
                } else {
                    t = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = t;
                    set_dart(l, i1); set_dart(l, i2);
                }
                continue;
            }

            int l = -1, i = -1;
            if (rnd01() < 0.4) {
                /* Focus on a block that still has unreached pairs. */
                int v = -1;
                for (int tries = 0; tries < 16; tries++) {
                    int u = rndint(N);
                    if (cur_r[u] != full) { v = u; break; }
                }
                if (v >= 0) {
                    int b = v / G;
                    l = rndint(d);
                    if (b < K) i = b;
                    else {
                        for (int j = 0; j < K; j++)
                            if (lay[l][j] == b - K) { i = j; break; }
                    }
                }
            }
            if (l < 0 || i < 0) { l = rndint(d); i = rndint(K); }

            int old = S[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            S[l][i] = nw;
            set_dart(l, i);
            long c2 = total_cost(new_r);
            if (accept(c2, cost, temp)) {
                cost = c2;
                memcpy(cur_r, new_r, sizeof(uint64_t) * (size_t)N);
                if (cost < best) { best = cost; last = it; }
            } else {
                S[l][i] = old;
                set_dart(l, i);
            }
        }
    }
    return 0;
}

static void print_lift(void) {
    long m = (long)d * K * G;
    printf("%d %ld\n", N, m);
    for (int u = 0; u < K * G; u++)
        for (int l = 0; l < d; l++) printf("%d %d\n", u, nbr[l][u]);
}

int main(int argc, char **argv) {
    if (argc < 10) {
        fprintf(stderr, "usage: %s d D K M K2 R seed time_limit patience\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]); D = atoi(argv[2]); K = atoi(argv[3]);
    M = atoi(argv[4]); K2 = atoi(argv[5]); R = atoi(argv[6]);
    long seed = atol(argv[7]);
    double limit = atof(argv[8]);
    long patience = atol(argv[9]);
    if (d < 1 || d > MAXD || D < 1 || K < 1 || K > MAXK || M < 1 || K2 < 1 || K2 > MAXQ) {
        printf("0 0\n");
        return 0;
    }
    G = M * K2;
    N = 2 * K * G;
    NB = 2 * K;
    if (N > MAXN) { printf("0 0\n"); return 0; }
    R = ((R % M) + M) % M;
    pw[0] = 1 % M;
    for (int b = 1; b < K2; b++) pw[b] = (pw[b - 1] * R) % M;
    if ((pw[K2 - 1] * R) % M != 1 % M) { printf("0 0\n"); return 0; }
    if (patience < 1) patience = 1;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    double deadline = now() + limit;
    if (run(deadline, patience)) print_lift();
    else printf("0 0\n");
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


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4)
_PATIENCE = 1500


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 1.5)
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

    # Lift search: a bandit over base sizes k, with the order goal ratcheted upward.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    goal = float(best_n) * 1.05

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        left = final - time.monotonic()
        if left < 1.5:
            break
        k = pick_k()
        target = max(2, int(goal // (2 * k)) + rng.randrange(0, 3))
        g = _sample_group(target, rng)
        if g is None:
            goal = max(float(best_n) * 1.02, goal * 0.99)
            continue
        m, k2, r = g
        G = m * k2
        if 2 * k * G <= best_n:
            goal = max(goal, best_n * 1.02)
            continue
        trials[k] += 1
        slice_s = min(left - 0.5, max(3.0, total / 8.0))
        try:
            text = lib.run_c(C_LIFT, [d, D, k, m, k2, r, rng.randrange(1 << 30),
                                      round(slice_s, 2), _PATIENCE],
                             timeout=slice_s + 10)
            n, e = lib.parse_graph_text(text)
        except Exception:
            n, e = 0, []
        if n > 0:
            wins[k] += 1
            consider(n, e)
            goal = max(goal, n * 1.04)
        else:
            goal = max(float(best_n) * 1.02, goal * 0.99)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
