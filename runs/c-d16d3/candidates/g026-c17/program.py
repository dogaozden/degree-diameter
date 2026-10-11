"""Bold change: bi-Cayley covering search for the D = 3 target.

A bipartite graph on A = Z_N and B = Z_N with a_x ~ b_(x+s) for s in S (|S| = d) is d-regular,
bipartite and simple. Its diameter is at most 3 whenever S - S covers all of Z_N: same-side
pairs are at distance 2, and a cross pair is at distance 3 via y - x = s - t + u.
So the search looks for a d-element set S with S - S = Z_N and as large N as possible,
which gives 2N vertices. The fallback is the conic blow-up (394 for d = 16) or K_{d,d}.
"""
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

#define MAXD 40
#define MAXN 1100

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int d, D;
static int S[MAXD], bestS[MAXD];
static int bestN = 0;
static int cnt[MAXN];

/* 1 if v is one of S[0..k-1]. */
static int has(int v, int k) {
    for (int i = 0; i < k; i++) if (S[i] == v) return 1;
    return 0;
}

/* Number of nonzero g in Z_N not of the form s - t (s != t, both in S). */
static int uncovered(int N) {
    for (int g = 0; g < N; g++) cnt[g] = 0;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            if (i != j) {
                int g = S[i] - S[j];
                if (g < 0) g += N;
                cnt[g]++;
            }
    int u = 0;
    for (int g = 1; g < N; g++) if (cnt[g] == 0) u++;
    return u;
}

/* Simulated annealing on S until S - S covers Z_N. Returns 1 on success, 0 on timeout. */
static int anneal(int N, double until) {
    for (int i = 0; i < d; i++) {
        int v;
        do v = rndint(N); while (has(v, i));
        S[i] = v;
    }
    int cur = uncovered(N);
    for (long it = 0; cur > 0; it++) {
        if ((it & 4095) == 0 && now() > until) return 0;
        int i = rndint(d), v = rndint(N);
        if (has(v, d)) continue;
        int old = S[i];
        S[i] = v;
        int nu = uncovered(N);
        double T = 0.6 * exp(-(double)(it % 30000) / 6000.0) + 0.04;
        if (nu <= cur || rnd01() < exp((cur - nu) / T)) cur = nu;
        else S[i] = old;
    }
    return 1;
}

/* Output the bi-Cayley graph for bestN: A = 0..N-1, B = N..2N-1, a_x ~ b_(x+s). */
static void print_best(void) {
    if (bestN <= 0) { printf("0 0\n"); return; }
    int N = bestN;
    printf("%d %d\n", 2 * N, N * d);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, N + (x + bestS[i]) % N);
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int N = atoi(argv[5]);
    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + limit;
    long maxN = (long)d * (d - 1) + 1;   /* |S - S| <= d(d-1) + 1 */
    if (N < d) N = d;
    if (N < 2) N = 2;
    while (N <= maxN && N < MAXN && now() < tend) {
        int ok = 0;
        while (!ok && now() < tend) {
            double rem = tend - now();
            double until = now() + (rem > 6.0 ? rem / 3 : rem);
            ok = anneal(N, until);
        }
        if (!ok) break;
        bestN = N;
        memcpy(bestS, S, sizeof(int) * d);
        N++;
    }
    print_best();
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def conic_blowup(d, D):
    """Twin-blow-up of PG(2,q) with q = d-3 odd, using a conic and a dual conic.

    Gives 2(q^2+q+1) + 2(q+1) vertices, which is 394 for q = 13 (d = 16).
    """
    q = d - 3
    if D != 3 or q < 3 or q % 2 == 0 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {v: i for i, v in enumerate(pts)}
    m = len(pts)
    conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if any(v not in index for v in conic):
        return None
    arc = [index[v] for v in conic]
    n0, base = lib.projective_plane_incidence(q)  # points 0..m-1, lines m..2m-1
    pcopy = {i: [i] for i in range(m)}
    lcopy = {j: [m + j] for j in range(m)}
    n = n0
    for i in arc:
        pcopy[i].append(n)
        n += 1
    for j in arc:
        lcopy[j].append(n)
        n += 1
    edges = set()
    for u, v in base:
        i, j = u, v - m
        for a in pcopy[i]:
            for b in lcopy[j]:
                edges.add((a, b) if a < b else (b, a))
    return n, sorted(edges)


def starts(d, D):
    """Candidate structured start graphs (validity is checked later)."""
    out = []
    ks = known_start(d, D)
    if ks is not None:
        out.append(ks)
    cb = conic_blowup(d, D)
    if cb is not None:
        out.append(cb)
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = None
    for cand in starts(d, D):
        try:
            ok = lib.is_valid(cand[0], cand[1], d, D)
        except Exception:
            ok = False
        if ok and (start is None or cand[0] > start[0]):
            start = cand
    best = start if start is not None else lib.haar_graph(d, range(d))  # K_{d,d}: always valid

    if best[0] >= lib.moore_bound(d, D) or D < 3 or d < 3:
        return best

    budget = 0.75 * time_limit - (time.monotonic() - t0) - 2.0
    if budget > 0.5:
        # Search upward from a few vertices below the current best half-order.
        N0 = max(d, best[0] // 2 - 8)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), N0],
                             timeout=budget + 10)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid structured or K_{d,d} fallback
    return best
