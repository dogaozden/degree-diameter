"""Difference-cover search over groups, with a structured fallback.

Bold change: instead of lifting or growing the structured start, search for a bi-Cayley
("Haar-type") graph. For a group G of order N and a set S of d elements, join a_x to b_{xs}
for s in S. The graph is d-regular and bipartite, and its diameter is at most 3 iff
S S^{-1} = G and S^{-1} S = G (every element of G is a difference of two elements of S,
on each side). So N can be as large as d(d-1)+1, giving up to 2(d(d-1)+1) vertices.
For d = 16 that is 482, the Moore bound. The record is 394, so a cover with N >= 198 would beat it.
C runs simulated annealing over S for groups Z_m x| Z_k, with cost = uncovered elements.

This is a long shot: near-perfect difference covers are rare. The conic-blowup start (394
for d = 16) and the other structured starts remain the fallback, so a failed search costs
only time. Only D = 3 uses the new search. Other D fall back to the structured starts
or K_{d,d}.
"""
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley difference-cover search for bipartite graphs with diameter 3.
 *
 * Usage: prog d D seed time_limit [lo]
 * Output: "n m" then m lines "u v" (a valid graph), or "0 0" if nothing was found.
 *
 * For group G (order N) and S (|S| = d): a_x ~ b_{x s}. Diameter <= 3 iff
 *   S S^{-1} = G and S^{-1} S = G.
 * Group: Z_m x| Z_k with element (a,b) = a*k+b, (a,b)(c,e) = (a + r^b c, b+e).
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 256
#define MAXD 32
#define MAXGROUPS 8192

static int d, D;
static int N;
static double t_end, t_lim;

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

/* ------------------------------------------------------------ groups */

typedef struct { int m, k, r; } GDesc;
static GDesc groups[MAXGROUPS];
static int ngroups;

static void enum_groups(int n) {
    ngroups = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            if (ngroups < MAXGROUPS) {
                groups[ngroups].m = 1;
                groups[ngroups].k = k;
                groups[ngroups].r = 0;
                ngroups++;
            }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ngroups < MAXGROUPS) {
                groups[ngroups].m = m;
                groups[ngroups].k = k;
                groups[ngroups].r = r;
                ngroups++;
            }
        }
    }
}

static int mulT[MAXG][MAXG];
static int invT[MAXG];

/* Multiplication and inverse tables for the group of order N described by g. */
static void build_table(GDesc g) {
    int m = g.m, k = g.k, r = g.r;
    int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            mulT[x][y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (mulT[x][y] == 0) invT[x] = y;
}

/* ------------------------------------------------------------ cover state */

static int S[MAXD];
static int inS[MAXG];
static int cnt1[MAXG], cnt2[MAXG]; /* cnt1: s t^{-1} counts, cnt2: s^{-1} t counts */
static int uncov;                   /* number of zero entries across both arrays */

static inline void bump(int *c, int idx, int delta) {
    if (delta > 0) {
        if (c[idx] == 0) uncov--;
        c[idx]++;
    } else {
        c[idx]--;
        if (c[idx] == 0) uncov++;
    }
}

/* Apply delta to every ordered pair involving slot `slot` (value S[slot]) and the current set. */
static void touch(int slot, int delta) {
    int v = S[slot];
    for (int j = 0; j < d; j++) {
        int t = S[j];
        bump(cnt1, mulT[v][invT[t]], delta);
        bump(cnt2, mulT[invT[v]][t], delta);
        if (j != slot) {
            bump(cnt1, mulT[t][invT[v]], delta);
            bump(cnt2, mulT[invT[t]][v], delta);
        }
    }
}

static void init_counts(void) {
    memset(cnt1, 0, sizeof cnt1);
    memset(cnt2, 0, sizeof cnt2);
    uncov = 2 * N;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) {
            bump(cnt1, mulT[S[i]][invT[S[j]]], 1);
            bump(cnt2, mulT[invT[S[i]]][S[j]], 1);
        }
}

static void random_S(void) {
    for (int x = 0; x < N; x++) inS[x] = 0;
    for (int i = 0; i < d; i++) {
        int x;
        do x = rndint(N); while (inS[x]);
        S[i] = x;
        inS[x] = 1;
    }
}

/* Simulated annealing on S. Returns 1 when both covers are complete. */
static int sa_run(long iters) {
    double T = 1.0;
    for (long it = 0; it < iters; it++) {
        if (uncov == 0) return 1;
        if ((it & 4095) == 0 && now() > t_lim) return 0;
        int i = rndint(d);
        int x;
        do x = rndint(N); while (inS[x]);
        int old = S[i];
        int before = uncov;
        touch(i, -1);
        inS[old] = 0;
        S[i] = x;
        inS[x] = 1;
        touch(i, 1);
        int delta = uncov - before;
        if (delta > 0 && rnd01() >= exp(-delta / T)) {
            touch(i, -1);
            inS[x] = 0;
            S[i] = old;
            inS[old] = 1;
            touch(i, 1);
        }
        T *= 0.99998;
        if (T < 0.15) T = 0.15;
    }
    return uncov == 0;
}

/* ------------------------------------------------------------ search over orders */

static GDesc bestG;
static int bestN = 0;
static int bestS[MAXD];

static int try_order(int n, double until) {
    N = n;
    enum_groups(n);
    t_lim = until;
    while (now() < until) {
        GDesc g = groups[rndint(ngroups)];
        build_table(g);
        random_S();
        init_counts();
        if (sa_run(300000)) {
            bestN = n;
            bestG = g;
            memcpy(bestS, S, sizeof(int) * d);
            return 1;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [lo]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = argc > 5 ? atoi(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D != 3) {
        printf("0 0\n");
        return 0;
    }
    if (lo < d) lo = d;
    int fails = 0;
    for (int n = lo; n <= d * (d - 1) + 1 && n < MAXG; n++) {
        double remain = t_end - now();
        if (remain < 0.5) break;
        double slice = remain * 0.25;
        if (slice < 1.0) slice = 1.0;
        if (slice > remain) slice = remain;
        if (try_order(n, now() + slice)) fails = 0;
        else if (++fails >= 3) break;
    }
    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    N = bestN;
    build_table(bestG);
    printf("%d %d\n", 2 * N, N * d);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, N + mulT[x][bestS[i]]);
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
    for u, v in base:            # u is a point (< m), v = m + line index
        i, j = u, v - m
        for a in pcopy[i]:
            for b in lcopy[j]:
                edges.add((a, b) if a < b else (b, a))
    return n, sorted(edges)


def starts(d, D):
    """Candidate structured start graphs (each validity-checked before use)."""
    out = []
    ks = known_start(d, D)
    if ks is not None:
        out.append(ks)
    cb = conic_blowup(d, D)
    if cb is not None:
        out.append(cb)
    return out


def difference_cover_graph(d, D, seed, budget, lo):
    """Run the C difference-cover search. Returns (n, edges), with n = 0 if nothing was found."""
    text = lib.run_c(C_SOURCE, [d, D, seed, budget, lo], stdin_graph=None, timeout=budget + 3)
    return lib.parse_graph_text(text)


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
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: always valid

    budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
    if D == 3 and d >= 3 and budget > 3.0 and best[0] < lib.moore_bound(d, D):
        lo = best[0] // 2 + 1   # a cover with N > best_n/2 gives a larger graph
        try:
            n, edges = difference_cover_graph(d, D, seed, budget, lo)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except Exception:
            pass   # keep the valid structured fallback
    return best
