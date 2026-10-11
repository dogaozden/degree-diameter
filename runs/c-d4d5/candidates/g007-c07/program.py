"""Bi-Cayley (Haar-type) search for bipartite degree-diameter graphs.

Replaces the voltage-lift hill climb with a different construction. For a finite group G of
order N (cyclic, direct, or semidirect Z_m x|_r Z_k) and a set S of d elements containing the
identity, let A = G and B = G with a_x ~ b_{x s} for s in S. Left multiplication by G is an
automorphism that preserves both sides, so the diameter is at most D exactly when BFS from a_e
and from b_e reaches all 2N vertices within D steps. That costs two BFS passes per candidate.
The C engine samples groups and connection sets for orders N above the record and keeps the
largest valid graph. The start is K_{d,d}, and Python also offers the projective-plane and
Araujo-Pardo-Lopez graphs. Every output is checked with lib.is_valid before it is returned.
"""
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley (Haar-type) search for bipartite degree-diameter graphs.
 * Usage:  prog d D seed time_limit
 * Output: "n m" then m lines "u v" for the largest valid graph found.
 *
 * Group G = Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k).
 * Graph: A-vertex x, B-vertex N+y, edges x -- N + x*s for s in S (|S| = d, 0 in S).
 * Diameter <= D iff BFS from A-vertex 0 and from B-vertex N reaches everything within D.
 */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 512
#define MAXD 16
#define MAXG 4096

static int d, D;
static double t_end;

static int mt[MAXN][MAXN];
static int ginv[MAXN];
static int rp[MAXN];

typedef struct { int m, k, r; } Grp;
static Grp groups[MAXG];
static int ngroups;

static int nbr[2 * MAXN][MAXD];
static int S[MAXD];
static int dist_[2 * MAXN], qu[2 * MAXN];

static int bestN = 0, bestM = 0;
static int bestU[MAXN * MAXD], bestV[MAXN * MAXD];

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

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

/* Bipartite Moore bound on the side size N (total order is 2N). */
static long moore_half(void) {
    if (d < 2 || D < 1) return 1;
    if (d == 2) return D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000L) break;
    }
    return s;
}

static void add_group(int m, int k, int r) {
    if (ngroups < MAXG) {
        groups[ngroups].m = m;
        groups[ngroups].k = k;
        groups[ngroups].r = r;
        ngroups++;
    }
}

/* All semidirect groups Z_m x|_r Z_k of order N (r^k = 1 mod m, gcd(r,m) = 1). */
static void enum_groups(int N) {
    ngroups = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) { add_group(1, k, 0); continue; }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            add_group(m, k, r);
        }
    }
}

static void build_group(int N, Grp g) {
    int m = g.m, k = g.k, r = g.r;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            mt[x][y] = (int)(((long)a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (mt[x][y] == 0) { ginv[x] = y; break; }
}

/* True iff the Haar graph for the current group and S has diameter <= D. */
static int check(int N) {
    int V = 2 * N;
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) {
            nbr[x][i] = N + mt[x][S[i]];
            nbr[N + x][i] = mt[x][ginv[S[i]]];
        }
    for (int src = 0; src < 2; src++) {
        int s = src ? N : 0;
        for (int v = 0; v < V; v++) dist_[v] = -1;
        int h = 0, t = 0;
        dist_[s] = 0;
        qu[t++] = s;
        while (h < t) {
            int v = qu[h++];
            if (dist_[v] >= D) continue;
            for (int i = 0; i < d; i++) {
                int u = nbr[v][i];
                if (dist_[u] < 0) {
                    dist_[u] = dist_[v] + 1;
                    qu[t++] = u;
                }
            }
        }
        if (t < V) return 0;
    }
    return 1;
}

static void record(int N) {
    if (N <= bestN) return;
    int c = 0;
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) {
            bestU[c] = x;
            bestV[c] = N + mt[x][S[i]];
            c++;
        }
    bestM = c;
    bestN = N;
}

/* Sample groups and connection sets of order N until one is valid or the time is up. */
static int try_N(int N, double until) {
    enum_groups(N);
    if (ngroups == 0) return 0;
    while (now() < until) {
        Grp g = groups[rndint(ngroups)];
        build_group(N, g);
        for (int t = 0; t < 300; t++) {
            S[0] = 0;
            for (int i = 1; i < d; i++) {
                int s, dup;
                do {
                    s = 1 + rndint(N - 1);
                    dup = 0;
                    for (int j = 0; j < i; j++)
                        if (S[j] == s) { dup = 1; break; }
                } while (dup);
                S[i] = s;
            }
            if (check(N)) {
                record(N);
                return 1;
            }
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    if (d > MAXD || d < 2 || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    /* Fallback: K_{d,d}, valid for D >= 2. */
    bestN = d;
    bestM = 0;
    for (int x = 0; x < d; x++)
        for (int y = 0; y < d; y++) {
            bestU[bestM] = x;
            bestV[bestM] = d + y;
            bestM++;
        }

    long hi = moore_half();
    int Nhi = hi > MAXN ? MAXN : (int)hi;
    while (now() < t_end) {
        int span = Nhi - bestN;
        if (span <= 0) break;
        int N = bestN + 1 + rndint(span < 3 ? span : 3);
        double left = t_end - now();
        double slice = left / 10.0;
        if (slice < 0.05) slice = 0.05;
        try_N(N, now() + slice);
    }

    printf("%d %d\n", 2 * bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
'''


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 15 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=None, timeout=budget + 5)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
