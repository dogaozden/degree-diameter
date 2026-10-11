"""Bi-Cayley voltage-lift search for bipartite graphs with max degree d and diameter D.

The C engine fixes a semidirect product Z_m x| Z_k2 and K base vertices per side. Each
of the d layers is a perfect matching between A- and B-base vertices, carrying one
voltage per dart. It anneals the voltages and layer matchings, scoring the number of
(representative, vertex) pairs left beyond distance D plus a penalty per duplicate dart.
Left multiplication by the group is an automorphism, so only the 2K representatives need BFS.

Fallbacks are K_{d,d} (valid for D >= 2), PG(2,q) when D = 3, and every candidate is
checked with lib.is_valid before it replaces the best graph. This was not executed in
this session, so the C engine is unverified.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXNV 40000
#define MAXG 2000
#define DUPPEN 1000000LL

static int d, D, K, m, k2, rr, G, NV;
static int *pw, *rt, *J, *S, *adj, *deg, *vis, *queue, *cnt;
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

/* (a,b)*(c,e) = (a + r^b c, b + e) in Z_m x| Z_k2, element coded as a*k2 + b. */
static int gmul(int x, int y) {
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long long t = (long long)a + (long long)pw[b] * c;
    return (int)(t % m) * k2 + (b + e) % k2;
}

static long long evaluate(void) {
    long long dup = 0, unreached = 0;
    int N = NV;
    int total_darts = d * K;
    memset(cnt, 0, sizeof(int) * (size_t)K * K * G);
    for (int idx = 0; idx < total_darts; idx++) {
        int i = idx % K;
        int key = (i * K + J[idx]) * G + S[idx];
        if (cnt[key]++) dup++;
    }
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int idx = 0; idx < total_darts; idx++) {
        int i = idx % K, j = J[idx], s = S[idx];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (K + j) * G + rt[s * G + g];
            adj[a * d + deg[a]++] = b;
            adj[b * d + deg[b]++] = a;
        }
    }
    for (int t = 0; t < 2 * K; t++) {
        int src = (t < K) ? t * G : (K + (t - K)) * G;
        stamp++;
        int head = 0, tail = 0;
        vis[src] = stamp;
        queue[tail++] = src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = queue[head++];
                for (int q = 0; q < d; q++) {
                    int v = adj[u * d + q];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        queue[tail++] = v;
                    }
                }
            }
        }
        unreached += (long long)(N - tail);
    }
    return unreached + dup * DUPPEN;
}

int main(int argc, char **argv) {
    if (argc < 9) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long long seed = atoll(argv[3]);
    double budget = atof(argv[4]);
    K = atoi(argv[5]);
    m = atoi(argv[6]);
    k2 = atoi(argv[7]);
    rr = atoi(argv[8]);
    if (d < 1 || D < 1 || K < 1 || m < 1 || k2 < 1 ||
        (long long)m * k2 > MAXG || 2LL * K * m * k2 > MAXNV) {
        printf("0 0\n");
        return 0;
    }
    G = m * k2;
    NV = 2 * K * G;

    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (!rs) rs = 1;
    for (int w = 0; w < 20; w++) rnd64();

    pw = malloc(sizeof(int) * k2);
    long long p = 1 % m;
    for (int b = 0; b < k2; b++) {
        pw[b] = (int)p;
        p = (p * rr) % m;
    }
    rt = malloc(sizeof(int) * (size_t)G * G);
    for (int s = 0; s < G; s++)
        for (int g = 0; g < G; g++)
            rt[s * G + g] = gmul(g, s);

    J = malloc(sizeof(int) * d * K);
    S = malloc(sizeof(int) * d * K);
    adj = malloc(sizeof(int) * (size_t)NV * d);
    deg = calloc(NV, sizeof(int));
    vis = calloc(NV, sizeof(int));
    queue = malloc(sizeof(int) * NV);
    cnt = malloc(sizeof(int) * (size_t)K * K * G);
    int *perm = malloc(sizeof(int) * K);

    /* Each layer l is a permutation i -> J[l*K+i]; each A and B base vertex gets d darts. */
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int r2 = rndi(i + 1);
            int t = perm[i]; perm[i] = perm[r2]; perm[r2] = t;
        }
        for (int i = 0; i < K; i++) {
            J[l * K + i] = perm[i];
            S[l * K + i] = rndi(G);
        }
    }

    long long cost = evaluate();
    clock_t c0 = clock();
    double T = 3.0;
    long long it = 0;
    while (cost > 0) {
        if ((it & 63) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= budget) break;
            double frac = el / budget;
            T = 3.0 * pow(0.02 / 3.0, frac);
        }
        it++;
        if (K >= 2 && rndu() < 0.4) {
            int l = rndi(d);
            int i1 = rndi(K);
            int i2 = rndi(K - 1);
            if (i2 >= i1) i2++;
            int a = l * K + i1, b = l * K + i2;
            int t = J[a]; J[a] = J[b]; J[b] = t;
            long long nc = evaluate();
            if (nc <= cost || rndu() < exp((double)(cost - nc) / T)) {
                cost = nc;
            } else {
                t = J[a]; J[a] = J[b]; J[b] = t;
            }
        } else {
            int idx = rndi(d * K);
            int old = S[idx];
            int nw = rndi(G);
            if (nw == old) continue;
            S[idx] = nw;
            long long nc = evaluate();
            if (nc <= cost || rndu() < exp((double)(cost - nc) / T)) {
                cost = nc;
            } else {
                S[idx] = old;
            }
        }
    }

    long long fin = evaluate();
    if (fin != 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", NV, d * K * G);
    for (int idx = 0; idx < d * K; idx++) {
        int i = idx % K, j = J[idx], s = S[idx];
        for (int g = 0; g < G; g++) {
            printf("%d %d\n", i * G + g, (K + j) * G + rt[s * G + g]);
        }
    }
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _group_options(G):
    """All (m, k2, r) with Z_m x| Z_k2 of order G = m*k2 and r^k2 = 1 mod m, gcd(r, m) = 1."""
    opts = []
    for k2 in range(1, 13):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                opts.append((m, k2, r))
    return opts


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    if D == 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best_n and lib.is_valid(pg[0], pg[1], d, D):
            best, best_n = pg, pg[0]

    if D == 2:
        return best

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    total = min(0.8 * time_limit, time_limit - 6.0)
    deadline = start + total
    rng = random.Random(seed)
    tgt = max(best_n + 2, moore // 2)
    it = 0

    while True:
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            break
        budget = min(3.0, remaining - 1.5)
        K = rng.choice([1, 1, 1, 2, 2, 3])
        G = min(1000, max(2, tgt // (2 * K) + rng.randrange(-1, 3)))
        opts = _group_options(G)
        if not opts:
            tgt = max(best_n + 2, tgt - 2)
            continue
        m, k2, r = rng.choice(opts)
        it += 1
        cseed = (seed * 7919 + it * 104729) % (2 ** 31)
        try:
            out = lib.run_c(C_SOURCE, [d, D, cseed, f"{budget:.2f}", K, m, k2, r],
                            timeout=budget + 8.0)
        except RuntimeError:
            break
        try:
            n, e = lib.parse_graph_text(out)
        except (ValueError, IndexError):
            n, e = 0, []
        if n > best_n and lib.is_valid(n, e, d, D):
            best, best_n = (n, e), n
            tgt = n + 2 * K
        else:
            tgt = max(best_n + 2, tgt - 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
