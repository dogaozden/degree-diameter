"""Bi-Cayley search engine over semidirect groups Z_M x| Z_K.

For the target cases this replaces the numpy lift search with a C simulated annealing over
connection sets. The graph is A_x ~ B_{x*s} for s in S, |S| = d, on a group G of order m, so it
has 2m vertices and is d-regular. Left multiplication is an automorphism, so the diameter check
reduces to two BFS runs, from A_e and from B_e. This makes each evaluation roughly
O(m*d*D) instead of the O(n^2 d D / 64) bitset check. The C engine searches over groups of
growing order and returns the largest valid graph it finds.

Fallbacks: K_{d,d}, the projective plane incidence graph, and the Araujo-Pardo-Lopez graph.
Every returned graph is checked with lib.is_valid.
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

#define MAXM 10000
#define MAXG (MAXM + 64)
#define MAXN (2 * MAXG)
#define MAXDEG 64

/* Graph: A_x = x, B_y = m + y, edge A_x -- B_{x*s} for s in S (|S| = d). */
static int dg, DD;
static int gM, gK, gR, mG;
static int pw[64];
static int qa[MAXG], qb[MAXG];
static int S[MAXDEG], invS[MAXDEG];
static int bestS[MAXDEG];
static int bestM, bestK, bestR, bestm;
static int found = 0;
static int mark[MAXN], dist_[MAXN], queue_[MAXN];
static int stamp = 0;
static double t_end;
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

static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long long powmodll(long long b, int e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Semidirect product Z_M x| Z_K, element (a,b) coded as a*K+b, (a,b)(c,e) = (a + R^b c, b + e). */
static void set_group(int M, int K, int R) {
    gM = M;
    gK = K;
    gR = R;
    mG = M * K;
    pw[0] = 1 % M;
    for (int b = 1; b < K; b++) pw[b] = (int)((long long)pw[b - 1] * R % M);
    for (int x = 0; x < mG; x++) {
        qa[x] = x / K;
        qb[x] = x % K;
    }
}

static inline int gmul(int x, int y) {
    int a1 = qa[x], b1 = qb[x], a2 = qa[y], b2 = qb[y];
    int a = (int)(((long long)a1 + (long long)pw[b1] * a2) % gM);
    int b = b1 + b2;
    if (b >= gK) b -= gK;
    return a * gK + b;
}

/* Inverse of (a,b) is (-R^(K-b) a, K-b). */
static inline int ginv(int x) {
    int a = qa[x], b = qb[x];
    int nb = (gK - b) % gK;
    long long t = (long long)pw[nb] * a % gM;
    int a2 = (int)((gM - t) % gM);
    return a2 * gK + nb;
}

static const int KS[] = {1, 1, 2, 2, 2, 3, 3, 4, 4, 5, 6, 6, 7, 8, 9, 10, 12};

/* Random group of order >= target (cyclic or semidirect), sets globals, returns order. */
static int sample_group(int target) {
    int K = KS[rndint(17)];
    int M = (target + K - 1) / K;
    if (M < 2) M = 2;
    int R = 1;
    if (K > 1 && M >= 3 && rnd01() >= 0.3) {
        for (int t = 0; t < 200; t++) {
            int c = 2 + rndint(M - 2);
            if (gcdi(c, M) == 1 && powmodll(c, K, M) == 1 % M) {
                R = c;
                break;
            }
        }
    }
    set_group(M, K, R);
    return mG;
}

static int in_S(int s) {
    for (int i = 0; i < dg; i++)
        if (S[i] == s) return 1;
    return 0;
}

static int dup_upto(int s, int i) {
    for (int j = 0; j < i; j++)
        if (S[j] == s) return 1;
    return 0;
}

/* Number of vertices NOT within distance DD of src. */
static long unreached(int src) {
    int N = 2 * mG;
    stamp++;
    int head = 0, tail = 0;
    queue_[tail++] = src;
    mark[src] = stamp;
    dist_[src] = 0;
    while (head < tail) {
        int v = queue_[head++];
        if (dist_[v] >= DD) continue;
        for (int i = 0; i < dg; i++) {
            int u = (v < mG) ? mG + gmul(v, S[i]) : gmul(v - mG, invS[i]);
            if (mark[u] != stamp) {
                mark[u] = stamp;
                dist_[u] = dist_[v] + 1;
                queue_[tail++] = u;
            }
        }
    }
    return N - tail;
}

/* Left multiplication is an automorphism, so A_e and B_e BFS cover all pairs. */
static long cost_of(void) { return unreached(0) + unreached(mG); }

static int anneal(long iters, long patience) {
    for (int i = 0; i < dg; i++) {
        int s;
        do { s = rndint(mG); } while (dup_upto(s, i));
        S[i] = s;
        invS[i] = ginv(s);
    }
    long cost = cost_of(), best = cost, last = 0;
    for (long t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 63) == 0 && now() > t_end) break;
        double T = 2.0 * (1.0 - (double)t / (double)iters) + 0.05;
        int i = rndint(dg), s = rndint(mG);
        if (in_S(s)) continue;
        int old = S[i], oldinv = invS[i];
        S[i] = s;
        invS[i] = ginv(s);
        long c2 = cost_of();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost < best) { best = cost; last = t; }
        } else {
            S[i] = old;
            invS[i] = oldinv;
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit start_m\n", argv[0]);
        return 2;
    }
    int d = atoi(argv[1]), D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int start_m = atoi(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (d < 2 || d > MAXDEG || D < 2) { printf("0 0\n"); return 0; }
    dg = d;
    DD = D;
    bestm = start_m;

    while (now() < t_end) {
        int extra = bestm / 200 + 3;
        int target = bestm + 1 + rndint(extra);
        if (target < dg) target = dg;
        if (target > MAXM) break;
        int m = sample_group(target);
        if (m <= bestm || m < dg) continue;
        if (anneal(8000, 2000)) {
            bestm = m;
            bestM = gM;
            bestK = gK;
            bestR = gR;
            memcpy(bestS, S, sizeof(int) * dg);
            found = 1;
        }
    }

    if (!found) { printf("0 0\n"); return 0; }
    set_group(bestM, bestK, bestR);
    for (int i = 0; i < dg; i++) {
        S[i] = bestS[i];
        invS[i] = ginv(S[i]);
    }
    int m = mG;
    printf("%d %d\n", 2 * m, m * dg);
    for (int x = 0; x < m; x++)
        for (int i = 0; i < dg; i++)
            printf("%d %d\n", x, m + gmul(x, S[i]));
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions used as starting points and fallbacks.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

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

    # Main phase: C annealing over bi-Cayley graphs on semidirect products, growing the group
    # order from the current best. Each graph has 2m vertices, so the start is best_n // 2.
    total = max(1.0, 0.85 * time_limit - 2.0)
    remaining = t0 + total - time.monotonic() - 1.0
    if remaining > 3.0 and best_n >= 4:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), best_n // 2],
                             stdin_graph=None, timeout=remaining + 15)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
