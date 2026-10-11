import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine: simulated annealing over bi-Cayley lifts of a small base graph,
# where the voltage group is a FINITE GROUP given by a multiplication table.
#
# Groups supported (both built inside C):
#   gtype 0: semidirect product Z_m x|_r Z_k, element (a, b) coded as a*k + b,
#            (a, b)(c, d) = (a + r^b c, b + d). (k = 1 gives the cyclic group.)
#   gtype 1: affine group AGL(1, p), p prime, element (b, a) coded as
#            b*(p-1) + (a-1), (b1, a1)(b2, a2) = (b1 + a1 b2, a1 a2).
#
# Base graph: K A-orbits and K B-orbits, DEG layers. Layer l is a permutation
# sigma_l of {0..K-1}; dart (l, i) joins A_i,g to B_{sigma_l(i),g*s}.
# Every vertex has degree DEG and the graph is bipartite.
# Cost = excess distance beyond DIAM over BFS from the 2K orbit representatives
# (by vertex transitivity this covers all pairs), plus a duplicate-edge penalty.
#
# Usage: prog DEG DIAM K gtype m k r seed slice_seconds
# Prints a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

GROUP_C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define BIGCOST (1 << 30)
#define STAG 6000
#define MAXNG 1500

static int DEG, DIAM, K, NG, NE, N;
static int *TAB;
static int *INV;
static int *POWR;
static int *dI, *dJ, *dS, *bestS, *bestJ;
static int *adj, *cnt, *fr, *nx;
static uint32_t *vis;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;
static clock_t T0C;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - T0C) / (double)CLOCKS_PER_SEC; }

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int is_prime(int p) {
    if (p < 2) return 0;
    for (int q = 2; (long long)q * q <= p; q++) if (p % q == 0) return 0;
    return 1;
}

static int build_group(int gtype, int m, int k, int r) {
    if (gtype == 0) {
        if (m < 1 || k < 1 || r < 0) return 0;
        r %= m;
        if (gcd_int(r, m) != 1) return 0;
        long long ng = (long long)m * k;
        if (ng > MAXNG) return 0;
        NG = (int)ng;
        POWR = malloc(sizeof(int) * (size_t)k);
        if (!POWR) return 0;
        POWR[0] = 1 % m;
        for (int b = 1; b < k; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % m);
        if (((long long)POWR[k - 1] * r) % m != 1 % m) return 0;
        TAB = malloc(sizeof(int) * (size_t)NG * NG);
        if (!TAB) return 0;
        for (int x = 0; x < NG; x++) {
            int a = x / k, b = x % k;
            for (int y = 0; y < NG; y++) {
                int c = y / k, dd = y % k;
                long long t = (a + (long long)POWR[b] * c) % m;
                TAB[x * NG + y] = (int)(t * k + (b + dd) % k);
            }
        }
    } else {
        int p = m;
        if (p < 3 || !is_prime(p)) return 0;
        long long ng = (long long)p * (p - 1);
        if (ng > MAXNG) return 0;
        NG = (int)ng;
        TAB = malloc(sizeof(int) * (size_t)NG * NG);
        if (!TAB) return 0;
        for (int x = 0; x < NG; x++) {
            int b1 = x / (p - 1), a1 = x % (p - 1) + 1;
            for (int y = 0; y < NG; y++) {
                int b2 = y / (p - 1), a2 = y % (p - 1) + 1;
                long long bb = (b1 + (long long)a1 * b2) % p;
                long long aa = ((long long)a1 * a2) % p;
                TAB[x * NG + y] = (int)(bb * (p - 1) + (aa - 1));
            }
        }
    }
    INV = malloc(sizeof(int) * NG);
    if (!INV) return 0;
    for (int x = 0; x < NG; x++) {
        INV[x] = 0;
        for (int y = 0; y < NG; y++) if (TAB[x * NG + y] == 0) { INV[x] = y; break; }
    }
    return 1;
}

static void build_adj(void) {
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < NE; e++) {
        int ba = dI[e] * NG, bb = (K + dJ[e]) * NG, s = dS[e];
        for (int g = 0; g < NG; g++) {
            int a = ba + g, b = bb + TAB[g * NG + s];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
}

static int cost_fn(void) {
    int dup = 0;
    for (int e1 = 0; e1 < NE; e1++)
        for (int e2 = e1 + 1; e2 < NE; e2++)
            if (dI[e1] == dI[e2] && dJ[e1] == dJ[e2] && dS[e1] == dS[e2]) dup++;

    build_adj();

    const int LMAX = DIAM + 3;
    const int UNREACH_W = LMAX - DIAM + 2;
    int total = 0;
    for (int ri = 0; ri < 2 * K; ri++) {
        int src = ri * NG;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)N);
            stamp = 0;
        }
        stamp++;
        vis[src] = stamp;
        int *cur = fr, *nxt = nx;
        int fn = 1, reached = 1;
        cur[0] = src;
        for (int lv = 0; lv < LMAX && fn > 0; lv++) {
            int nn = 0;
            for (int q = 0; q < fn; q++) {
                int u = cur[q];
                const int *au = adj + (size_t)u * DEG;
                for (int t = 0; t < DEG; t++) {
                    int v = au[t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        nxt[nn++] = v;
                    }
                }
            }
            reached += nn;
            if (lv + 1 > DIAM) total += (lv + 1 - DIAM) * nn;
            int *tmp = cur; cur = nxt; nxt = tmp;
            fn = nn;
        }
        total += (N - reached) * UNREACH_W;
    }
    return total + PEN * dup;
}

static void save_best(void) {
    memcpy(bestS, dS, sizeof(int) * (size_t)NE);
    memcpy(bestJ, dJ, sizeof(int) * (size_t)NE);
}

int main(int argc, char **argv) {
    if (argc < 10) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    int gtype = atoi(argv[4]);
    int gm = atoi(argv[5]);
    int gk = atoi(argv[6]);
    int gr = atoi(argv[7]);
    uint64_t seed = strtoull(argv[8], NULL, 10);
    double slice = atof(argv[9]);

    if (DEG < 1 || DIAM < 1 || K < 1 || K > 4) {
        printf("0 0\n");
        return 0;
    }
    if (!build_group(gtype, gm, gk, gr)) {
        printf("0 0\n");
        return 0;
    }

    NE = DEG * K;
    N = 2 * K * NG;
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    dI = malloc(sizeof(int) * NE);
    dJ = malloc(sizeof(int) * NE);
    dS = malloc(sizeof(int) * NE);
    bestS = malloc(sizeof(int) * NE);
    bestJ = malloc(sizeof(int) * NE);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    vis = calloc((size_t)N, sizeof(uint32_t));
    int *p = malloc(sizeof(int) * K);
    if (!dI || !dJ || !dS || !bestS || !bestJ || !adj || !cnt || !fr || !nx || !vis || !p) {
        printf("0 0\n");
        return 0;
    }

    T0C = clock();
    int found = 0;
    int bestCost = BIGCOST;
    const int RL = 40000;

    while (!found && elapsed() < slice) {
        double T0;
        if (bestCost >= BIGCOST || rnd01() < 0.2) {
            for (int l = 0; l < DEG; l++) {
                for (int i = 0; i < K; i++) p[i] = i;
                for (int i = K - 1; i > 0; i--) {
                    int j = rndint(i + 1);
                    int t = p[i]; p[i] = p[j]; p[j] = t;
                }
                for (int i = 0; i < K; i++) {
                    dI[l * K + i] = i;
                    dJ[l * K + i] = p[i];
                }
            }
            for (int e = 0; e < NE; e++) dS[e] = rndint(NG);
            T0 = 2.0;
        } else {
            memcpy(dJ, bestJ, sizeof(int) * (size_t)NE);
            memcpy(dS, bestS, sizeof(int) * (size_t)NE);
            int kick = NE / 8 + 1;
            for (int q = 0; q < kick; q++) dS[rndint(NE)] = rndint(NG);
            T0 = 0.8;
        }

        int cur = cost_fn();
        if (cur < bestCost) { bestCost = cur; save_best(); }
        if (cur == 0) { found = 1; break; }

        int runBest = cur;
        int since = 0;
        for (int it = 0; it < RL; it++) {
            if ((it & 127) == 0 && elapsed() >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.05;
            if (K > 1 && rnd01() < 0.3) {
                int l = rndint(DEG);
                int i1 = rndint(K);
                int i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                int e1 = l * K + i1, e2 = l * K + i2;
                int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                }
            } else {
                int e = rndint(NE);
                int old = dS[e];
                int ns = rndint(NG);
                if (ns == old) continue;
                dS[e] = ns;
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    dS[e] = old;
                }
            }
            if (cur < bestCost) { bestCost = cur; save_best(); }
            if (cur < runBest) { runBest = cur; since = 0; }
            else if (++since > STAG) break;
            if (cur == 0) { found = 1; break; }
        }
    }

    if (found) {
        memcpy(dS, bestS, sizeof(int) * (size_t)NE);
        memcpy(dJ, bestJ, sizeof(int) * (size_t)NE);
        printf("%d %d\n", N, NE * NG);
        for (int e = 0; e < NE; e++) {
            for (int g = 0; g < NG; g++) {
                printf("%d %d\n", dI[e] * NG + g, (K + dJ[e]) * NG + TAB[g * NG + dS[e]]);
            }
        }
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: exact fallback, group sampling, search loop.
# ----------------------------------------------------------------------------

def _isprime(p):
    """True if p is a prime."""
    if p < 2:
        return False
    return all(p % q for q in range(2, int(math.isqrt(p)) + 1))


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (degree q + 1 <= d)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Pick a group with order about target. Returns (gtype, m, k, r, order), or None."""
    if rng.random() < 0.25:
        ps = [p for p in range(3, 120)
              if _isprime(p) and target <= p * (p - 1) <= 1.6 * target + 12]
        if ps:
            p = rng.choice(ps)
            return 1, p, 1, 1, p * (p - 1)
    n = target + rng.randrange(0, max(1, target // 12) + 1)
    divs = [x for x in range(1, n + 1) if n % x == 0]
    k = rng.choice(divs)
    m = n // k
    rs = [r for r in range(1, m + 1) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
    if not rs:
        return None
    return 0, m, k, rng.choice(rs), n


def _group_search(d, D, rng, best, deadline):
    """Repeatedly run the group-lift engine, aiming at a vertex count above the current best."""
    step = 0.01
    fails = 0
    while fails < 4:
        remaining = deadline - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(remaining, 10.0)
        K = rng.choice([1, 1, 1, 2, 2, 3])
        cur_n = best[0][0]
        target = max(2, -(-(cur_n + 2) // (2 * K)), math.ceil(cur_n * (1 + step) / (2 * K)))
        if target > 1500:
            break
        g = _sample_group(target, rng)
        if g is None:
            continue
        gtype, m, k, r, _ = g
        try:
            out = lib.run_c(
                GROUP_C_SOURCE,
                [d, D, K, gtype, m, k, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                timeout=slice_s + 6.0,
            )
        except RuntimeError:
            fails += 1
            continue
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        if n > best[0][0] and lib.is_valid(n, e, d, D):
            best[0] = (n, e)


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = t_start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = [lib.haar_graph(d, range(d))]

    def consider(cand):
        try:
            n, e = cand
            if n > best[0][0] and lib.is_valid(n, e, d, D):
                best[0] = (n, e)
        except Exception:
            pass

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg)
            if D == 3 and lib.is_prime_power(d - 1):
                n, e = best[0]
                if lib.is_valid(n, e, d, D):
                    return n, e

    if d >= 2 and D >= 3:
        try:
            _group_search(d, D, rng, best, deadline - 0.5)
        except Exception:
            pass

    n, e = best[0]
    if lib.is_valid(n, e, d, D):
        return n, e
    return lib.haar_graph(d, range(d))
