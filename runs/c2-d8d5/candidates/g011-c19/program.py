import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts of 2k base vertices.
#
# Vertices are (block b, group element g), b in 0..2k-1 (blocks < k are side A,
# blocks >= k are side B), coded as b*G + g. Group G = Z_m x| Z_k2 (element a*k2+b).
# Each of the d layers is a perfect matching between A-blocks and B-blocks:
# A-block i is matched to B-block layers[l][i] with voltage S[l][i], joining
# (i,g) to (j, g*s). Left multiplication by G is an automorphism, so the
# diameter condition only needs checking from the identity of each block.
# Reachability is tracked as a 64-bit mask of block identities per vertex.
# Cost = (block, vertex) pairs at distance > D, plus a penalty per duplicate edge.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

#define MAXD 16
#define MAXK 32
#define MAXG 3000
#define MAXN 100000

static int d_, D_, k_, G_, N_;
static int *mulT, *nbr;
static int layers[MAXD][MAXK];
static int S[MAXD][MAXK];
static u64 *cur, *nxt;

static void build_group(int m, int kk, int r) {
    int G = G_;
    long long *powr = malloc(sizeof(long long) * (size_t)kk);
    for (int b = 0; b < kk; b++)
        powr[b] = (b == 0) ? (1 % m) : ((powr[b - 1] * r) % m);
    for (int x = 0; x < G; x++) {
        int a = x / kk, b = x % kk;
        for (int y = 0; y < G; y++) {
            int c = y / kk, dd = y % kk;
            long long aa = ((long long)a + powr[b] * c) % m;
            mulT[x * G + y] = (int)(aa * kk + (b + dd) % kk);
        }
    }
    free(powr);
}

static void shuffle_perm(int *p, int n) {
    for (int i = 0; i < n; i++) p[i] = i;
    for (int i = n - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = p[i]; p[i] = p[j]; p[j] = t;
    }
}

static void build_nbr(void) {
    int d = d_, G = G_, k = k_;
    for (int v = 0; v < N_ * d; v++) nbr[v] = -1;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) {
            int j = layers[l][i], s = S[l][i];
            for (int g = 0; g < G; g++) {
                int u = i * G + g;
                int v = (k + j) * G + mulT[g * G + s];
                nbr[u * d + l] = v;
                nbr[v * d + l] = u;
            }
        }
}

static int dupcount(void) {
    int ki[MAXD * MAXK], kj[MAXD * MAXK], ks[MAXD * MAXK];
    int n = 0;
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < k_; i++) {
            ki[n] = i; kj[n] = layers[l][i]; ks[n] = S[l][i]; n++;
        }
    int c = 0;
    for (int a = 0; a < n; a++)
        for (int b = a + 1; b < n; b++)
            if (ki[a] == ki[b] && kj[a] == kj[b] && ks[a] == ks[b]) c++;
    return c;
}

/* Number of (block identity, vertex) pairs at distance > D_. Zero means valid. */
static long long unreached(void) {
    int N = N_, d = d_, k2 = 2 * k_;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < k2; b++) cur[(size_t)b * G_] |= 1ULL << b;
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[v * d + l]];
            nxt[v] = x;
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) bad += k2 - __builtin_popcountll(cur[v]);
    return bad;
}

static long long total_cost(void) {
    return unreached() + 1000LL * (long long)dupcount();
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]), D = atoi(argv[2]), k = atoi(argv[3]);
    int m = atoi(argv[4]), k2 = atoi(argv[5]), r = atoi(argv[6]);
    rs ^= (u64)strtoull(argv[7], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[8]);
    if (d < 1 || d > MAXD || D < 1 || k < 1 || k > MAXK || m < 1 || k2 < 1) {
        printf("0 0\n"); return 0;
    }
    long long G = (long long)m * k2;
    if (G > MAXG || 2LL * k * G > MAXN || G < 2) { printf("0 0\n"); return 0; }
    d_ = d; D_ = D; k_ = k; G_ = (int)G; N_ = (int)(2LL * k * G);
    int N = N_;
    mulT = malloc(sizeof(int) * (size_t)(G * G));
    nbr = malloc(sizeof(int) * (size_t)N * d);
    cur = malloc(sizeof(u64) * (size_t)N);
    nxt = malloc(sizeof(u64) * (size_t)N);
    if (!mulT || !nbr || !cur || !nxt) { printf("0 0\n"); return 0; }
    build_group(m, k2, r);

    for (int l = 0; l < d; l++) {
        shuffle_perm(layers[l], k);
        for (int i = 0; i < k; i++) S[l][i] = rint_(G_);
    }
    build_nbr();
    long long cost = total_cost();

    clock_t c0 = clock();
    const double T0 = 30.0, T1 = 0.3;
    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);

        int l = rint_(d);
        int swapmove = (k >= 2 && rdbl() < 0.3);
        int i1 = rint_(k), i2 = 0, old = 0, nw = 0;
        if (swapmove) {
            i2 = rint_(k - 1);
            if (i2 >= i1) i2++;
            int t = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = t;
        } else {
            old = S[l][i1];
            nw = rint_(G_);
            if (nw == old) continue;
            S[l][i1] = nw;
        }
        build_nbr();
        long long nc = total_cost();
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
        } else {
            if (swapmove) {
                int t = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = t;
            } else {
                S[l][i1] = old;
            }
            build_nbr();
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", N, N * d / 2);
    for (int u = 0; u < N; u++)
        for (int l = 0; l < d; l++) {
            int v = nbr[u * d + l];
            if (v > u) printf("%d %d\n", u, v);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 6, 8, 10, 12, 16, 18, 20, 24])
        m = max(2, -(-target // k2))
        if k2 == 1:
            return m, 1, 1
        r = None
        if m > 2:
            for _ in range(80):
                c = rng.randrange(2, m)
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
        if r is None:
            continue
        return m, k2, r
    return None


def _run_lift_search(d, D, k, m, k2, r, seed, budget):
    """Run the C annealer for one bi-Cayley configuration; returns (n, edges) or (0, [])."""
    out = lib.run_c(C_SOURCE, [d, D, k, m, k2, r, seed, f"{budget:.2f}"],
                    stdin_graph=None, timeout=budget + 10.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    reserve = max(3.0, 0.08 * time_limit)
    deadline = t0 + time_limit - reserve

    KS = (2, 3, 4, 5, 6)
    trials = {k: 0 for k in KS}
    wins = {k: 0 for k in KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(KS)
        return max(KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    fails = 0
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            break
        budget = min(remaining - 1.0, max(3.0, 0.25 * remaining))
        if budget < 1.0:
            break

        k = pick_k()
        base = best[0] // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 16 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G = m * k2
        if 2 * k * G <= best[0] or G > 3000 or 2 * k * G > 100000:
            continue

        trials[k] += 1
        try:
            n, e = _run_lift_search(d, D, k, m, k2, r, rng.randrange(1, 1 << 30), budget)
        except Exception:
            fails += 1
            if fails >= 3:
                break
            continue
        if n > 0:
            wins[k] += 1
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
