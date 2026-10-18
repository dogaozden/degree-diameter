import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over voltage lifts of bi-regular base graphs.
#
# The lift has 2K blocks of size g (A blocks 0..K-1, B blocks K..2K-1). A group
# G of order g acts on the left and preserves all edges. Layer l of the base
# graph is a permutation sg[l][i] of the K A-blocks onto the K B-blocks, with a
# voltage sv[l][i] in G. Edge: A(i,x) -- B(sg[l][i], x*sv[l][i]). Each vertex
# gets exactly one edge per layer, so the lift is d-regular and bipartite.
#
# Left-invariance means distance from (b,x) to any v equals distance from
# (b,e) to x^-1 v. So the cost is the sum over the 2K block identities of the
# number of unreached vertices within distance D, plus a penalty for parallel
# edges. Cost 0 gives a valid graph of order 2*K*g.
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

#define FAIL do { printf("0 0\n"); return 0; } while (0)

/* group: 0 = Z_p1, 1 = Z_p1 x|_{gp3} Z_gp2, 2 = Z_p1 x Z_p2 */
static int gtype, gp1, gp2, gp3, g;
static int *gpow;
static int K, d_, D_, N;
static int *sg, *sgi, *sv, *nbr, *vis, *qu;
static int stamp_ = 0;
static const long long PEN = 200;

static int gmul(int x, int y) {
    switch (gtype) {
    case 0: {
        int s = x + y;
        return s >= gp1 ? s - gp1 : s;
    }
    case 1: {
        int k = gp2, m = gp1;
        int a = x / k, b = x % k, c = y / k, dd = y % k;
        long long t = ((long long)a + (long long)gpow[b] * c) % m;
        return (int)(t * k + (b + dd) % k);
    }
    default: {
        int p2 = gp2;
        int a = x / p2, b = x % p2, c = y / p2, dd = y % p2;
        int aa = (a + c) % gp1;
        int bb = (b + dd) % p2;
        return aa * p2 + bb;
    }
    }
}

static int ginv(int x) {
    switch (gtype) {
    case 0:
        return x == 0 ? 0 : gp1 - x;
    case 1: {
        int k = gp2, m = gp1;
        int a = x / k, b = x % k;
        int nb = (k - b) % k;
        long long t = ((-(long long)gpow[nb] * a) % m + m) % m;
        return (int)(t * k + nb);
    }
    default: {
        int p2 = gp2;
        int a = x / p2, b = x % p2;
        return ((gp1 - a) % gp1) * p2 + (p2 - b) % p2;
    }
    }
}

static void build_nbr(void) {
    for (int i = 0; i < K; i++)
        for (int x = 0; x < g; x++) {
            int v = i * g + x;
            for (int l = 0; l < d_; l++) {
                int j = sg[l * K + i];
                nbr[v * d_ + l] = (K + j) * g + gmul(x, sv[l * K + i]);
            }
        }
    for (int j = 0; j < K; j++)
        for (int y = 0; y < g; y++) {
            int v = (K + j) * g + y;
            for (int l = 0; l < d_; l++) {
                int i = sgi[l * K + j];
                nbr[v * d_ + l] = i * g + gmul(y, ginv(sv[l * K + i]));
            }
        }
}

static long long eval_cost(void) {
    build_nbr();
    long long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = l + 1; l2 < d_; l2++)
                if (sg[l * K + i] == sg[l2 * K + i] && sv[l * K + i] == sv[l2 * K + i]) dup++;
    long long unreached = 0;
    for (int b = 0; b < 2 * K; b++) {
        stamp_++;
        int head = 0, tail = 0;
        int src = b * g;
        vis[src] = stamp_;
        qu[tail++] = src;
        for (int lev = 0; lev < D_ && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int v = qu[head++];
                for (int l = 0; l < d_; l++) {
                    int u = nbr[v * d_ + l];
                    if (vis[u] != stamp_) { vis[u] = stamp_; qu[tail++] = u; }
                }
            }
        }
        unreached += N - tail;
    }
    return unreached + PEN * dup;
}

int main(int argc, char **argv) {
    if (argc < 10) FAIL;
    gtype = atoi(argv[1]);
    gp1 = atoi(argv[2]);
    gp2 = atoi(argv[3]);
    gp3 = atoi(argv[4]);
    K = atoi(argv[5]);
    d_ = atoi(argv[6]);
    D_ = atoi(argv[7]);
    rs ^= (u64)strtoull(argv[8], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[9]);
    if (K < 1 || d_ < 1 || D_ < 1) FAIL;

    if (gtype == 0) {
        if (gp1 < 2) FAIL;
        g = gp1;
    } else if (gtype == 1) {
        if (gp1 < 2 || gp2 < 1) FAIL;
        g = gp1 * gp2;
        gpow = malloc(sizeof(int) * (size_t)gp2);
        long long p = 1 % gp1;
        for (int b = 0; b < gp2; b++) {
            gpow[b] = (int)p;
            p = p * gp3 % gp1;
        }
        if (p != 1 % gp1) FAIL;
    } else if (gtype == 2) {
        if (gp1 < 1 || gp2 < 1 || gp1 * gp2 < 2) FAIL;
        g = gp1 * gp2;
    } else {
        FAIL;
    }
    if ((long long)2 * K * g > 300000) FAIL;
    N = 2 * K * g;

    sg = malloc(sizeof(int) * (size_t)K * d_);
    sgi = malloc(sizeof(int) * (size_t)K * d_);
    sv = malloc(sizeof(int) * (size_t)K * d_);
    nbr = malloc(sizeof(int) * (size_t)N * d_);
    vis = calloc((size_t)N, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)N);
    if (!sg || !sgi || !sv || !nbr || !vis || !qu) FAIL;

    for (int l = 0; l < d_; l++) {
        int *p = sg + l * K;
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < K; i++) sgi[l * K + p[i]] = i;
        for (int i = 0; i < K; i++) sv[l * K + i] = rint_(g);
    }

    long long cost = eval_cost();
    clock_t c0 = clock();
    const double T0 = 20.0, T1 = 0.3;
    double el = 0.0, T = T0;
    long long it = 0;
    int found = (cost == 0);

    while (!found) {
        if ((it & 31) == 0) {
            el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= limit) break;
            T = T0 * pow(T1 / T0, el / limit);
        }
        it++;
        int l = rint_(d_);
        if (K >= 2 && (rnd() & 3) == 0) {
            int i1 = rint_(K), i2 = rint_(K - 1);
            if (i2 >= i1) i2++;
            int *s = sg + l * K, *si = sgi + l * K;
            int a = s[i1], b = s[i2];
            s[i1] = b; s[i2] = a; si[b] = i1; si[a] = i2;
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) cost = nc;
            else { s[i1] = a; s[i2] = b; si[a] = i1; si[b] = i2; }
        } else {
            int i = rint_(K), idx = l * K + i;
            int old = sv[idx], nv = rint_(g);
            if (nv == old) continue;
            sv[idx] = nv;
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) cost = nc;
            else sv[idx] = old;
        }
        if (cost == 0) found = 1;
    }

    if (!found) FAIL;
    build_nbr();
    long long M = (long long)K * g * d_;
    printf("%d %lld\n", N, M);
    for (int i = 0; i < K; i++)
        for (int x = 0; x < g; x++) {
            int v = i * g + x;
            for (int l = 0; l < d_; l++)
                printf("%d %d\n", v, nbr[v * d_ + l]);
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


def _random_group(glo, ghi, rng):
    """Random group spec (gtype, p1, p2, p3, order) with order in [glo, ghi], or None."""
    if glo > ghi:
        return None
    fam = rng.random()
    if fam < 0.35:
        lo = max(2, glo)
        if lo > ghi:
            return None
        m = rng.randint(lo, ghi)
        return (0, m, 0, 0, m)
    if fam < 0.6:
        a = rng.choice([2, 2, 3, 4, 5, 6, 8])
        blo = max(2, -(-glo // a))
        bhi = ghi // a
        if blo > bhi:
            return None
        b = rng.randint(blo, bhi)
        return (2, a, b, 0, a * b)
    k2 = rng.choice([2, 2, 3, 3, 4, 5, 6, 8])
    mlo = max(3, -(-glo // k2))
    mhi = ghi // k2
    if mlo > mhi:
        return None
    m = rng.randint(mlo, mhi)
    rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
    if not rs:
        return None
    r = rng.choice(rs)
    return (1, m, k2, r, m * k2)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 when d - 1 is a prime power (calibration case).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Main search: voltage lifts over varied groups, aiming just above the current best.
    deadline = t0 + max(0.5, min(time_limit - 5.0, 0.9 * time_limit))
    crashes = 0
    while crashes < 3:
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            break
        lo = best[0] + 1
        hi = int(best[0] * 1.15) + 12
        opts = [K for K in range(1, 7) if -(-lo // (2 * K)) <= hi // (2 * K)]
        if not opts:
            break
        K = rng.choice(opts)
        glo = -(-lo // (2 * K))
        ghi = hi // (2 * K)
        spec = None
        for _ in range(40):
            spec = _random_group(glo, ghi, rng)
            if spec is not None:
                break
        if spec is None:
            continue
        gtype, p1, p2, p3, _g = spec
        budget = min(8.0, max(2.0, remaining / 3.0), remaining - 1.0)
        try:
            out = lib.run_c(
                C_SOURCE,
                [gtype, p1, p2, p3, K, d, D, rng.randrange(1, 1 << 30), f"{budget:.2f}"],
                stdin_graph=None,
                timeout=budget + 10.0,
            )
            n, e = lib.parse_graph_text(out)
        except Exception:
            crashes += 1
            continue
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
