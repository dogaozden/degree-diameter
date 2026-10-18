import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lift annealer over a semidirect product Z_m x|_r Z_k2.
#
# Changes from the parent's lift engine:
#   * group multiplication is a precomputed table, so each move is cheap;
#   * a move rebuilds only the touched layer instead of the whole graph;
#   * the optimisation is restarted from scratch per call, and the Python
#     side hunts a target order slightly above the best valid graph.
#
# Vertices: A_i x = i*G + x and B_t x = (k+t)*G + x.
# Layer l sends A_i x to B_{perm[l][i]} (x * vol[l][i]). Left multiplication
# by G is an automorphism, so only the 2k block representatives are checked
# for reach within D.
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, m_, k2_, G_, N_;
static int *perm, *vol, *nbr, *pw, *mt, *queue_, *stamp;
static int curstamp = 0;

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static void build_layer(int l) {
    int k = k_, G = G_, d = d_;
    for (int i = 0; i < k; i++) {
        int t = perm[l * k + i], s = vol[l * k + i];
        for (int x = 0; x < G; x++) {
            int y = mt[x * G + s];
            int a = i * G + x, b = (k + t) * G + y;
            nbr[(size_t)a * d + l] = b;
            nbr[(size_t)b * d + l] = a;
        }
    }
}

static long long eval_cost(void) {
    int k = k_, d = d_, G = G_, N = N_;
    long long dups = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1 * k + i] == perm[l2 * k + i] && vol[l1 * k + i] == vol[l2 * k + i])
                    dups++;
    long long cost = 0;
    for (int b = 0; b < 2 * k; b++) {
        int src = b * G;
        curstamp++;
        int h = 0, t = 0;
        queue_[t++] = src;
        stamp[src] = curstamp;
        int dist = 0;
        while (h < t && dist < D_ && t < N) {
            int end = t;
            while (h < end) {
                int v = queue_[h++];
                const int *nv = nbr + (size_t)v * d;
                for (int l = 0; l < d; l++) {
                    int u = nv[l];
                    if (stamp[u] != curstamp) {
                        stamp[u] = curstamp;
                        queue_[t++] = u;
                    }
                }
            }
            dist++;
        }
        cost += N - t;
    }
    return cost + 50 * dups;
}

static int cmp_ll(const void *a, const void *b) {
    long long x = *(const long long *)a, y = *(const long long *)b;
    return (x > y) - (x < y);
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    k_ = atoi(argv[5]);
    m_ = atoi(argv[6]);
    k2_ = atoi(argv[7]);
    int r = atoi(argv[8]);
    if (d_ < 1 || d_ > 64 || D_ < 1 || k_ < 1 || k_ > 64 || m_ < 2 || k2_ < 1) {
        printf("0 0\n");
        return 0;
    }
    G_ = m_ * k2_;
    if (G_ > 2000 || (long long)2 * k_ * G_ > 60000) { printf("0 0\n"); return 0; }
    N_ = 2 * k_ * G_;
    r = ((r % m_) + m_) % m_;
    if (gcd_(r, m_) != 1) { printf("0 0\n"); return 0; }

    pw = malloc(sizeof(int) * (size_t)(k2_ + 1));
    pw[0] = 1 % m_;
    for (int b = 1; b <= k2_; b++) pw[b] = (int)((long long)pw[b - 1] * r % m_);
    if (pw[k2_] != 1 % m_) { printf("0 0\n"); return 0; }

    /* Multiplication table of (a,b)(c,e) = (a + r^b c, b + e), element a*k2+b. */
    mt = malloc(sizeof(int) * (size_t)G_ * G_);
    for (int x = 0; x < G_; x++) {
        int a = x / k2_, b = x % k2_;
        for (int y = 0; y < G_; y++) {
            int c = y / k2_, e = y % k2_;
            int a2 = (int)((a + (long long)pw[b] * c) % m_);
            int b2 = (b + e) % k2_;
            mt[x * G_ + y] = a2 * k2_ + b2;
        }
    }

    perm = malloc(sizeof(int) * (size_t)d_ * k_);
    vol = malloc(sizeof(int) * (size_t)d_ * k_);
    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    queue_ = malloc(sizeof(int) * (size_t)N_);
    stamp = calloc((size_t)N_, sizeof(int));
    if (!perm || !vol || !nbr || !queue_ || !stamp) { printf("0 0\n"); return 0; }

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) perm[l * k_ + i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[l * k_ + i];
            perm[l * k_ + i] = perm[l * k_ + j];
            perm[l * k_ + j] = t;
        }
        for (int i = 0; i < k_; i++) vol[l * k_ + i] = rint_(G_);
    }
    for (int l = 0; l < d_; l++) build_layer(l);

    long long cost = eval_cost();
    const double T0 = 4.0, T1 = 0.1;
    clock_t c0 = clock();
    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);
        int l = rint_(d_), i = rint_(k_);
        if (k_ >= 2 && rint_(3) == 0) {
            int i2 = rint_(k_ - 1);
            if (i2 >= i) i2++;
            int *p1 = &perm[l * k_ + i], *p2 = &perm[l * k_ + i2];
            int tmp = *p1; *p1 = *p2; *p2 = tmp;
            build_layer(l);
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                tmp = *p1; *p1 = *p2; *p2 = tmp;
                build_layer(l);
            }
        } else {
            int old = vol[l * k_ + i];
            int nv = rint_(G_);
            if (nv == old) continue;
            vol[l * k_ + i] = nv;
            build_layer(l);
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                vol[l * k_ + i] = old;
                build_layer(l);
            }
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }

    /* nbr matches the accepted state, which has cost 0. */
    long long *pairs = malloc(sizeof(long long) * (size_t)N_ * d_);
    int cnt = 0;
    for (int v = 0; v < N_; v++)
        for (int l = 0; l < d_; l++) {
            int u = nbr[(size_t)v * d_ + l];
            if (u > v) pairs[cnt++] = (long long)v * N_ + u;
        }
    qsort(pairs, (size_t)cnt, sizeof(long long), cmp_ll);
    int uniq = 0;
    for (int i = 0; i < cnt; i++)
        if (i == 0 || pairs[i] != pairs[i - 1]) pairs[uniq++] = pairs[i];
    printf("%d %d\n", N_, uniq);
    for (int i = 0; i < uniq; i++)
        printf("%lld %lld\n", pairs[i] / N_, pairs[i] % N_);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python: constructions and the target-order search loop.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4, 5, 6, 7, 8, 10, 12)
_GMAX = 2000
_GROUP_CACHE = {}


def _group_options(G):
    """All semidirect descriptors (m, k2, r) with m*k2 = G, cached per G.

    k2 = 1 gives the cyclic group; r = 1 gives the direct product.
    """
    if G in _GROUP_CACHE:
        return _GROUP_CACHE[G]
    opts = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            opts.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                opts.append((m, k2, r))
    _GROUP_CACHE[G] = opts
    return opts


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _pick_k(rng, cand, stats):
    """Bandit choice of block count k: mostly exploit, sometimes explore."""
    if rng.random() < 0.25:
        return rng.choice(cand)
    return max(cand, key=lambda k: (stats[k][1] + 1) / (stats[k][0] + 2) + 0.02 * rng.random())


def _lift_in_c(d, D, k, G, rng, seconds, seed):
    """Run the C lift annealer for a random group of order G; returns (n, edges) or (0, [])."""
    m, k2, r = rng.choice(_group_options(G))
    out = lib.run_c(C_LIFT, [d, D, seed, f"{seconds:.2f}", k, m, k2, r],
                    stdin_graph=None, timeout=seconds + 15.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best  # exact Moore-type construction: calibration case
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    # Target search: repeatedly aim for a bi-Cayley lift of order 2*k*G just
    # above the current best. Successes raise the bar; failures are cheap.
    end = t0 + 0.9 * time_limit - 1.5
    stats = {k: [0, 0] for k in _KS}
    while True:
        remaining = end - time.monotonic()
        if remaining < 2.0:
            break
        n_best = best[0]
        cand = [k for k in _KS if n_best // (2 * k) + 1 <= _GMAX]
        if not cand:
            break
        k = _pick_k(rng, cand, stats)
        Gmin = n_best // (2 * k) + 1
        if rng.random() < 0.6:
            G = Gmin
        else:
            G = min(_GMAX, Gmin + rng.randint(1, max(2, Gmin // 30)))
        slice_s = min(12.0, max(3.0, 0.3 * remaining))
        slice_s = min(slice_s, remaining - 1.0)
        stats[k][0] += 1
        try:
            n_, e_ = _lift_in_c(d, D, k, G, rng, slice_s, rng.randrange(1, 1 << 30))
        except RuntimeError:
            n_, e_ = 0, []
        if n_ > best[0] and lib.is_valid(n_, e_, d, D):
            stats[k][1] += 1
            best = (n_, e_)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
