import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: table-driven bi-Cayley lift annealer.
#
# The group G is supplied as a multiplication table on stdin, encoded as a
# graph text: header "G G*G", then pairs (x*G+y, x*y). This allows any finite
# group (semidirect products, direct products, ...), not only the cyclic-based
# family used before.
#
# Vertices: A_i x and B_t x for i, t in [0, k) and x in G (index i*G+x, (k+t)*G+x).
# Layer l gives perm[l][i] and vol[l][i]:  A_i x ~ B_{perm[l][i]} (x * vol[l][i]).
# Every vertex gets exactly one neighbour per layer, so the graph is d-regular
# and bipartite. Left multiplication by G is an automorphism, so validity
# reduces to the 2k block representatives: cost = unreached vertices within
# distance D of those representatives, plus a penalty for repeated darts.
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

static int d_, D_, k_, G_, N_;
static int *mul_, *perm, *vol, *nbr, *queue_, *stamp;
static int curstamp = 0;

static void build_nbr(void) {
    int k = k_, G = G_, d = d_;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) {
            int t = perm[l * k + i], s = vol[l * k + i];
            for (int x = 0; x < G; x++) {
                int y = mul_[x * G + s];
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
    build_nbr();
    long long cost = 0;
    for (int b = 0; b < 2 * k; b++) {
        int src = b * G;
        curstamp++;
        int h = 0, t = 0;
        queue_[t++] = src;
        stamp[src] = curstamp;
        int dist = 0;
        while (h < t && dist < D_) {
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
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    k_ = atoi(argv[5]);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { printf("0 0\n"); return 0; }
    G_ = n0;
    if (d_ < 1 || d_ > 64 || D_ < 1 || k_ < 1 || G_ < 2 || G_ > 3000) { printf("0 0\n"); return 0; }
    if ((long long)m0 != (long long)G_ * G_) { printf("0 0\n"); return 0; }
    if ((long long)G_ * 2 * k_ > 200000) { printf("0 0\n"); return 0; }
    N_ = 2 * k_ * G_;

    mul_ = malloc(sizeof(int) * (size_t)G_ * G_);
    perm = malloc(sizeof(int) * (size_t)d_ * k_);
    vol = malloc(sizeof(int) * (size_t)d_ * k_);
    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    queue_ = malloc(sizeof(int) * (size_t)N_);
    stamp = calloc((size_t)N_, sizeof(int));
    if (!mul_ || !perm || !vol || !nbr || !queue_ || !stamp) { printf("0 0\n"); return 0; }

    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || u >= G_ * G_ || v < 0 || v >= G_) { printf("0 0\n"); return 0; }
        mul_[u] = v;
    }

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

    long long cost = eval_cost();
    const double T0 = 6.0, T1 = 0.15;
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
            int t = *p1; *p1 = *p2; *p2 = t;
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                t = *p1; *p1 = *p2; *p2 = t;
            }
        } else {
            int old = vol[l * k_ + i];
            int nv = rint_(G_);
            if (nv == old) continue;
            vol[l * k_ + i] = nv;
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                vol[l * k_ + i] = old;
            }
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }
    build_nbr();

    long long *pairs = malloc(sizeof(long long) * (size_t)N_ * d_);
    int cnt = 0;
    for (int v = 0; v < N_; v++)
        for (int l = 0; l < d_; l++) {
            int u = nbr[v * d_ + l];
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
# Python constructions and glue.
# ----------------------------------------------------------------------------

_KS = (3, 4, 5, 6)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _dir_mul(a, b):
    """Multiplication in Z_a x Z_b, element x = x1*b + y1."""
    def mul(x, y):
        x1, y1 = divmod(x, b)
        x2, y2 = divmod(y, b)
        return ((x1 + x2) % a) * b + (y1 + y2) % b
    return mul


def _sample_group(G, rng):
    """Return (order, mul) for a group of order G (direct or semidirect product), or None."""
    divs = [x for x in range(1, G + 1) if G % x == 0]
    for _ in range(100):
        if rng.random() < 0.35:
            a = rng.choice(divs)
            b = G // a
            if a >= 2 and b >= 2:
                return G, _dir_mul(a, b)
        k2 = rng.choice(divs)
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(80):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _table_edges(order, mul):
    """Encode the multiplication table as graph-format pairs (x*order+y, x*y) for the C engine."""
    return [(x * order + y, mul(x, y)) for x in range(order) for y in range(order)]


def _pick_k(rng, stats):
    """Bandit choice of base-block count k (mostly exploit, sometimes explore)."""
    if rng.random() < 0.25:
        return rng.choice(_KS)
    return max(_KS, key=lambda k: (stats[k][1] + 1) / (stats[k][0] + 2) + 0.02 * rng.random())


def _lift_in_c(d, D, k, G, edges, seconds, seed):
    """Run the C table-driven lift annealer; returns (n, edges) or (0, [])."""
    out = lib.run_c(C_LIFT, [d, D, seed, f"{seconds:.2f}", k],
                    stdin_graph=(G, edges), timeout=seconds + 15.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

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

    if d < 3:
        return best

    # Lift annealing over a varied family of groups, with an adaptive target size.
    lift_end = t0 + 0.85 * time_limit
    stats = {k: [0, 0] for k in _KS}   # [trials, wins]
    frac = 0.04                        # target = best * (1 + frac)
    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 1.5:
            break
        k = _pick_k(rng, stats)
        target_n = int(best[0] * (1.0 + frac)) + 2
        G_min = max(2, -(-target_n // (2 * k)))
        G = G_min + rng.randrange(0, 8)
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        if 2 * k * order <= best[0]:
            continue
        edges = _table_edges(order, mul)
        stats[k][0] += 1
        slice_s = min(10.0, max(2.0, 0.3 * remaining))
        try:
            n_, e_ = _lift_in_c(d, D, k, order, edges, slice_s, rng.randrange(1, 1 << 30))
        except (RuntimeError, ValueError):
            n_, e_ = 0, []
        if n_ > best[0] and lib.is_valid(n_, e_, d, D):
            stats[k][1] += 1
            best = (n_, e_)
            frac = min(0.25, frac * 1.3)
        else:
            frac = max(0.003, frac * 0.85)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
