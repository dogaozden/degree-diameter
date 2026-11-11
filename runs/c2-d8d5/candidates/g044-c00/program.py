import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: degree-preserving annealer over lifts of a general base bipartite
# multigraph. Base has k A-blocks and k B-blocks, each of base degree d, given
# by E = k*d darts (ea, eb, ev). Dart j with voltage ev[j] in G = Z_m x| Z_k2
# joins A_{ea} x to B_{eb} (x * ev). Moves: swap the B-endpoints of two darts
# (preserves every block degree, so this is NOT restricted to per-layer
# permutations) or change one voltage. Left multiplication by G is an
# automorphism, so cost = unreached ordered pairs from the 2k block
# representatives plus a penalty for repeated darts.
# ----------------------------------------------------------------------------

C_DART = r"""
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

static int d_, D_, k_, m_, k2_, G_, N_, E_;
static int *ea, *eb, *ev, *pw, *nbr, *fill, *queue_, *stamp;
static int curstamp = 0;

static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_;
    int c = y / k2_, e = y % k2_;
    int a2 = (a + (int)((long long)pw[b] * c % m_)) % m_;
    int b2 = (b + e) % k2_;
    return a2 * k2_ + b2;
}

static void build_nbr(void) {
    int N = N_, d = d_;
    memset(fill, 0, sizeof(int) * (size_t)N);
    for (int j = 0; j < E_; j++) {
        int i = ea[j], t = eb[j], s = ev[j];
        for (int x = 0; x < G_; x++) {
            int y = gmul(x, s);
            int a = i * G_ + x;
            int b = (k_ + t) * G_ + y;
            nbr[(size_t)a * d + fill[a]++] = b;
            nbr[(size_t)b * d + fill[b]++] = a;
        }
    }
}

static long long eval_cost(void) {
    int N = N_, d = d_;
    long long dups = 0;
    for (int j1 = 0; j1 < E_; j1++)
        for (int j2 = j1 + 1; j2 < E_; j2++)
            if (ea[j1] == ea[j2] && eb[j1] == eb[j2] && ev[j1] == ev[j2]) dups++;
    build_nbr();
    long long cost = 0;
    for (int b = 0; b < 2 * k_; b++) {
        int src = b * G_;
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

static void print_graph(void) {
    int N = N_;
    long long *pairs = malloc(sizeof(long long) * (size_t)E_ * (size_t)G_);
    if (!pairs) { printf("0 0\n"); return; }
    int cnt = 0;
    for (int j = 0; j < E_; j++)
        for (int x = 0; x < G_; x++) {
            int a = ea[j] * G_ + x;
            int b = (k_ + eb[j]) * G_ + gmul(x, ev[j]);
            if (a > b) { int t = a; a = b; b = t; }
            pairs[cnt++] = (long long)a * N + b;
        }
    qsort(pairs, (size_t)cnt, sizeof(long long), cmp_ll);
    int uniq = 0;
    for (int i = 0; i < cnt; i++)
        if (i == 0 || pairs[i] != pairs[i - 1]) pairs[uniq++] = pairs[i];
    printf("%d %d\n", N, uniq);
    for (int i = 0; i < uniq; i++)
        printf("%lld %lld\n", pairs[i] / N, pairs[i] % N);
    free(pairs);
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
    if (d_ < 1 || d_ > 32 || D_ < 1 || k_ < 1 || k_ > 16 || m_ < 2 || k2_ < 1) {
        printf("0 0\n");
        return 0;
    }
    r %= m_;
    if (r < 0) r += m_;
    G_ = m_ * k2_;
    if ((long long)G_ * 2 * k_ > 200000) { printf("0 0\n"); return 0; }
    N_ = 2 * k_ * G_;
    E_ = k_ * d_;

    pw = malloc(sizeof(int) * (size_t)(k2_ + 1));
    if (!pw) { printf("0 0\n"); return 0; }
    pw[0] = 1 % m_;
    for (int b = 1; b <= k2_; b++) pw[b] = (int)((long long)pw[b - 1] * r % m_);
    if (pw[k2_] != 1 % m_) { printf("0 0\n"); return 0; }

    ea = malloc(sizeof(int) * (size_t)E_);
    eb = malloc(sizeof(int) * (size_t)E_);
    ev = malloc(sizeof(int) * (size_t)E_);
    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    fill = malloc(sizeof(int) * (size_t)N_);
    queue_ = malloc(sizeof(int) * (size_t)N_);
    stamp = calloc((size_t)N_, sizeof(int));
    if (!ea || !eb || !ev || !nbr || !fill || !queue_ || !stamp) { printf("0 0\n"); return 0; }

    for (int j = 0; j < E_; j++) { ea[j] = j / d_; eb[j] = j / d_; }
    for (int j = E_ - 1; j > 0; j--) {
        int q = rint_(j + 1);
        int t = eb[j]; eb[j] = eb[q]; eb[q] = t;
    }
    for (int j = 0; j < E_; j++) ev[j] = rint_(G_);

    long long cost = eval_cost();
    const double T0 = 6.0, T1 = 0.15;
    clock_t c0 = clock();
    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);
        if (rint_(2) == 0) {
            int j1 = rint_(E_), j2 = rint_(E_);
            if (eb[j1] == eb[j2]) continue;
            int t = eb[j1]; eb[j1] = eb[j2]; eb[j2] = t;
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                t = eb[j1]; eb[j1] = eb[j2]; eb[j2] = t;
            }
        } else {
            int j = rint_(E_);
            int old = ev[j];
            int nv = rint_(G_);
            if (nv == old) continue;
            ev[j] = nv;
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                ev[j] = old;
            }
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }
    print_graph();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4, 5, 6)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _pick_k(rng, stats):
    """Bandit choice of base-block count k (mostly exploit, sometimes explore)."""
    if rng.random() < 0.2:
        return rng.choice(_KS)
    return max(_KS, key=lambda k: (stats[k][1] + 1) / (stats[k][0] + 2) + 0.02 * rng.random())


def _dart_engine(d, D, k, m, k2, r, seconds, seed):
    """Run the C dart-lift annealer for one group; returns (n, edges) or (0, [])."""
    out = lib.run_c(C_DART, [d, D, seed, f"{seconds:.2f}", k, m, k2, r],
                    stdin_graph=None, timeout=seconds + 10.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2), or a single edge if that fails.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])

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

    # Search: degree-preserving dart lifts over semidirect groups, adaptive target.
    budget_end = t0 + 0.85 * time_limit
    stats = {k: [0, 0] for k in _KS}
    frac = 0.06
    while True:
        remaining = budget_end - time.monotonic()
        if remaining < 1.5:
            break
        k = _pick_k(rng, stats)
        target_n = int(best[0] * (1.0 + frac)) + 2
        g = _sample_group(max(2, -(-target_n // (2 * k))), rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best[0]:
            continue
        stats[k][0] += 1
        slice_s = min(6.0, max(1.5, 0.3 * remaining))
        try:
            n_, e_ = _dart_engine(d, D, k, m, k2, r, slice_s, rng.randrange(1, 1 << 30))
        except Exception:
            n_, e_ = 0, []
        if n_ > best[0] and lib.is_valid(n_, e_, d, D):
            stats[k][1] += 1
            best = (n_, e_)
            frac = min(0.25, frac * 1.3)
        else:
            frac = max(0.003, frac * 0.85)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
        if not lib.is_valid(best[0], best[1], d, D):
            best = (2, [(0, 1)])
    return best
