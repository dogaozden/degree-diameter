import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: tabu-guided bi-Cayley lift search over Z_m x| Z_k2.
#
# This replaces the earlier simulated-annealing lift and toggle engines with a
# different search. Each iteration samples several candidate moves (retarget
# one dart's voltage, or swap two block-images within one layer), evaluates
# each exactly, and applies the best non-tabu one. Aspiration allows a tabu
# move that beats the best cost seen so far. Stagnation triggers a random kick.
#
# Vertices: A_i x and B_t x, i, t in [0, k), x in G. Index A_i x = i*G + x and
# B_t x = (k+t)*G + x. Layer l sends A_i x to B_{perm[l][i]} (x * vol[l][i]).
# Every vertex has exactly one neighbour per layer, so the graph is d-regular
# and bipartite. Left multiplication by G is an automorphism, so validity is
# checked from the 2k block representatives: the cost is the number of vertices
# not reached within D steps, plus a penalty for repeated darts.
# ----------------------------------------------------------------------------

C_TABU = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#include <limits.h>

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static int d_, D_, k_, m_, k2_, G_, N_;
static int *perm, *vol, *nbr, *pw, *queue_, *stamp;
static long long *tabu;
static int curstamp = 0;

static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_;
    int c = y / k2_, e = y % k2_;
    int a2 = (a + (pw[b] * c) % m_) % m_;
    int b2 = (b + e) % k2_;
    return a2 * k2_ + b2;
}

static void set_dart(int l, int i) {
    int k = k_, G = G_, d = d_;
    int t = perm[l * k + i], s = vol[l * k + i];
    for (int x = 0; x < G; x++) {
        int y = gmul(x, s);
        int a = i * G + x, b = (k + t) * G + y;
        nbr[a * d + l] = b;
        nbr[b * d + l] = a;
    }
}

static void set_all_darts(void) {
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < k_; i++) set_dart(l, i);
}

static long long eval_cost(void) {
    int k = k_, d = d_, D = D_, N = N_, G = G_;
    long long dups = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1 * k + i] == perm[l2 * k + i] && vol[l1 * k + i] == vol[l2 * k + i])
                    dups++;
    if (curstamp >= 1000000000) {
        memset(stamp, 0, sizeof(int) * (size_t)N);
        curstamp = 0;
    }
    long long cost = 0;
    for (int b = 0; b < 2 * k; b++) {
        int src = b * G;
        curstamp++;
        int h = 0, t = 0;
        queue_[t++] = src;
        stamp[src] = curstamp;
        int dist = 0;
        while (h < t && dist < D) {
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
    int cands = argc > 9 ? atoi(argv[9]) : 16;
    if (d_ < 1 || d_ > 64 || D_ < 1 || k_ < 1 || m_ < 2 || k2_ < 1 || cands < 1) {
        printf("0 0\n");
        return 0;
    }
    r %= m_;
    if (r < 0) r += m_;
    G_ = m_ * k2_;
    if ((long long)G_ * 2 * k_ > 200000) { printf("0 0\n"); return 0; }
    N_ = 2 * k_ * G_;

    pw = malloc(sizeof(int) * (size_t)(k2_ + 1));
    pw[0] = 1 % m_;
    for (int b = 1; b <= k2_; b++) pw[b] = (int)((long long)pw[b - 1] * r % m_);
    if (pw[k2_] != 1 % m_) { printf("0 0\n"); return 0; }

    perm = malloc(sizeof(int) * (size_t)d_ * k_);
    vol = malloc(sizeof(int) * (size_t)d_ * k_);
    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    queue_ = malloc(sizeof(int) * (size_t)N_);
    stamp = calloc((size_t)N_, sizeof(int));
    tabu = calloc((size_t)d_ * k_, sizeof(long long));
    if (!perm || !vol || !nbr || !queue_ || !stamp || !tabu) { printf("0 0\n"); return 0; }

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

    set_all_darts();
    long long cost = eval_cost();
    long long bestSeen = cost;
    int stall = 0;
    const int stall_lim = 150;
    long long it = 0;
    clock_t c0 = clock();

    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        it++;

        long long bc = LLONG_MAX;
        int mt = -1, ml = -1, mi = -1, mi2 = -1, mnv = 0;
        for (int c = 0; c < cands; c++) {
            if (k_ >= 2 && rint_(3) == 0) {
                int l = rint_(d_), i = rint_(k_);
                int i2 = rint_(k_ - 1);
                if (i2 >= i) i2++;
                int *p1 = &perm[l * k_ + i], *p2 = &perm[l * k_ + i2];
                int tt = *p1; *p1 = *p2; *p2 = tt;
                set_dart(l, i);
                set_dart(l, i2);
                long long nc = eval_cost();
                tt = *p1; *p1 = *p2; *p2 = tt;
                set_dart(l, i);
                set_dart(l, i2);
                int isT = (tabu[l * k_ + i] > it) || (tabu[l * k_ + i2] > it);
                if ((!isT || nc < bestSeen) && nc < bc) {
                    bc = nc; mt = 1; ml = l; mi = i; mi2 = i2;
                }
            } else {
                int l = rint_(d_), i = rint_(k_);
                int old = vol[l * k_ + i];
                int nv = rint_(G_);
                if (nv == old) continue;
                vol[l * k_ + i] = nv;
                set_dart(l, i);
                long long nc = eval_cost();
                vol[l * k_ + i] = old;
                set_dart(l, i);
                int isT = tabu[l * k_ + i] > it;
                if ((!isT || nc < bestSeen) && nc < bc) {
                    bc = nc; mt = 0; ml = l; mi = i; mnv = nv;
                }
            }
        }

        if (mt < 0) {
            for (int p = 0; p < 3; p++) {
                int l = rint_(d_), i = rint_(k_);
                vol[l * k_ + i] = rint_(G_);
            }
            set_all_darts();
            cost = eval_cost();
            continue;
        }

        if (mt == 0) {
            vol[ml * k_ + mi] = mnv;
            set_dart(ml, mi);
            tabu[ml * k_ + mi] = it + 7 + rint_(8);
        } else {
            int *p1 = &perm[ml * k_ + mi], *p2 = &perm[ml * k_ + mi2];
            int tt = *p1; *p1 = *p2; *p2 = tt;
            set_dart(ml, mi);
            set_dart(ml, mi2);
            long long tn = it + 7 + rint_(8);
            tabu[ml * k_ + mi] = tn;
            tabu[ml * k_ + mi2] = tn;
        }
        cost = bc;

        if (cost < bestSeen) { bestSeen = cost; stall = 0; }
        else stall++;

        if (stall > stall_lim && cost > 0) {
            for (int p = 0; p < 4; p++) {
                int l = rint_(d_), i = rint_(k_);
                vol[l * k_ + i] = rint_(G_);
                set_dart(l, i);
            }
            cost = eval_cost();
            bestSeen = cost;
            stall = 0;
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }

    /* nbr matches the current state: cost == 0 was just evaluated after set_dart. */
    long long *pairs = malloc(sizeof(long long) * (size_t)N_ * d_);
    if (!pairs) { printf("0 0\n"); return 0; }
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
    """Bandit choice of block count k (mostly exploit, sometimes explore)."""
    if rng.random() < 0.2:
        return rng.choice(_KS)
    return max(_KS, key=lambda k: (stats[k][1] + 1) / (stats[k][0] + 2) + 0.02 * rng.random())


def _tabu_in_c(d, D, k, m, k2, r, seconds, seed, cands):
    """Run the C tabu lift search for one group; returns (n, edges) or (0, [])."""
    out = lib.run_c(C_TABU, [d, D, seed, f"{seconds:.2f}", k, m, k2, r, cands],
                    stdin_graph=None, timeout=seconds + 10.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.85 * time_limit - 2.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for the D = 3 calibration case: return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    try:
        stats = {k: [0, 0] for k in _KS}   # [trials, wins]
        frac = 0.05                         # target = best * (1 + frac)
        while True:
            remaining = deadline - time.monotonic()
            if remaining < 2.0:
                break
            k = _pick_k(rng, stats)
            target_n = int(best[0] * (1.0 + frac)) + 2
            g = _sample_group(max(2, -(-target_n // (2 * k))), rng)
            if g is None:
                continue
            m, k2, r = g
            if 2 * k * m * k2 <= best[0]:
                continue
            slice_s = min(10.0, max(1.5, 0.3 * remaining))
            slice_s = min(slice_s, remaining - 0.5)
            if slice_s < 1.0:
                break
            stats[k][0] += 1
            try:
                n_, e_ = _tabu_in_c(d, D, k, m, k2, r, slice_s,
                                    rng.randrange(1, 1 << 30), 16)
            except RuntimeError:
                n_, e_ = 0, []
            if n_ > best[0] and lib.is_valid(n_, e_, d, D):
                stats[k][1] += 1
                best = (n_, e_)
                frac = min(0.2, frac * 1.3)
            else:
                frac = max(0.003, frac * 0.85)
    except Exception:
        pass  # keep the best valid graph found so far

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
