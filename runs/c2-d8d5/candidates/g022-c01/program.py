import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley (voltage) lift search over Z_m with k blocks per side.
#
# Vertices: A(i,g) = i*m+g and B(j,h) = k*m + j*m + h, for i,j in [0,k), g,h in Z_m.
# The base graph has d layers. Layer l sends A-block i to B-block pi_l(i), with
# voltage s_{l,i}: A(i,g) ~ B(pi_l(i), g+s_{l,i}). Each layer is a bijection of
# blocks, so every vertex has degree exactly d. Two layers with the same
# (pi_l(i), s_{l,i}) would create a double edge, so such pairs are penalized.
#
# Translation by Z_m is an automorphism, so the diameter condition only needs
# BFS from the 2k representatives A(i,0) and B(j,0). Cost = unreached pairs
# summed over those sources, plus a penalty per duplicate dart. Simulated
# annealing moves change one voltage or swap two block images in one layer.
# For each k, the search tries increasing group orders m and keeps the largest
# zero-cost lift.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXD 64
#define MAXK 8
#define MAXM 8192
#define MAXN (2 * MAXK * MAXM)
#define ITERS 12000
#define PEN 40

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, K_, M_, N_;
static int pi_[MAXD][MAXK], pinv_[MAXD][MAXK], sv_[MAXD][MAXK];
static int bpi[MAXD][MAXK], bsv[MAXD][MAXK];
static int best_k = 0, best_m = 0, best_n = 0;
static int *stamp_, *dist_, *queue_;
static int curstamp_ = 0;
static clock_t c0_;
static double limit_;

static int time_up(void) {
    return (double)(clock() - c0_) / CLOCKS_PER_SEC >= limit_;
}

static int neighbour(int v, int l) {
    if (v < K_ * M_) {
        int i = v / M_, g = v % M_;
        return K_ * M_ + pi_[l][i] * M_ + (g + sv_[l][i]) % M_;
    } else {
        int w = v - K_ * M_;
        int j = w / M_, h = w % M_;
        int i = pinv_[l][j];
        return i * M_ + (h - sv_[l][i] + M_) % M_;
    }
}

static int reach_count(int src) {
    if (++curstamp_ == 2000000000) {
        memset(stamp_, 0, sizeof(int) * MAXN);
        curstamp_ = 1;
    }
    int h = 0, t = 0;
    queue_[t++] = src;
    stamp_[src] = curstamp_;
    dist_[src] = 0;
    while (h < t) {
        int v = queue_[h++];
        if (dist_[v] >= D_) continue;
        for (int l = 0; l < d_; l++) {
            int u = neighbour(v, l);
            if (stamp_[u] != curstamp_) {
                stamp_[u] = curstamp_;
                dist_[u] = dist_[v] + 1;
                queue_[t++] = u;
            }
        }
    }
    return t;
}

static long long cost_of(void) {
    long long unreached = 0, dups = 0;
    int nsrc = 2 * K_;
    for (int s = 0; s < nsrc; s++) {
        int src = (s < K_) ? s * M_ : K_ * M_ + (s - K_) * M_;
        unreached += (long long)(N_ - reach_count(src));
    }
    for (int i = 0; i < K_; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = l + 1; l2 < d_; l2++)
                if (pi_[l][i] == pi_[l2][i] && sv_[l][i] == sv_[l2][i]) dups++;
    return unreached + (long long)PEN * dups;
}

static void random_init(void) {
    for (int l = 0; l < d_; l++) {
        int perm[MAXK];
        for (int i = 0; i < K_; i++) perm[i] = i;
        for (int i = K_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K_; i++) {
            pi_[l][i] = perm[i];
            pinv_[l][perm[i]] = i;
            sv_[l][i] = rint_(M_);
        }
    }
}

static void swap_images(int l, int i1, int i2) {
    int t = pi_[l][i1]; pi_[l][i1] = pi_[l][i2]; pi_[l][i2] = t;
    pinv_[l][pi_[l][i1]] = i1;
    pinv_[l][pi_[l][i2]] = i2;
}

static int anneal(void) {
    random_init();
    long long cur = cost_of();
    const double T0 = 6.0, T1 = 0.05;
    for (int t = 0; t < ITERS && cur > 0; t++) {
        if ((t & 127) == 0 && time_up()) break;
        double T = T0 * pow(T1 / T0, (double)t / ITERS);
        long long c2;
        if (K_ > 1 && rdbl() < 0.3) {
            int l = rint_(d_), i1 = rint_(K_), i2 = rint_(K_);
            if (i1 == i2) continue;
            swap_images(l, i1, i2);
            c2 = cost_of();
            if (c2 <= cur || rdbl() < exp(-(double)(c2 - cur) / T)) cur = c2;
            else swap_images(l, i1, i2);
        } else {
            int l = rint_(d_), i = rint_(K_);
            int old = sv_[l][i];
            int nw = rint_(M_);
            if (nw == old) continue;
            sv_[l][i] = nw;
            c2 = cost_of();
            if (c2 <= cur || rdbl() < exp(-(double)(c2 - cur) / T)) cur = c2;
            else sv_[l][i] = old;
        }
    }
    return cur == 0;
}

static void save_best(void) {
    best_k = K_;
    best_m = M_;
    best_n = N_;
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < K_; i++) {
            bpi[l][i] = pi_[l][i];
            bsv[l][i] = sv_[l][i];
        }
}

int main(int argc, char **argv) {
    if (argc < 7) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    limit_ = atof(argv[4]);
    int kmax = atoi(argv[5]);
    long long moore = atoll(argv[6]);
    if (d_ < 1 || d_ > MAXD || D_ < 1 || kmax < 1) { printf("0 0\n"); return 0; }
    if (kmax > MAXK) kmax = MAXK;

    stamp_ = calloc(MAXN, sizeof(int));
    dist_ = malloc(sizeof(int) * MAXN);
    queue_ = malloc(sizeof(int) * MAXN);
    if (!stamp_ || !dist_ || !queue_) { printf("0 0\n"); return 0; }

    int lo[MAXK + 1], hi[MAXK + 1], step[MAXK + 1];
    int usable = 0;
    for (int k = 1; k <= kmax; k++) {
        lo[k] = 2;
        step[k] = 4;
        long long h = moore / (2LL * k);
        if (h > MAXM) h = MAXM;
        hi[k] = (int)h;
        if (hi[k] >= lo[k]) usable++;
    }

    c0_ = clock();
    while (usable > 0 && !time_up()) {
        int k = 1 + rint_(kmax);
        if (hi[k] < lo[k]) continue;
        int m = lo[k] + rint_(step[k] + 1);
        if (m > hi[k]) m = hi[k];
        K_ = k;
        M_ = m;
        N_ = 2 * k * m;
        if (anneal()) {
            if (N_ > best_n) save_best();
            lo[k] = m + 1;
            if (step[k] < 64) step[k] *= 2;
            if (hi[k] < lo[k]) usable--;
        } else {
            step[k] /= 2;
        }
    }

    if (best_k == 0) { printf("0 0\n"); return 0; }
    int K = best_k, M = best_m, d = d_;
    printf("%d %d\n", 2 * K * M, K * M * d);
    for (int i = 0; i < K; i++)
        for (int g = 0; g < M; g++)
            for (int l = 0; l < d; l++) {
                int a = i * M + g;
                int b = K * M + bpi[l][i] * M + (g + bsv[l][i]) % M;
                printf("%d %d\n", a, b);
            }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue and deterministic constructions (fallbacks).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = (2, [(0, 1)])  # always valid for d >= 1, D >= 1

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    consider(*lib.haar_graph(d, range(d)))  # K_{d,d}, diameter 2

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact extremal construction

    # Main search: voltage lifts over Z_m with up to 4 blocks per side.
    elapsed = time.monotonic() - t0
    c_budget = min(0.8 * time_limit, time_limit - 8.0) - elapsed
    if c_budget >= 2.0:
        moore = lib.moore_bound(d, D)
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, str(int(seed) % (1 << 31)), f"{c_budget:.2f}", 4, moore],
                timeout=c_budget + 20.0,
            )
            cn, ce = lib.parse_graph_text(out)
            consider(cn, ce)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])
    return best
