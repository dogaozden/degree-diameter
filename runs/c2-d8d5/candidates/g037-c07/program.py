import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction: bi-Cayley lifts over Z_m x| Z_k2 with k base blocks per side.
#
# Vertices are A(i,g) and B(j,y) for block i,j in [0,k) and group element g,y.
# Layer l joins A(i,g) to B(p_l(i), g*s_l(i)), where p_l is a permutation (so
# every vertex gets exactly d neighbour slots) and s_l(i) is a group voltage.
# Left multiplication is an automorphism, so the cost only needs one BFS per
# block representative (2k BFS runs per evaluation, not N). The C annealer
# minimises the total number of unreached pairs from those representatives.
# Duplicate neighbour slots are harmless (they only lose an edge), and the
# output is deduplicated in Python before validation.
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

static int d_, D_, k_, G_, k2_, m_, r_, N_;
static int *mul_t, *inv_t, *perm, *pinv, *sv, *nb, *seen, *dd, *queue, *pw;
static int stamp_ = 0;

static void build_nb(void) {
    int k = k_, G = G_, d = d_;
    for (int i = 0; i < k; i++)
        for (int g = 0; g < G; g++) {
            int v = i * G + g;
            for (int l = 0; l < d; l++) {
                int j = perm[l * k + i];
                nb[v * d + l] = (k + j) * G + mul_t[g * G + sv[l * k + i]];
            }
        }
    for (int j = 0; j < k; j++)
        for (int y = 0; y < G; y++) {
            int v = (k + j) * G + y;
            for (int l = 0; l < d; l++) {
                int i = pinv[l * k + j];
                nb[v * d + l] = i * G + mul_t[y * G + inv_t[sv[l * k + i]]];
            }
        }
}

static long long ball_cost(int src) {
    int d = d_;
    stamp_++;
    int h = 0, t = 0, cnt = 1;
    queue[t++] = src;
    seen[src] = stamp_;
    dd[src] = 0;
    while (h < t) {
        int v = queue[h++];
        int dv = dd[v];
        if (dv >= D_) continue;
        const int *row = nb + (size_t)v * d;
        for (int l = 0; l < d; l++) {
            int u = row[l];
            if (seen[u] != stamp_) {
                seen[u] = stamp_;
                dd[u] = dv + 1;
                queue[t++] = u;
                cnt++;
            }
        }
    }
    return (long long)(N_ - cnt);
}

static long long cost_eval(void) {
    build_nb();
    long long tot = 0;
    for (int b = 0; b < 2 * k_; b++) tot += ball_cost(b * G_);
    return tot;
}

static void swap_perm(int l, int i1, int i2) {
    int k = k_;
    int a = perm[l * k + i1], b = perm[l * k + i2];
    perm[l * k + i1] = b;
    perm[l * k + i2] = a;
    pinv[l * k + b] = i1;
    pinv[l * k + a] = i2;
}

static int build_group(void) {
    int m = m_, k2 = k2_, r = r_;
    int G = G_;
    pw = malloc(sizeof(int) * (size_t)k2);
    if (!pw) return 0;
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    if ((long long)pw[k2 - 1] * r % m != 1 % m) return 0;
    mul_t = malloc(sizeof(int) * (size_t)G * G);
    inv_t = malloc(sizeof(int) * (size_t)G);
    if (!mul_t || !inv_t) return 0;
    for (int x = 0; x < G; x++) {
        int a1 = x / k2, b1 = x % k2;
        for (int y = 0; y < G; y++) {
            int a2 = y / k2, b2 = y % k2;
            int a = (int)((a1 + (long long)pw[b1] * a2) % m);
            int b = (b1 + b2) % k2;
            mul_t[x * G + y] = a * k2 + b;
        }
    }
    for (int g = 0; g < G; g++) {
        int found = -1;
        for (int h = 0; h < G; h++)
            if (mul_t[g * G + h] == 0) { found = h; break; }
        if (found < 0) return 0;
        inv_t[g] = found;
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 9) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    k_ = atoi(argv[5]);
    m_ = atoi(argv[6]);
    k2_ = atoi(argv[7]);
    r_ = atoi(argv[8]);
    if (d_ < 1 || D_ < 1 || k_ < 1 || m_ < 2 || k2_ < 1) { printf("0 0\n"); return 0; }
    G_ = m_ * k2_;
    if (G_ > 3000 || (long long)G_ * G_ > 4000000LL) { printf("0 0\n"); return 0; }
    if (!build_group()) { printf("0 0\n"); return 0; }

    int d = d_, k = k_, G = G_;
    N_ = 2 * k * G;
    perm = malloc(sizeof(int) * (size_t)d * k);
    pinv = malloc(sizeof(int) * (size_t)d * k);
    sv = malloc(sizeof(int) * (size_t)d * k);
    nb = malloc(sizeof(int) * (size_t)N_ * d);
    seen = calloc((size_t)N_, sizeof(int));
    dd = malloc(sizeof(int) * (size_t)N_);
    queue = malloc(sizeof(int) * (size_t)N_);
    if (!perm || !pinv || !sv || !nb || !seen || !dd || !queue) { printf("0 0\n"); return 0; }

    for (int l = 0; l < d; l++) {
        int tmp[64];
        if (k > 64) { printf("0 0\n"); return 0; }
        for (int i = 0; i < k; i++) tmp[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = tmp[i]; tmp[i] = tmp[j]; tmp[j] = t;
        }
        for (int i = 0; i < k; i++) {
            perm[l * k + i] = tmp[i];
            pinv[l * k + tmp[i]] = i;
        }
        for (int i = 0; i < k; i++) sv[l * k + i] = rint_(G);
    }

    clock_t c0 = clock();
    long long cur = cost_eval();
    const double T0 = 3.0, T1 = 0.1;
    double el = 0.0, T = T0;
    long long it = 0;
    while (cur > 0) {
        if ((it & 127) == 0) {
            el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= limit) break;
            T = T0 * pow(T1 / T0, el / limit);
        }
        it++;
        if (k >= 2 && rdbl() < 0.3) {
            int l = rint_(d), i1 = rint_(k), i2 = rint_(k - 1);
            if (i2 >= i1) i2++;
            swap_perm(l, i1, i2);
            long long nc = cost_eval();
            long long delta = nc - cur;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cur = nc;
            } else {
                swap_perm(l, i1, i2);
            }
        } else {
            int l = rint_(d), i = rint_(k);
            int idx = l * k + i;
            int old = sv[idx];
            int nw = rint_(G);
            if (nw == old) continue;
            sv[idx] = nw;
            long long nc = cost_eval();
            long long delta = nc - cur;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cur = nc;
            } else {
                sv[idx] = old;
            }
        }
    }

    if (cur != 0) { printf("0 0\n"); return 0; }
    build_nb();
    int M = k * G * d;
    printf("%d %d\n", N_, M);
    for (int v = 0; v < k * G; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nb[v * d + l]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue and constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(300):
        k2 = rng.choice([1, 1, 1, 2, 2, 3, 4, 6])
        m = max(2, -(-target // k2))
        G = m * k2
        if G * G > 3_000_000:
            continue
        if k2 == 1:
            return m, 1, 1
        for _ in range(80):
            r = rng.randrange(2, m) if m > 2 else 1
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                return m, k2, r
    return None


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

    deadline = t0 + max(1.0, time_limit - 5.0)

    # Bi-Cayley search: grow the target order whenever a lift is found.
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 0.5:
            break
        k = rng.choice([1, 1, 2, 2, 3, 4, 5, 6])
        base = best[0] // (2 * k)
        target = base + 1 + rng.randrange(0, max(2, base // 60 + 2))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best[0]:
            continue
        slice_t = min(5.0, remaining - 0.3)
        if slice_t < 0.5:
            break
        try:
            out = lib.run_c(C_SOURCE,
                            [d, D, rng.randrange(1, 1 << 30), f"{slice_t:.2f}", k, m, k2, r],
                            timeout=slice_t + 10.0)
            n, e = lib.parse_graph_text(out)
        except Exception:
            continue
        if n > 0 and e:
            e = sorted({(min(u, v), max(u, v)) for u, v in e if u != v})
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
