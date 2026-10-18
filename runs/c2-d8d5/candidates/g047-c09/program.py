import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lift annealer over an arbitrary finite group given by a
# descriptor. Two group families are supported:
#   type 0: semidirect product Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))
#   type 1: affine group V x| <M>, V = Z_p^2, <M> cyclic in GL(2,p) of order h
#           (element (v, j) coded as (v1*p+v2)*h + j, product (v,j)(w,l) = (v+M^j w, j+l))
#
# Vertices: A_i x and B_t x for i, t in [0, k) and x in G (index i*G+x, (k+t)*G+x).
# Layer l gives perm[l][i] and vol[l][i]:  A_i x ~ B_{perm[l][i]} (x * vol[l][i]).
# Each vertex has one neighbour per layer, so the graph is d-regular and bipartite.
# Left multiplication by G is an automorphism, so validity reduces to the 2k
# block representatives; cost = unreached vertices in those radius-D balls
# + penalty for repeated darts. Simulated annealing on perm/vol moves.
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

static int d_, D_, k_, G_, N_, gtype_;
static int m_, k2_;
static int *pw;
static int p_, h_;
static int *mat;
static int *perm, *vol, *nbr, *queue_, *stamp;
static int curstamp = 0;

static int gmul(int x, int y) {
    if (gtype_ == 0) {
        int a = x / k2_, b = x % k2_;
        int c = y / k2_, e = y % k2_;
        int a2 = (a + (pw[b] * c) % m_) % m_;
        int b2 = (b + e) % k2_;
        return a2 * k2_ + b2;
    } else {
        int v = x / h_, j = x % h_;
        int w = y / h_, l = y % h_;
        int w1 = w / p_, w2 = w % p_;
        const int *M = mat + 4 * j;
        int u1 = (M[0] * w1 + M[1] * w2) % p_;
        int u2 = (M[2] * w1 + M[3] * w2) % p_;
        int v1 = v / p_, v2 = v % p_;
        int z1 = (v1 + u1) % p_, z2 = (v2 + u2) % p_;
        int j2 = (j + l) % h_;
        return (z1 * p_ + z2) * h_ + j2;
    }
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
    int k = k_, d = d_, D = D_, N = N_;
    long long dups = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1 * k + i] == perm[l2 * k + i] && vol[l1 * k + i] == vol[l2 * k + i])
                    dups++;
    long long cost = 0;
    for (int b = 0; b < 2 * k; b++) {
        int src = b * G_;
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
    if (argc < 7) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    k_ = atoi(argv[5]);
    gtype_ = atoi(argv[6]);
    if (d_ < 1 || d_ > 64 || D_ < 1 || k_ < 1) { printf("0 0\n"); return 0; }

    if (gtype_ == 0) {
        if (argc < 10) { printf("0 0\n"); return 0; }
        m_ = atoi(argv[7]);
        k2_ = atoi(argv[8]);
        int r = atoi(argv[9]);
        if (m_ < 2 || k2_ < 1) { printf("0 0\n"); return 0; }
        r %= m_;
        pw = malloc(sizeof(int) * (size_t)(k2_ + 1));
        if (!pw) { printf("0 0\n"); return 0; }
        pw[0] = 1 % m_;
        for (int b = 1; b <= k2_; b++) pw[b] = (int)((long long)pw[b - 1] * r % m_);
        if (pw[k2_] != 1 % m_) { printf("0 0\n"); return 0; }
        G_ = m_ * k2_;
    } else if (gtype_ == 1) {
        if (argc < 9) { printf("0 0\n"); return 0; }
        p_ = atoi(argv[7]);
        h_ = atoi(argv[8]);
        if (p_ < 2 || h_ < 1 || argc < 9 + 4 * h_) { printf("0 0\n"); return 0; }
        mat = malloc(sizeof(int) * (size_t)(4 * h_));
        if (!mat) { printf("0 0\n"); return 0; }
        for (int i = 0; i < 4 * h_; i++) mat[i] = atoi(argv[9 + i]);
        G_ = p_ * p_ * h_;
    } else {
        printf("0 0\n");
        return 0;
    }

    if ((long long)G_ * 2 * k_ > 200000 || G_ < 2) { printf("0 0\n"); return 0; }
    N_ = 2 * k_ * G_;

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

    set_all_darts();
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
            set_dart(l, i);
            set_dart(l, i2);
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                t = *p1; *p1 = *p2; *p2 = t;
                set_dart(l, i);
                set_dart(l, i2);
            }
        } else {
            int old = vol[l * k_ + i];
            int nv = rint_(G_);
            if (nv == old) continue;
            vol[l * k_ + i] = nv;
            set_dart(l, i);
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                vol[l * k_ + i] = old;
                set_dart(l, i);
            }
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }

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
_I2 = (1, 0, 0, 1)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _mat_mul(X, Y, p):
    """Product of two 2x2 matrices (row-major 4-tuples) mod p."""
    a, b, c, dd = X
    e, f, g, h = Y
    return ((a * e + b * g) % p, (a * f + b * h) % p,
            (c * e + dd * g) % p, (c * f + dd * h) % p)


def _affine_pool(rng, primes=(3, 5, 7, 11), samples=400):
    """Cyclic subgroups <M> of GL(2,p) found by random sampling.

    Returns a list of (p, h, flat) where flat holds the h matrices M^0..M^(h-1).
    The affine group V x| <M> has order p*p*h.
    """
    pool, seen = [], set()
    for p in primes:
        for _ in range(samples):
            M = tuple(rng.randrange(p) for _ in range(4))
            a, b, c, dd = M
            if (a * dd - b * c) % p == 0:
                continue
            powers, cur, closed = [_I2], M, False
            while len(powers) <= 200:
                if cur == _I2:
                    closed = True
                    break
                powers.append(cur)
                cur = _mat_mul(cur, M, p)
            if not closed or len(powers) < 2:
                continue
            key = (p, frozenset(powers))
            if key in seen:
                continue
            seen.add(key)
            pool.append((p, len(powers), [x for Q in powers for x in Q]))
    return pool


def _sample_group(target, rng):
    """Return (m, k2, r) for the semidirect Z_m x| Z_k2 with m*k2 >= target, or None."""
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


def _pick_group(lo_G, hi_G, pool, rng):
    """Return (gtype, gargs, order) for a group of order near [lo_G, hi_G], or None."""
    opts = [t for t in pool if lo_G <= t[0] * t[0] * t[1] <= hi_G]
    if opts and rng.random() < 0.8:
        p, h, flat = rng.choice(opts)
        return 1, [p, h] + flat, p * p * h
    g = _sample_group(lo_G, rng)
    if g is None:
        return None
    m, k2, r = g
    return 0, [m, k2, r], m * k2


def _pick_k(rng, stats):
    """Bandit choice of base-block count k (mostly exploit, sometimes explore)."""
    if rng.random() < 0.25:
        return rng.choice(_KS)
    return max(_KS, key=lambda k: (stats[k][1] + 1) / (stats[k][0] + 2) + 0.02 * rng.random())


def _lift_in_c(d, D, k, gtype, gargs, seconds, seed):
    """Run the C lift annealer for one group; returns (n, edges) or (0, [])."""
    args = [d, D, seed, f"{seconds:.2f}", k, gtype, *gargs]
    out = lib.run_c(C_LIFT, args, stdin_graph=None, timeout=seconds + 10.0)
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

    # Lift search over affine groups V x| <M> (V = Z_p^2) and semidirect Z_m x| Z_k2.
    pool = _affine_pool(rng)
    lift_end = t0 + 0.9 * time_limit - 1.0
    stats = {k: [0, 0] for k in _KS}   # [trials, wins]
    frac = 0.05                         # target = best * (1 + frac)
    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 1.0:
            break
        k = _pick_k(rng, stats)
        need = best[0] * (1.0 + frac) + 2
        lo_G = max(2, -(-int(need) // (2 * k)))
        hi_G = int(lo_G * 1.1) + 3
        g = _pick_group(lo_G, hi_G, pool, rng)
        if g is None:
            continue
        gtype, gargs, G = g
        if 2 * k * G <= best[0]:
            continue
        stats[k][0] += 1
        slice_s = min(4.0, max(1.0, 0.25 * remaining))
        try:
            n_, e_ = _lift_in_c(d, D, k, gtype, gargs, slice_s, rng.randrange(1, 1 << 30))
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
    return best
