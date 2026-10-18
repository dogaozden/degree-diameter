import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine 1 (phase 1, unchanged from parent): bi-Cayley lift annealer over
# Z_m x| Z_k2 with block count k. Validity is checked on the 2k block
# representatives by BFS to depth D.
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
static int *perm, *vol, *nbr, *pw, *queue_, *stamp;
static int curstamp = 0;

static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_;
    int c = y / k2_, e = y % k2_;
    int a2 = (a + (pw[b] * c) % m_) % m_;
    int b2 = (b + e) % k2_;
    return a2 * k2_ + b2;
}

static void build_nbr(void) {
    int k = k_, G = G_, d = d_;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) {
            int t = perm[l * k + i], s = vol[l * k + i];
            for (int x = 0; x < G; x++) {
                int y = gmul(x, s);
                int a = i * G + x, b = (k + t) * G + y;
                nbr[a * d + l] = b;
                nbr[b * d + l] = a;
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
    if (d_ < 1 || d_ > 64 || D_ < 1 || k_ < 1 || m_ < 2 || k2_ < 1) { printf("0 0\n"); return 0; }
    r %= m_;
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
# C engine 2 (phase 2, new): bi-Cayley annealer over an ARBITRARY finite group
# given by its multiplication table (read from stdin). Groups include
# non-metabelian ones such as SL(2,p) x Z_c, which the semidirect lift misses.
#
# Vertices: A_i x and B_t y for i,t in [0,k), x,y in G. Node ids: A_i x = i*G+x,
# B_t y = (k+t)*G+y. Layer l gives perm[l][i] = t and voltage vol[l][i]:
#     A_i x ~ B_{perm[l][i]} (x * vol[l][i]).
# Left multiplication by G is an automorphism, so validity is decided by BFS
# to depth D from the 2k representatives A_i e and B_t e (cost = unreached
# pairs + penalty for duplicate darts). Output is d-regular and bipartite.
# Stdin: "G G*G" header, then G*G pairs "0 table[j]" with j = x*G + y.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;
static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, G_, N_;
static int *mt, *inv_, *perm, *vol, *back, *queue_, *stamp;
static int curstamp = 0;

static void build_back(void) {
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < k_; i++) {
            int t = perm[l * k_ + i];
            back[t * d_ + l] = i * d_ + l;
        }
}

static void nbrs(int v, int *out) {
    int k = k_, G = G_, d = d_;
    if (v < k * G) {
        int i = v / G, x = v % G;
        for (int l = 0; l < d; l++) {
            int t = perm[l * k + i];
            int y = mt[x * G + vol[l * k + i]];
            out[l] = (k + t) * G + y;
        }
    } else {
        int w = v - k * G;
        int t = w / G, y = w % G;
        for (int j = 0; j < d; j++) {
            int code = back[t * d + j];
            int i = code / d, l = code % d;
            int x = mt[y * G + inv_[vol[l * k + i]]];
            out[j] = i * G + x;
        }
    }
}

static long long cost_eval(void) {
    int k = k_, d = d_, G = G_, N = N_;
    long long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1 * k + i] == perm[l2 * k + i] && vol[l1 * k + i] == vol[l2 * k + i])
                    dup++;
    long long cost = 0;
    int nb[64];
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
                nbrs(v, nb);
                for (int j = 0; j < d; j++) {
                    int u = nb[j];
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
    return cost + 50 * dup;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    k_ = atoi(argv[5]);

    int G0 = 0, M0 = 0;
    if (scanf("%d %d", &G0, &M0) != 2) { printf("0 0\n"); return 0; }
    G_ = G0;
    if (d_ < 1 || d_ > 64 || D_ < 1 || k_ < 1 || G_ < 1 ||
        (long long)G_ * G_ != (long long)M0 || (long long)2 * k_ * G_ > 200000) {
        printf("0 0\n");
        return 0;
    }
    long long MM = (long long)G_ * G_;
    mt = malloc(sizeof(int) * (size_t)MM);
    inv_ = malloc(sizeof(int) * (size_t)G_);
    if (!mt || !inv_) { printf("0 0\n"); return 0; }
    for (long long j = 0; j < MM; j++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2 || b < 0 || b >= G_) { printf("0 0\n"); return 0; }
        mt[j] = b;
    }
    for (int x = 0; x < G_; x++) {
        if (mt[x] != x || mt[x * G_] != x) { printf("0 0\n"); return 0; }
    }
    for (int x = 0; x < G_; x++) {
        int f = -1;
        for (int y = 0; y < G_; y++) if (mt[x * G_ + y] == 0) { f = y; break; }
        if (f < 0) { printf("0 0\n"); return 0; }
        inv_[x] = f;
    }

    N_ = 2 * k_ * G_;
    perm = malloc(sizeof(int) * (size_t)d_ * k_);
    vol = malloc(sizeof(int) * (size_t)d_ * k_);
    back = malloc(sizeof(int) * (size_t)d_ * k_);
    queue_ = malloc(sizeof(int) * (size_t)N_);
    stamp = calloc((size_t)N_, sizeof(int));
    if (!perm || !vol || !back || !queue_ || !stamp) { printf("0 0\n"); return 0; }

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
    build_back();

    long long cost = cost_eval();
    const double T0 = 3.0, T1 = 0.05;
    clock_t c0 = clock();
    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);
        int l = rint_(d_), i = rint_(k_);
        if (k_ >= 2 && rint_(4) == 0) {
            int i2 = rint_(k_ - 1);
            if (i2 >= i) i2++;
            int *p1 = &perm[l * k_ + i], *p2 = &perm[l * k_ + i2];
            int tmp = *p1; *p1 = *p2; *p2 = tmp;
            build_back();
            long long nc = cost_eval();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                tmp = *p1; *p1 = *p2; *p2 = tmp;
                build_back();
            }
        } else {
            int idx = l * k_ + i;
            int old = vol[idx];
            int nv = rint_(G_);
            if (nv == old) continue;
            vol[idx] = nv;
            long long nc = cost_eval();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                vol[idx] = old;
            }
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }

    int m = k_ * G_ * d_;
    printf("%d %d\n", N_, m);
    for (int i = 0; i < k_; i++)
        for (int x = 0; x < G_; x++) {
            int v = i * G_ + x;
            for (int l = 0; l < d_; l++) {
                int t = perm[l * k_ + i];
                int y = mt[x * G_ + vol[l * k_ + i]];
                printf("%d %d\n", v, (k_ + t) * G_ + y);
            }
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4, 5)
_SL_CACHE = {}


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


def _lift_in_c(d, D, k, m, k2, r, seconds, seed):
    """Run the C lift annealer for one group; returns (n, edges) or (0, [])."""
    out = lib.run_c(C_LIFT, [d, D, seed, f"{seconds:.2f}", k, m, k2, r],
                    stdin_graph=None, timeout=seconds + 10.0)
    return lib.parse_graph_text(out)


def _semidirect_table(m, k2, r):
    """Multiplication table (numpy G x G, identity 0) of Z_m x| Z_k2 with (a,b)(c,e) = (a + r^b c, b + e)."""
    G = m * k2
    idx = np.arange(G, dtype=np.int64)
    a, b = idx // k2, idx % k2
    pw = np.array([pow(r, bb, m) for bb in range(k2)], dtype=np.int64) % m
    A1, B1 = a[:, None], b[:, None]
    A2, B2 = a[None, :], b[None, :]
    a3 = (A1 + pw[B1] * A2) % m
    b3 = (B1 + B2) % k2
    return a3 * k2 + b3


def _cyclic_table(c):
    """Multiplication table of Z_c."""
    idx = np.arange(c, dtype=np.int64)
    return (idx[:, None] + idx[None, :]) % c


def _product_table(T1, T2):
    """Multiplication table of the direct product of two groups given by tables."""
    G1, G2 = T1.shape[0], T2.shape[0]
    x = np.arange(G1 * G2, dtype=np.int64)
    x1, x2 = x // G2, x % G2
    return T1[x1[:, None], x1[None, :]] * G2 + T2[x2[:, None], x2[None, :]]


def _sl2_table(p):
    """Multiplication table of SL(2, p) for prime p, identity at index 0."""
    if p in _SL_CACHE:
        return _SL_CACHE[p]
    ident = (1, 0, 0, 1)
    els = [ident]
    for a, b, c, dd in itertools.product(range(p), repeat=4):
        if (a, b, c, dd) != ident and (a * dd - b * c) % p == 1:
            els.append((a, b, c, dd))
    E = np.array(els, dtype=np.int64)
    G = len(els)
    lut = np.full(p ** 4, -1, dtype=np.int64)
    codes = ((E[:, 0] * p + E[:, 1]) * p + E[:, 2]) * p + E[:, 3]
    lut[codes] = np.arange(G)
    a1, b1, c1, d1 = (E[:, j][:, None] for j in range(4))
    a2, b2, c2, d2 = (E[:, j][None, :] for j in range(4))
    A = (a1 * a2 + b1 * c2) % p
    B = (a1 * b2 + b1 * d2) % p
    C = (c1 * a2 + d1 * c2) % p
    Dm = (c1 * b2 + d1 * d2) % p
    code = ((A * p + B) * p + C) * p + Dm
    T = lut[code]
    _SL_CACHE[p] = T
    return T


def _random_group(lo, hi, rng):
    """Random group multiplication table with order in [lo, hi], or None."""
    u = rng.random()
    if u < 0.5:
        for _ in range(30):
            k2 = rng.choice([2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20,
                             21, 24, 28, 30, 35, 36, 40, 42, 48])
            mlo = max(2, -(-lo // k2))
            mhi = hi // k2
            if mlo > mhi:
                continue
            m = rng.randint(mlo, mhi)
            cands = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            return _semidirect_table(m, k2, rng.choice(cands))
        return None
    if u < 0.8:
        p, order = rng.choice([(5, 120), (7, 336)])
        mlo = max(1, -(-lo // order))
        mhi = hi // order
        if mlo > mhi:
            return None
        c = rng.randint(mlo, mhi)
        T = _sl2_table(p)
        return T if c == 1 else _product_table(T, _cyclic_table(c))
    return None


def _run_table(table, d, D, k, seconds, seed):
    """Run the table-group annealer for block count k; returns (n, edges) or (0, [])."""
    G = int(table.shape[0])
    flat = table.reshape(-1).tolist()
    pairs = [(0, v) for v in flat]
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}", k],
                    stdin_graph=(G, pairs), timeout=seconds + 15.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    total = min(float(time_limit), 60.0) * 0.85 - 1.5
    deadline = t0 + max(0.0, total)
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

    # Phase 1 (about 30%): parent's cyclic-semidirect lift annealing.
    try:
        lift_end = t0 + 0.3 * total
        stats = {k: [0, 0] for k in _KS}
        frac = 0.08
        while True:
            remaining = lift_end - time.monotonic()
            if remaining < 1.0:
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
            slice_s = min(4.0, max(1.0, 0.25 * remaining))
            try:
                n_, e_ = _lift_in_c(d, D, k, m, k2, r, slice_s, rng.randrange(1, 1 << 30))
            except RuntimeError:
                n_, e_ = 0, []
            if n_ > best[0] and lib.is_valid(n_, e_, d, D):
                stats[k][1] += 1
                best = (n_, e_)
                frac = min(0.25, frac * 1.3)
            else:
                frac = max(0.003, frac * 0.85)
    except Exception:
        pass  # keep the valid fallback

    # Phase 2 (rest of budget): annealing over arbitrary finite groups
    # (SL(2,p) x Z_c and semidirect groups), aiming just above the current best.
    try:
        misses = 0
        while misses < 400:
            remaining = deadline - time.monotonic()
            if remaining < 3.0:
                break
            ks = [k for k in (1, 2, 3) if -(-(best[0] + 2) // (2 * k)) <= 900]
            if not ks:
                break
            k = rng.choice(ks)
            lo = -(-(best[0] + 2) // (2 * k))
            hi = min(900, lo + max(10, lo // 12))
            g = _random_group(lo, hi, rng)
            if g is None:
                misses += 1
                continue
            misses = 0
            slice_s = min(8.0, max(2.0, 0.4 * remaining))
            try:
                n_, e_ = _run_table(g, d, D, k, slice_s, rng.randrange(1, 1 << 30))
            except RuntimeError:
                n_, e_ = 0, []
            consider(n_, e_)
    except Exception:
        pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
