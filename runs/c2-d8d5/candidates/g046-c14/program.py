import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine A (new): bi-Cayley lift annealer over PSL(2,p) or PGL(2,p).
#
# The group is the projective linear group over GF(p), with canonical
# representatives (first nonzero entry = 1). Mode 0 is PSL (square determinant,
# order p(p^2-1)/2), mode 1 is PGL (order p(p^2-1)). The C code builds the
# group itself, so no data has to be passed through the command line.
#
# Vertices: A_i x and B_t x for i, t in [0, k), x in G (index i*G+x, (k+t)*G+x).
# Layer l has a permutation perm[l][i] and a voltage vol[l][i]:
#     A_i x ~ B_{perm[l][i]} (x * vol[l][i]).
# Left multiplication by G is an automorphism, so the cost only needs the 2k
# block identities. Cost = unreached vertices in those radius-D balls plus a
# penalty for repeated darts. Products x*s are cached per voltage row, so a
# move only recomputes one row of G products.
# ----------------------------------------------------------------------------

C_PROJ = r"""
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

static int d_, D_, k_, p_, G_, N_;
static int *el, *idx_, *inv_;
static int *perm, *vol, *ytab, *nbr, *queue_, *stamp, *rowtmp;
static int curstamp = 0;
static int bad_ = 0;

static int powmod(int b, int e) {
    long long r = 1, x = ((long long)b % p_ + p_) % p_;
    while (e > 0) {
        if (e & 1) r = r * x % p_;
        x = x * x % p_;
        e >>= 1;
    }
    return (int)r;
}

static int key4(int a, int b, int c, int d) {
    return ((a * p_ + b) * p_ + c) * p_ + d;
}

static void push_el(int a, int b, int c, int dd) {
    el[4 * G_] = a;
    el[4 * G_ + 1] = b;
    el[4 * G_ + 2] = c;
    el[4 * G_ + 3] = dd;
    idx_[key4(a, b, c, dd)] = G_;
    G_++;
}

static void build_group(int mode) {
    int p = p_;
    int n4 = p * p * p * p;
    idx_ = malloc(sizeof(int) * (size_t)n4);
    el = malloc(sizeof(int) * 4 * (size_t)n4);
    inv_ = malloc(sizeof(int) * (size_t)(p + 1));
    for (int i = 0; i < n4; i++) idx_[i] = -1;
    for (int f = 1; f < p; f++) inv_[f] = powmod(f, p - 2);
    G_ = 0;
    push_el(1, 0, 0, 1);  /* identity is element 0 */
    int h = (p - 1) / 2;
    for (int a = 0; a < p; a++)
        for (int b = 0; b < p; b++)
            for (int c = 0; c < p; c++)
                for (int dd = 0; dd < p; dd++) {
                    if (a == 1 && b == 0 && c == 0 && dd == 1) continue;
                    int f = a ? a : (b ? b : (c ? c : dd));
                    if (f != 1) continue;
                    int det = ((a * dd - b * c) % p + p) % p;
                    if (det == 0) continue;
                    if (mode == 0 && powmod(det, h) != 1) continue;
                    push_el(a, b, c, dd);
                }
}

static int mul_idx(int x, int y) {
    const int *A = el + 4 * (size_t)x;
    const int *B = el + 4 * (size_t)y;
    long long a = ((long long)A[0] * B[0] + (long long)A[1] * B[2]) % p_;
    long long b = ((long long)A[0] * B[1] + (long long)A[1] * B[3]) % p_;
    long long c = ((long long)A[2] * B[0] + (long long)A[3] * B[2]) % p_;
    long long dd = ((long long)A[2] * B[1] + (long long)A[3] * B[3]) % p_;
    long long f = a ? a : (b ? b : (c ? c : dd));
    if (!f) { bad_ = 1; return 0; }
    long long iv = inv_[f];
    a = a * iv % p_;
    b = b * iv % p_;
    c = c * iv % p_;
    dd = dd * iv % p_;
    int r = idx_[key4((int)a, (int)b, (int)c, (int)dd)];
    if (r < 0) { bad_ = 1; return 0; }
    return r;
}

static void set_row(int e, int s) {
    int G = G_;
    int *row = ytab + (size_t)e * G;
    for (int x = 0; x < G; x++) row[x] = mul_idx(x, s);
    vol[e] = s;
}

static void build_nbr(void) {
    int k = k_, d = d_, G = G_;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) {
            int e = l * k + i;
            int t = perm[e];
            const int *yr = ytab + (size_t)e * G;
            for (int x = 0; x < G; x++) {
                int a = i * G + x;
                int b = (k + t) * G + yr[x];
                nbr[(size_t)a * d + l] = b;
                nbr[(size_t)b * d + l] = a;
            }
        }
}

static long long eval_cost(void) {
    int k = k_, d = d_, N = N_;
    long long dups = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1 * k + i] == perm[l2 * k + i] && vol[l1 * k + i] == vol[l2 * k + i])
                    dups++;
    build_nbr();
    long long cost = 0;
    for (int b = 0; b < 2 * k; b++) {
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

int main(int argc, char **argv) {
    if (argc < 8) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    k_ = atoi(argv[5]);
    p_ = atoi(argv[6]);
    int mode = atoi(argv[7]);
    if (d_ < 1 || d_ > 64 || D_ < 1 || k_ < 1 || p_ < 3 || p_ > 23) { printf("0 0\n"); return 0; }

    build_group(mode);
    if (bad_ || G_ < 2) { printf("0 0\n"); return 0; }
    N_ = 2 * k_ * G_;
    if ((long long)N_ > 200000) { printf("0 0\n"); return 0; }

    int E = d_ * k_;
    perm = malloc(sizeof(int) * (size_t)E);
    vol = malloc(sizeof(int) * (size_t)E);
    ytab = malloc(sizeof(int) * (size_t)E * (size_t)G_);
    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    queue_ = malloc(sizeof(int) * (size_t)N_);
    stamp = calloc((size_t)N_, sizeof(int));
    rowtmp = malloc(sizeof(int) * (size_t)G_);
    if (!perm || !vol || !ytab || !nbr || !queue_ || !stamp || !rowtmp) { printf("0 0\n"); return 0; }

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
    for (int e = 0; e < E; e++) set_row(e, vol[e]);
    if (bad_) { printf("0 0\n"); return 0; }

    long long cost = eval_cost();
    const double T0 = 4.0, T1 = 0.2;
    clock_t c0 = clock();
    while (cost > 0) {
        double el_t = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el_t >= limit) break;
        double T = T0 * pow(T1 / T0, el_t / limit);
        int l = rint_(d_), i = rint_(k_);
        int e = l * k_ + i;
        if (k_ >= 2 && rint_(3) == 0) {
            int i2 = rint_(k_ - 1);
            if (i2 >= i) i2++;
            int e2 = l * k_ + i2;
            int t = perm[e]; perm[e] = perm[e2]; perm[e2] = t;
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                t = perm[e]; perm[e] = perm[e2]; perm[e2] = t;
            }
        } else {
            int old = vol[e];
            int nv = rint_(G_);
            if (nv == old) continue;
            memcpy(rowtmp, ytab + (size_t)e * G_, sizeof(int) * (size_t)G_);
            set_row(e, nv);
            if (bad_) {
                bad_ = 0;
                vol[e] = old;
                memcpy(ytab + (size_t)e * G_, rowtmp, sizeof(int) * (size_t)G_);
                continue;
            }
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                vol[e] = old;
                memcpy(ytab + (size_t)e * G_, rowtmp, sizeof(int) * (size_t)G_);
            }
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }

    build_nbr();
    long long *pairs = malloc(sizeof(long long) * (size_t)N_ * d_);
    if (!pairs) { printf("0 0\n"); return 0; }
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
# C engine B (kept from the parent): bi-Cayley lift annealer over the
# semidirect product Z_m x| Z_k2 (element a*k2+b, product (a,b)(c,e) = (a + r^b c, b + e)).
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

    build_nbr();
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

_KS = (1, 2, 3, 4, 5)
_PROJ_PRIMES = (5, 7, 11, 13, 17)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _proj_candidates(best_n, cap=5200):
    """Bi-Cayley candidates over PSL/PGL(2,p) with 2*k*|G| in (best_n, cap]."""
    out = []
    for p in _PROJ_PRIMES:
        for mode in (0, 1):
            G = p * (p * p - 1) // (2 if mode == 0 else 1)
            for k in range(1, 7):
                n = 2 * k * G
                if best_n < n <= cap:
                    out.append((n, p, mode, k))
    return out


def _proj_in_c(d, D, p, mode, k, seconds, seed):
    """Run the PSL/PGL lift annealer; returns (n, edges) or (0, [])."""
    out = lib.run_c(C_PROJ, [d, D, seed, f"{seconds:.2f}", k, p, mode],
                    stdin_graph=None, timeout=seconds + 10.0)
    return lib.parse_graph_text(out)


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
    """Run the semidirect lift annealer for one group; returns (n, edges) or (0, [])."""
    out = lib.run_c(C_LIFT, [d, D, seed, f"{seconds:.2f}", k, m, k2, r],
                    stdin_graph=None, timeout=seconds + 10.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + max(1.0, time_limit - 5.0)   # margin for C compile and process overhead
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always a valid fallback for D >= 2

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

    # Phase P (new construction): bi-Cayley lifts over PSL(2,p) / PGL(2,p).
    # Smallest unbeaten candidate first; a failed candidate gets a longer slice next time.
    proj_end = time.monotonic() + 0.7 * max(0.0, end - time.monotonic())
    fails = {}
    while True:
        rem = proj_end - time.monotonic()
        if rem < 1.5:
            break
        cands = _proj_candidates(best[0])
        if not cands:
            break
        cand = min(cands, key=lambda c: (fails.get(c, 0), c[0]))
        f = fails.get(cand, 0)
        sl = min(rem, max(3.0, min(25.0, 0.25 * rem)) * (1.6 ** f))
        if sl < 1.0:
            break
        n_, p, mode, k = cand
        try:
            cn, ce = _proj_in_c(d, D, p, mode, k, sl, rng.randrange(1, 1 << 30))
        except Exception:
            cn, ce = 0, []
        if cn > best[0] and lib.is_valid(cn, ce, d, D):
            best = (cn, ce)
        else:
            fails[cand] = f + 1

    # Phase L: semidirect cyclic-by-cyclic lifts with an adaptive target size.
    stats = {k: [0, 0] for k in _KS}
    frac = 0.08
    while True:
        remaining = end - time.monotonic()
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
