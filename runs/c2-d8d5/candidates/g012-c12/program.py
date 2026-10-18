import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts on the semidirect product
# G = Z_m x| Z_k2 (element a*k2+b, product (a,b)(c,e) = (a + r^b c, b+e)).
#
# The lift has 2k base vertices, each blown up into a copy of G. Layer l
# carries a permutation J_l of the k A-bases onto the k B-bases and a voltage
# S_l[i] in G, joining A(i,g) to B(J_l[i], g*S_l[i]). Every vertex then has
# degree exactly d. Left multiplication by a group element is an automorphism,
# so distances only need to be checked from the 2k base vertices. The cost is
# the number of (base, far vertex) pairs at distance > D, plus a large penalty
# for duplicate darts. Cost zero means a valid graph, which is printed.
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

#define MAXDEG 16
#define MAXK 8
#define MAXPW 64

static int d_, D_, K_, G_, M_, K2_, N_;
static int S_[MAXDEG][MAXK];
static int J_[MAXDEG][MAXK];
static long long pw_[MAXPW];
static int *nbr, *dist, *queue;

static int gmul(int x, int y) {
    int a = x / K2_, b = x % K2_;
    int c = y / K2_, e = y % K2_;
    long long t = (pw_[b] * (long long)c) % M_;
    int aa = (int)(((long long)a + t) % M_);
    return aa * K2_ + (b + e) % K2_;
}

static void build_nbr(void) {
    int d = d_;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K_; i++) {
            int j = J_[l][i], s = S_[l][i];
            for (int g = 0; g < G_; g++) {
                int A = i * G_ + g;
                int B = (K_ + j) * G_ + gmul(g, s);
                nbr[A * d + l] = B;
                nbr[B * d + l] = A;
            }
        }
    }
}

static long long dup_count(void) {
    long long c = 0;
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < K_; i++)
            for (int l2 = 0; l2 < l; l2++)
                if (J_[l2][i] == J_[l][i] && S_[l2][i] == S_[l][i]) c++;
    return c;
}

/* Sum over the 2K base vertices of the number of vertices at distance > D_. */
static long long eval_bad(void) {
    build_nbr();
    int N = N_, d = d_;
    long long bad = 0;
    for (int b = 0; b < 2 * K_; b++) {
        for (int v = 0; v < N; v++) dist[v] = -1;
        int src = b * G_;
        int head = 0, tail = 0;
        queue[tail++] = src;
        dist[src] = 0;
        int cnt = 0;
        while (head < tail) {
            int v = queue[head++];
            cnt++;
            if (dist[v] >= D_) continue;
            for (int t = 0; t < d; t++) {
                int u = nbr[v * d + t];
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    queue[tail++] = u;
                }
            }
        }
        bad += N - cnt;
    }
    return bad;
}

static long long full_cost(void) {
    long long PEN = N_;
    return eval_bad() + PEN * dup_count();
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    K_ = atoi(argv[5]);
    M_ = atoi(argv[6]);
    K2_ = atoi(argv[7]);
    long long r = atoll(argv[8]);
    if (d_ < 1 || d_ > MAXDEG || D_ < 1 || K_ < 1 || K_ > MAXK ||
        M_ < 1 || K2_ < 1 || K2_ >= MAXPW) {
        printf("0 0\n");
        return 0;
    }
    G_ = M_ * K2_;
    long long Nl = 2LL * K_ * G_;
    if (Nl > 200000) { printf("0 0\n"); return 0; }
    N_ = (int)Nl;

    /* Power table r^b mod M and the check r^K2 = 1 mod M. */
    long long rm = r % M_;
    pw_[0] = 1 % M_;
    for (int b = 1; b < K2_; b++) pw_[b] = (pw_[b - 1] * rm) % M_;
    long long p = (pw_[K2_ - 1] * rm) % M_;
    if (p != 1 % M_) { printf("0 0\n"); return 0; }

    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    dist = malloc(sizeof(int) * (size_t)N_);
    queue = malloc(sizeof(int) * (size_t)N_);
    if (!nbr || !dist || !queue) { printf("0 0\n"); return 0; }

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K_; i++) J_[l][i] = i;
        for (int i = K_ - 1; i > 0; i--) {
            int t = rint_(i + 1);
            int tmp = J_[l][i]; J_[l][i] = J_[l][t]; J_[l][t] = tmp;
        }
        for (int i = 0; i < K_; i++) S_[l][i] = rint_(G_);
    }

    long long cur = full_cost();
    double T0 = 2.0 + 0.05 * (double)cur, T1 = 0.2;
    clock_t start = clock();
    while (cur > 0) {
        double el = (double)(clock() - start) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);
        int l = rint_(d_);
        int mode = (K_ >= 2 && rdbl() < 0.3) ? 1 : 2;
        int i1 = 0, i2 = 0, i = 0, oldS = 0;
        if (mode == 1) {
            i1 = rint_(K_);
            i2 = rint_(K_ - 1);
            if (i2 >= i1) i2++;
            int t = J_[l][i1]; J_[l][i1] = J_[l][i2]; J_[l][i2] = t;
        } else {
            i = rint_(K_);
            oldS = S_[l][i];
            S_[l][i] = rint_(G_);
        }
        long long nc = full_cost();
        long long delta = nc - cur;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            if (mode == 1) {
                int t = J_[l][i1]; J_[l][i1] = J_[l][i2]; J_[l][i2] = t;
            } else {
                S_[l][i] = oldS;
            }
        }
    }

    if (cur != 0) { printf("0 0\n"); return 0; }
    build_nbr();
    int N = N_, d = d_;
    long long m = (long long)N * d / 2;
    printf("%d %lld\n", N, m);
    for (int v = 0; v < N; v++)
        for (int t = 0; t < d; t++) {
            int u = nbr[v * d + t];
            if (u > v) printf("%d %d\n", v, u);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_KS = (1, 2, 2, 3, 3, 4)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
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
    if D == 2:
        return best

    # Bi-Cayley lifts over semidirect products, annealed in C. Each call tries
    # to beat the current best order; a success raises the target.
    deadline = t0 + max(1.0, time_limit - 6.0)
    failures = 0
    while failures < 3:
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            break
        k = rng.choice(_KS)
        target = max(2, best[0] // (2 * k) + 1 + rng.randrange(0, 4))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best[0]:
            continue
        slice_ = min(remaining, 8.0)
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, rng.randrange(1, 1 << 30), f"{slice_:.2f}", k, m, k2, r],
                timeout=slice_ + 15.0,
            )
            n, e = lib.parse_graph_text(out)
        except Exception:
            failures += 1
            continue
        if n > 0:
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
