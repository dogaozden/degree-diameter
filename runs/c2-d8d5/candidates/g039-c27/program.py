import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley voltage lifts.
#
# Base: k vertices A_0..A_{k-1} and k vertices B_0..B_{k-1}. Group G = Z_m x| Z_k2
# (element a*k2+b, product (a,b)(c,e) = (a + r^b c, b+e)). Layer l is a permutation
# sig_l of {0..k-1} with voltage volt[l][i]: the dart (l,i) joins A_i,g to B_{sig_l(i)},g*s.
# Every vertex then has exactly d neighbours (one per layer), and the graph is bipartite.
#
# Left multiplication is an automorphism, so the graph has diameter <= D iff the ball of
# radius D around each of the 2k base vertices (i, identity) covers everything. Cost is
# the total number of uncovered vertices over those 2k BFS runs, plus a penalty for
# duplicate darts. Cost 0 means valid; the engine prints the lift and exits.
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

static int d_, D_, k_, m_, k2_, G_, N_;
static int *pw, *sig, *volt, *invp, *gsi, *nb, *vis, *dd, *qu;
static unsigned stamp_ = 0;

static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_, c = y / k2_, e = y % k2_;
    int A = (int)(((long long)a + (long long)pw[b] * c) % m_);
    int B = (b + e) % k2_;
    return A * k2_ + B;
}

static int ginv(int x) {
    int a = x / k2_, b = x % k2_;
    int nb_ = (k2_ - b) % k2_;
    int A = (int)(((long long)pw[nb_] * a) % m_);
    A = (m_ - A) % m_;
    return A * k2_ + nb_;
}

static void rebuild(void) {
    int k = k_, G = G_, d = d_;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) {
            invp[l * k + sig[l * k + i]] = i;
        }
    for (int idx = 0; idx < k * d; idx++) gsi[idx] = ginv(volt[idx]);
    for (int i = 0; i < k; i++)
        for (int g = 0; g < G; g++) {
            int v = i * G + g;
            for (int l = 0; l < d; l++) {
                int j = sig[l * k + i];
                int s = volt[l * k + i];
                nb[v * d + l] = (k + j) * G + gmul(g, s);
            }
        }
    for (int j = 0; j < k; j++)
        for (int x = 0; x < G; x++) {
            int v = (k + j) * G + x;
            for (int l = 0; l < d; l++) {
                int i = invp[l * k + j];
                int si = gsi[l * k + i];
                nb[v * d + l] = i * G + gmul(x, si);
            }
        }
}

static long long evaluate(void) {
    rebuild();
    int N = N_, d = d_, k = k_, G = G_;
    long long cost = 0;
    for (int b = 0; b < 2 * k; b++) {
        int s = b * G;
        stamp_++;
        int h = 0, t = 0;
        qu[t++] = s;
        vis[s] = stamp_;
        dd[s] = 0;
        while (h < t) {
            int v = qu[h++];
            int dv = dd[v];
            if (dv >= D_) continue;
            int *row = nb + (size_t)v * d;
            for (int l = 0; l < d; l++) {
                int u = row[l];
                if (vis[u] != stamp_) {
                    vis[u] = stamp_;
                    dd[u] = dv + 1;
                    qu[t++] = u;
                }
            }
        }
        cost += (long long)(N - t);
    }
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (sig[l * k + i] == sig[l2 * k + i] && volt[l * k + i] == volt[l2 * k + i])
                    cost += G;
    return cost;
}

static void randomize(void) {
    int k = k_, d = d_;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) sig[l * k + i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = sig[l * k + i];
            sig[l * k + i] = sig[l * k + j];
            sig[l * k + j] = t;
        }
    }
    for (int idx = 0; idx < k * d; idx++) volt[idx] = rint_(G_);
}

static int gcd_(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    k_ = atoi(argv[5]);
    m_ = atoi(argv[6]);
    k2_ = atoi(argv[7]);
    int r = atoi(argv[8]);
    if (d_ < 1 || D_ < 1 || k_ < 1 || m_ < 2 || k2_ < 1) { printf("0 0\n"); return 0; }
    G_ = m_ * k2_;
    N_ = 2 * k_ * G_;
    if (N_ > 400000) { printf("0 0\n"); return 0; }
    r %= m_;
    if (r < 0) r += m_;
    if (gcd_(r, m_) != 1 && !(m_ == 1)) { printf("0 0\n"); return 0; }

    pw = malloc(sizeof(int) * (size_t)k2_);
    pw[0] = 1 % m_;
    for (int b = 1; b < k2_; b++) pw[b] = (int)((long long)pw[b - 1] * r % m_);
    if ((long long)pw[k2_ - 1] * r % m_ != 1 % m_) { printf("0 0\n"); return 0; }

    int kd = k_ * d_;
    sig = malloc(sizeof(int) * (size_t)kd);
    volt = malloc(sizeof(int) * (size_t)kd);
    invp = malloc(sizeof(int) * (size_t)kd);
    gsi = malloc(sizeof(int) * (size_t)kd);
    nb = malloc(sizeof(int) * (size_t)N_ * d_);
    vis = calloc((size_t)N_, sizeof(int));
    dd = calloc((size_t)N_, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)N_);
    if (!pw || !sig || !volt || !invp || !gsi || !nb || !vis || !dd || !qu) {
        printf("0 0\n");
        return 0;
    }

    randomize();
    clock_t c0 = clock();
    long long cost = evaluate();
    long long bestc = cost, iter = 0, lastImp = 0;
    double frac = 0.0;
    const double T0 = 3.0, T1 = 0.05;
    const long long RESTART = 40000;

    while (cost != 0) {
        if ((iter & 127) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= limit) break;
            frac = el / limit;
        }
        iter++;
        double T = T0 * pow(T1 / T0, frac);
        if (iter - lastImp > RESTART) {
            randomize();
            cost = evaluate();
            bestc = cost;
            lastImp = iter;
            continue;
        }
        if (k_ >= 2 && rdbl() < 0.35) {
            int l = rint_(d_), i1 = rint_(k_), i2 = rint_(k_ - 1);
            if (i2 >= i1) i2++;
            int a = l * k_ + i1, b = l * k_ + i2;
            int tmp = sig[a]; sig[a] = sig[b]; sig[b] = tmp;
            long long nc = evaluate();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                tmp = sig[a]; sig[a] = sig[b]; sig[b] = tmp;
            }
        } else {
            int idx = rint_(kd);
            int old = volt[idx];
            int nw = rint_(G_);
            if (nw == old) continue;
            volt[idx] = nw;
            long long nc = evaluate();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                volt[idx] = old;
            }
        }
        if (cost < bestc) { bestc = cost; lastImp = iter; }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }
    rebuild();
    int N = N_, d = d_, M = k_ * G_ * d_;
    printf("%d %d\n", N, M);
    for (int v = 0; v < k_ * G_; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nb[v * d + l]);
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
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 about target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1 % m
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

    # Safe fallback: K_{d,d}, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact record construction (calibration case)

    deadline = t0 + max(1.0, 0.88 * time_limit - 1.5)
    slice_s = max(3.0, min(10.0, 0.12 * time_limit))
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.25:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() + 1.0 < deadline:
        k = pick_k()
        base = best[0] // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 16 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G = m * k2
        if 2 * k * G <= best[0]:
            continue
        remaining = deadline - time.monotonic()
        budget = min(slice_s, remaining - 0.5)
        if budget < 1.0:
            break
        trials[k] += 1
        try:
            out = lib.run_c(C_SOURCE, [d, D, rng.randrange(1, 1 << 30), f"{budget:.2f}", k, m, k2, r],
                            stdin_graph=None, timeout=budget + 15.0)
            n, e = lib.parse_graph_text(out)
        except Exception:
            continue
        if n > best[0]:
            wins[k] += 1
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
