import math
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over groups Z_m x| Z_t with K base vertices per side.
#
# A lift has 2*K*G vertices, G = m*t. Each layer l is a permutation sig_l of
# the K A-blocks onto the K B-blocks, plus a voltage S_{l,i} in the group.
# Vertex A_{i,x} is joined to B_{sig_l(i), x*S_{l,i}} in every layer l, so the
# lift is d-regular and bipartite. Left translations are automorphisms, so the
# distance profile of each block is read from one representative per block
# (2K BFS runs). Cost = total unreached pairs over the representatives, plus a
# penalty for duplicate edges. Cost 0 means a valid graph. Simulated annealing
# moves change voltages and swap layer permutations. The engine sweeps the order
# upward: after each success it moves to the next m with fresh random starts.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXK 8
#define MAXD 16
#define MAXG 6000
#define MAXN (2 * MAXK * MAXG)

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, K_, T_, M_, R_, G_, N_;
static int pw[64];
static int sig[MAXD * MAXK], inv_[MAXD * MAXK], S[MAXD * MAXK];
static int bsig[MAXD * MAXK], bS[MAXD * MAXK];
static int bestFound = 0, bestM = 0, bestR = 1, bestG = 0;

static int adj_[MAXN * MAXD];
static int stampv[MAXN], distv[MAXN], qv[MAXN];
static int curst = 0;
static int badtmp[2 * MAXK], badcur[2 * MAXK];
static int cand[MAXG];

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static long long powmod_(long long b, int e, int m) {
    long long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gmul(int x, int y) {
    int a = x / T_, b = x - a * T_;
    int c = y / T_, e = y - c * T_;
    int a2 = (a + (int)((long long)pw[b] * c % M_)) % M_;
    int b2 = (b + e) % T_;
    return a2 * T_ + b2;
}

static int pick_r(int m, int t) {
    int nc = 0;
    for (int r = 1; r < m; r++) {
        if (gcd_(r, m) == 1 && powmod_(r, t, m) == 1 % m) cand[nc++] = r;
    }
    if (nc == 0) return 1 % m;
    return cand[rint_(nc)];
}

static void set_pw(void) {
    pw[0] = 1 % M_;
    for (int b = 1; b < T_; b++) pw[b] = (int)((long long)pw[b - 1] * R_ % M_);
}

static void shuffle_perm(int *p, int n) {
    for (int i = 0; i < n; i++) p[i] = i;
    for (int i = n - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = p[i]; p[i] = p[j]; p[j] = t;
    }
}

static void random_state(void) {
    int tmp[MAXK];
    for (int l = 0; l < d_; l++) {
        shuffle_perm(tmp, K_);
        for (int i = 0; i < K_; i++) {
            sig[l * K_ + i] = tmp[i];
            inv_[l * K_ + tmp[i]] = i;
            S[l * K_ + i] = rint_(G_);
        }
    }
}

static void build_adj(void) {
    int G = G_, K = K_, d = d_;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            int j = sig[l * K + i], s = S[l * K + i];
            for (int x = 0; x < G; x++) {
                int A = i * G + x;
                int B = (K + j) * G + gmul(x, s);
                adj_[A * d + l] = B;
                adj_[B * d + l] = A;
            }
        }
}

static int dupcount(void) {
    int dup = 0;
    for (int i = 0; i < K_; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++)
                if (sig[l1 * K_ + i] == sig[l2 * K_ + i] && S[l1 * K_ + i] == S[l2 * K_ + i])
                    dup++;
    return dup;
}

static long long eval_cost(void) {
    build_adj();
    int K = K_, G = G_, d = d_, N = N_;
    long long total = 0;
    for (int b = 0; b < 2 * K; b++) {
        int src = b * G;
        curst++;
        int h = 0, t = 0;
        stampv[src] = curst; distv[src] = 0; qv[t++] = src;
        int vis = 1;
        while (h < t) {
            int v = qv[h++];
            int dv = distv[v];
            if (dv >= D_) continue;
            const int *nb = &adj_[v * d];
            for (int l = 0; l < d; l++) {
                int u = nb[l];
                if (stampv[u] != curst) {
                    stampv[u] = curst;
                    distv[u] = dv + 1;
                    qv[t++] = u;
                    vis++;
                }
            }
        }
        badtmp[b] = N - vis;
        total += N - vis;
    }
    return total + 1000LL * dupcount();
}

static int anneal(double slice) {
    random_state();
    long long cost = eval_cost();
    memcpy(badcur, badtmp, sizeof(int) * 2 * K_);
    clock_t c0 = clock();
    double T = 4.0;
    long it = 0;
    while (cost != 0) {
        if ((it & 31) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= slice) break;
            double fr = el / slice;
            T = 4.0 * pow(0.05, fr);
        }
        it++;
        if (rint_(4) == 0 && K_ >= 2) {
            int l = rint_(d_);
            int i1 = rint_(K_), i2 = rint_(K_ - 1);
            if (i2 >= i1) i2++;
            int a1 = sig[l * K_ + i1], a2 = sig[l * K_ + i2];
            sig[l * K_ + i1] = a2; sig[l * K_ + i2] = a1;
            inv_[l * K_ + a2] = i1; inv_[l * K_ + a1] = i2;
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
                memcpy(badcur, badtmp, sizeof(int) * 2 * K_);
            } else {
                sig[l * K_ + i1] = a1; sig[l * K_ + i2] = a2;
                inv_[l * K_ + a1] = i1; inv_[l * K_ + a2] = i2;
            }
        } else {
            int l = rint_(d_), i = rint_(K_);
            if (rdbl() < 0.5) {
                int b = -1;
                for (int t = 0; t < 8; t++) {
                    int c = rint_(2 * K_);
                    if (badcur[c] > 0) { b = c; break; }
                }
                if (b >= 0) {
                    if (b < K_) i = b;
                    else i = inv_[l * K_ + (b - K_)];
                }
            }
            int idx = l * K_ + i;
            int old = S[idx];
            int nw = rint_(G_);
            if (nw == old) continue;
            S[idx] = nw;
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
                memcpy(badcur, badtmp, sizeof(int) * 2 * K_);
            } else {
                S[idx] = old;
            }
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 8) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    K_ = atoi(argv[5]);
    T_ = atoi(argv[6]);
    int m = atoi(argv[7]);
    if (d_ < 1 || d_ > MAXD || D_ < 1 || K_ < 1 || K_ > MAXK || T_ < 1 || T_ > 60 || m < 2) {
        printf("0 0\n");
        return 0;
    }
    for (int w = 0; w < 20; w++) rnd();

    clock_t c0 = clock();
    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        double left = limit - el;
        if (left < 0.3) break;
        if (m * T_ > MAXG) break;
        M_ = m;
        G_ = m * T_;
        N_ = 2 * K_ * G_;
        R_ = pick_r(m, T_);
        set_pw();
        double slice = limit / 5.0;
        if (slice < 1.0) slice = 1.0;
        if (slice > left) slice = left;
        if (anneal(slice)) {
            bestFound = 1;
            bestM = M_;
            bestR = R_;
            bestG = G_;
            memcpy(bsig, sig, sizeof(int) * d_ * K_);
            memcpy(bS, S, sizeof(int) * d_ * K_);
            m++;
        }
    }

    if (!bestFound) {
        printf("0 0\n");
        return 0;
    }
    M_ = bestM;
    R_ = bestR;
    G_ = bestG;
    set_pw();
    memcpy(sig, bsig, sizeof(int) * d_ * K_);
    memcpy(S, bS, sizeof(int) * d_ * K_);
    int K = K_, G = G_, d = d_;
    printf("%d %d\n", 2 * K * G, d * K * G);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            int j = sig[l * K + i], s = S[l * K + i];
            for (int x = 0; x < G; x++) {
                int A = i * G + x;
                int B = (K + j) * G + gmul(x, s);
                printf("%d %d\n", A, B);
            }
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
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

    # Voltage-lift sweeps in C over several small base sizes and group types.
    # (k base blocks per side, t = order of the Z_t factor in Z_m x| Z_t.)
    deadline = t0 + max(2.0, 0.85 * time_limit - 2.0)
    moore = lib.moore_bound(d, D)
    configs = [(2, 1), (4, 1), (3, 2), (2, 3)]
    for idx, (k, t) in enumerate(configs):
        remaining = deadline - time.monotonic()
        left = len(configs) - idx
        budget = remaining / left - 0.5
        if budget < 1.5:
            continue
        m0 = max(2, moore // (4 * 2 * k * t))  # start near a quarter of the Moore bound
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed * 7 + idx + 1, f"{budget:.2f}", k, t, m0],
                            timeout=budget + 15.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
