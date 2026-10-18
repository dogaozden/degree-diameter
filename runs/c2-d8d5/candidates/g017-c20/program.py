import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage-lift annealer over semidirect products Z_m x| Z_k2.
#
# A bipartite graph with k blocks per side is a lift of a d-regular bipartite
# base multigraph (d perfect matchings between the blocks). Vertex (i, x) of
# A-block i is joined in layer l to (T[l][i], x * S[l][i]) on the B side, with
# x * s taken in the group. The graph is invariant under left multiplication,
# so the diameter is at most D iff every vertex is within distance D of each of
# the 2k block identities. Cost = unreached (vertex, identity) pairs
# + PEN * duplicate darts. The search samples a group and k, anneals voltages
# and layer permutations until cost 0, and keeps the largest success.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
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

static double wall(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

#define PEN 40

static int d_, D_;
static int K_, G_, M_, K2_, R_, N_;
static int *pw_, *T_, *S_, *invT_, *nbt_;
static u64 *rA_, *rB_;

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int powmod_(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return (int)r;
}

/* Semidirect product Z_M x| Z_K2, element a*K2 + b, (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / K2_, b = x % K2_;
    int c = y / K2_, e = y % K2_;
    long long t = ((long long)a + (long long)pw_[b] * c) % M_;
    return (int)(t * K2_ + (b + e) % K2_);
}

/* Inverse of (a,b) is (-r^(-b) a, -b). */
static int ginv(int x) {
    int a = x / K2_, b = x % K2_;
    int nbb = (K2_ - b) % K2_;
    long long c = ((long long)((M_ - a) % M_) * pw_[nbb]) % M_;
    return (int)(c * K2_ + nbb);
}

static void set_group(int k, int G, int M, int K2, int r) {
    K_ = k; G_ = G; M_ = M; K2_ = K2; R_ = r; N_ = 2 * k * G;
    pw_[0] = 1 % M;
    for (int b = 1; b < K2; b++) pw_[b] = (int)(((long long)pw_[b - 1] * r) % M);
}

static void build_nb(void) {
    int K = K_, G = G_, N = N_, d = d_;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++)
            invT_[l * K + T_[l * K + i]] = i;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) {
            int t = T_[l * K + i], s = S_[l * K + i];
            for (int x = 0; x < G; x++)
                nbt_[(size_t)l * N + i * G + x] = (K + t) * G + gmul(x, s);
        }
        for (int j = 0; j < K; j++) {
            int i = invT_[l * K + j];
            int si = ginv(S_[l * K + i]);
            for (int y = 0; y < G; y++)
                nbt_[(size_t)l * N + (K + j) * G + y] = i * G + gmul(y, si);
        }
    }
}

static long long eval_cost(void) {
    build_nb();
    int N = N_, d = d_, K = K_, G = G_;
    u64 *cur = rA_, *nxt = rB_;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[b * G] |= (u64)1 << b;
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 r = cur[v];
            for (int l = 0; l < d; l++) r |= cur[nbt_[(size_t)l * N + v]];
            nxt[v] = r;
            if (r != cur[v]) changed = 1;
        }
        u64 *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long long cost = 0;
    for (int v = 0; v < N; v++) cost += 2 * K - __builtin_popcountll(cur[v]);
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (T_[l * K + i] == T_[l2 * K + i] && S_[l * K + i] == S_[l2 * K + i]) dup++;
    return cost + (long long)PEN * dup;
}

static int anneal(double until) {
    int K = K_, G = G_, d = d_;
    for (int l = 0; l < d; l++) {
        int *Tl = T_ + l * K;
        for (int i = 0; i < K; i++) Tl[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int tmp = Tl[i]; Tl[i] = Tl[j]; Tl[j] = tmp;
        }
        for (int i = 0; i < K; i++) S_[l * K + i] = rint_(G);
    }
    long long cost = eval_cost();
    const double T0 = 8.0, T1 = 0.2;
    double t_start = wall();
    double span = until - t_start;
    if (span <= 0) span = 1e-9;
    double temp = T0;
    for (long long it = 0; cost != 0; it++) {
        if ((it & 63) == 0) {
            double now = wall();
            if (now >= until) break;
            double frac = (now - t_start) / span;
            temp = T0 * pow(T1 / T0, frac);
        }
        int mv = rint_(10);
        if (mv < 6 || K < 2) {
            int l = rint_(d), i = rint_(K);
            int idx = l * K + i;
            int old = S_[idx], nv = rint_(G);
            if (nv == old) continue;
            S_[idx] = nv;
            long long nc = eval_cost();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / temp)) cost = nc;
            else S_[idx] = old;
        } else if (mv < 8) {
            int l = rint_(d), i1 = rint_(K), i2 = rint_(K);
            if (i1 == i2) continue;
            int a1 = l * K + i1, a2 = l * K + i2;
            int t1 = T_[a1], t2 = T_[a2];
            T_[a1] = t2; T_[a2] = t1;
            long long nc = eval_cost();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / temp)) cost = nc;
            else { T_[a1] = t1; T_[a2] = t2; }
        } else {
            int l = rint_(d), i1 = rint_(K), i2 = rint_(K);
            if (i1 == i2) continue;
            int a1 = l * K + i1, a2 = l * K + i2;
            int s1 = S_[a1], s2 = S_[a2];
            S_[a1] = s2; S_[a2] = s1;
            long long nc = eval_cost();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / temp)) cost = nc;
            else { S_[a1] = s1; S_[a2] = s2; }
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    int min_n = argc > 5 ? atoi(argv[5]) : 0;
    int kmax = argc > 6 ? atoi(argv[6]) : 8;
    if (kmax < 1) kmax = 1;
    if (kmax > 16) kmax = 16;
    rs ^= (u64)seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d_ < 1 || d_ > 64 || D_ < 1) {
        printf("0 0\n");
        return 0;
    }

    double t0 = wall();
    double deadline = t0 + limit;
    int best_n = min_n;
    int found = 0;
    int bestK = 0, bestG = 0, bestM = 0, bestK2 = 1, bestR = 0;
    int *bestT = malloc(sizeof(int) * (size_t)d_ * kmax);
    int *bestS = malloc(sizeof(int) * (size_t)d_ * kmax);
    T_ = malloc(sizeof(int) * (size_t)d_ * kmax);
    S_ = malloc(sizeof(int) * (size_t)d_ * kmax);
    invT_ = malloc(sizeof(int) * (size_t)d_ * kmax);
    if (!bestT || !bestS || !T_ || !S_ || !invT_) {
        printf("0 0\n");
        return 0;
    }

    while (wall() < deadline) {
        int k = 1 + rint_(kmax);
        int Gmin = best_n / (2 * k) + 1;
        int span = Gmin / 25 + 1;
        int G = Gmin + rint_(span);
        if (rint_(4) == 0) G = Gmin;

        int K2 = 1;
        if (rint_(3) != 0) {
            int lim = G < 40 ? G : 40;
            for (int a = 0; a < 40; a++) {
                int c = 1 + rint_(lim);
                if (G % c == 0) { K2 = c; break; }
            }
        }
        int M = G / K2;
        int r = 0, okg = 1;
        if (K2 > 1 && M > 1) {
            okg = 0;
            for (int a = 0; a < 300; a++) {
                int c = 1 + rint_(M - 1);
                if (gcd_(c, M) == 1 && powmod_(c, K2, M) == 1 % M) { r = c; okg = 1; break; }
            }
        }
        if (!okg) continue;

        int Nn = 2 * k * G;
        pw_ = malloc(sizeof(int) * (size_t)K2);
        nbt_ = malloc(sizeof(int) * (size_t)d_ * (size_t)Nn);
        rA_ = malloc(sizeof(u64) * (size_t)Nn);
        rB_ = malloc(sizeof(u64) * (size_t)Nn);
        if (!pw_ || !nbt_ || !rA_ || !rB_) {
            free(pw_); free(nbt_); free(rA_); free(rB_);
            break;
        }
        set_group(k, G, M, K2, r);

        double until = wall() + 3.0;
        if (until > deadline) until = deadline;
        int ok = anneal(until);

        if (ok && Nn > best_n) {
            best_n = Nn;
            found = 1;
            bestK = k; bestG = G; bestM = M; bestK2 = K2; bestR = r;
            memcpy(bestT, T_, sizeof(int) * (size_t)d_ * k);
            memcpy(bestS, S_, sizeof(int) * (size_t)d_ * k);
        }
        free(pw_); free(nbt_); free(rA_); free(rB_);
        pw_ = NULL; nbt_ = NULL; rA_ = NULL; rB_ = NULL;
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    int K = bestK, G = bestG;
    pw_ = malloc(sizeof(int) * (size_t)bestK2);
    if (!pw_) { printf("0 0\n"); return 0; }
    set_group(K, G, bestM, bestK2, bestR);
    printf("%d %d\n", best_n, K * d_ * G);
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d_; l++)
            for (int x = 0; x < G; x++) {
                int u = i * G + x;
                int v = (K + bestT[l * K + i]) * G + gmul(x, bestS[l * K + i]);
                printf("%d %d\n", u, v);
            }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue and fallback constructions.
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
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact optimum for this calibration case

    remaining = time_limit - (time.monotonic() - t0)
    budget = min(0.85 * remaining, remaining - 8.0)
    if budget >= 3.0:
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, int(seed) & 0x7FFFFFFF, f"{budget:.2f}", best[0], 8],
                stdin_graph=None,
                timeout=max(2.0, remaining - 2.0),
            )
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
