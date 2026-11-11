import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley voltage-lift annealer over semidirect products
# Z_m x| Z_k2, with k base blocks per side.
#
# A lift with k blocks per side and d layers: each layer l is a permutation
# P_l of the blocks, and each A-block i carries a voltage S[l][i] in the group.
# Vertex (block b, element x) is joined to (block k+P_l[i], x*S) for A-block i.
# Left multiplication by any group element is an automorphism, so the lift is
# valid (diameter <= D) iff every one of the 2k identity vertices reaches all
# N vertices within D steps. This is checked with one bitset BFS over
# 2k sources (instead of all N sources), so one evaluation costs O(D*d*N).
# Cost = unreached (source, vertex) pairs + PEN * (duplicate dart keys).
# Moves: swap two blocks within a layer, or change one voltage, with the
# endpoint biased toward vertices that are still unreached. Each trial samples a
# new group just above the current best order, and the best valid lift is kept.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;
typedef uint32_t u32;

#define PEN 60

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, K_, G_, m_, k2_, N_;
static int *ga, *gb, *powr, *P, *S, *nbr, *Pold, *Sold;
static u32 *cur, *cand, *wa, *wb;
static int best_n = 0, best_m = 0, found = 0;
static int *bestU = NULL, *bestV = NULL;
static clock_t c0;
static double limit;

static double elapsed(void) { return (double)(clock() - c0) / CLOCKS_PER_SEC; }

static long long powmod(long long b, long long e, long long mod) {
    long long r = 1 % mod;
    b %= mod; if (b < 0) b += mod;
    while (e > 0) {
        if (e & 1) r = r * b % mod;
        b = b * b % mod;
        e >>= 1;
    }
    return r;
}

static int gcdi(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

/* Random Z_m x| Z_k2 with r^k2 = 1 mod m, order m*k2 >= target. */
static int sample_group(int target, int *mo, int *ko, int *ro) {
    static const int K2S[] = {1,2,2,3,4,4,5,6,6,8,8,9,10,12,12,14,16,18,20,24};
    const int nk = (int)(sizeof(K2S) / sizeof(K2S[0]));
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2S[rint_(nk)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = -1;
        if (k2 == 1) {
            r = 1;
        } else {
            for (int t = 0; t < 300 && r < 0; t++) {
                int c = 1 + rint_(m - 1);
                if (gcdi(c, m) == 1 && powmod(c, k2, m) == 1 % m) r = c;
            }
            if (r < 0 && k2 % 2 == 0) r = m - 1;   /* (m-1)^k2 = 1 for even k2 */
        }
        if (r < 0) continue;
        *mo = m; *ko = k2; *ro = r;
        return 1;
    }
    return 0;
}

static inline int gmul(int x, int y) {
    int a = ga[x], b = gb[x], c = ga[y], dd = gb[y];
    int A = (a + (powr[b] * c) % m_) % m_;
    int Bv = (b + dd) % k2_;
    return A * k2_ + Bv;
}

static inline int ginv(int x) {
    int a = ga[x], b = gb[x];
    int nb = (k2_ - b) % k2_;
    int t = (powr[nb] * a) % m_;
    int A = (m_ - t) % m_;
    return A * k2_ + nb;
}

static void build_nbr(void) {
    int d = d_, K = K_, G = G_;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) {
            int idx = l * K + i;
            int j = P[idx], s = S[idx];
            int si = ginv(s);
            for (int x = 0; x < G; x++) {
                int v = i * G + x;
                nbr[(size_t)v * d + l] = (K + j) * G + gmul(x, s);
            }
            for (int y = 0; y < G; y++) {
                int v = (K + j) * G + y;
                nbr[(size_t)v * d + l] = i * G + gmul(y, si);
            }
        }
    }
}

/* Number of duplicated (block, target block, voltage) darts. */
static int dupcount(void) {
    int dup = 0;
    int L = d_ * K_;
    for (int a = 0; a < L; a++) {
        int ia = a % K_;
        for (int b = 0; b < a; b++) {
            if (b % K_ == ia && P[b] == P[a] && S[b] == S[a]) { dup++; break; }
        }
    }
    return dup;
}

/* Fills out[v] = bitmask of the 2K sources within distance D of v.
   Returns the number of unreached (source, vertex) pairs. */
static long long evaluate(u32 *out) {
    int N = N_, d = d_, nsrc = 2 * K_;
    u32 *a = wa, *b = wb;
    memset(a, 0, sizeof(u32) * (size_t)N);
    for (int s = 0; s < nsrc; s++) a[(size_t)s * G_] = 1u << s;
    for (int t = 0; t < D_; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u32 x = a[v];
            const int *nb = nbr + (size_t)v * d;
            for (int l = 0; l < d; l++) x |= a[nb[l]];
            b[v] = x;
            if (x != a[v]) changed = 1;
        }
        u32 *tp = a; a = b; b = tp;
        if (!changed) break;
    }
    long long pc = 0;
    for (int v = 0; v < N; v++) {
        out[v] = a[v];
        pc += __builtin_popcount(a[v]);
    }
    return (long long)nsrc * N - pc;
}

static int run_trial(int iters, int patience, double T0, double T1) {
    int L = d_ * K_;
    int N = N_;
    u32 full = (1u << (2 * K_)) - 1;
    build_nbr();
    long long cost = evaluate(cur) + PEN * (long long)dupcount();
    long long bestc = cost;
    int last_imp = 0;
    for (int it = 0; it < iters && cost != 0; it++) {
        if (it - last_imp > patience) break;
        if (((it & 31) == 0) && elapsed() >= limit) break;
        double frac = (double)it / iters;
        double T = T0 * pow(T1 / T0, frac);
        memcpy(Pold, P, sizeof(int) * L);
        memcpy(Sold, S, sizeof(int) * L);
        if (K_ >= 2 && rdbl() < 0.2) {
            int l = rint_(d_);
            int i1 = rint_(K_);
            int i2 = rint_(K_ - 1);
            if (i2 >= i1) i2++;
            int t = P[l * K_ + i1]; P[l * K_ + i1] = P[l * K_ + i2]; P[l * K_ + i2] = t;
        } else {
            int idx = -1;
            if (rdbl() < 0.5) {
                for (int tries = 0; tries < 30; tries++) {
                    int v = rint_(N);
                    if (cur[v] != full) {
                        int blk = v / G_;
                        if (blk < K_) {
                            idx = rint_(d_) * K_ + blk;
                        } else {
                            int j = blk - K_;
                            int l = rint_(d_);
                            for (int i = 0; i < K_; i++)
                                if (P[l * K_ + i] == j) { idx = l * K_ + i; break; }
                        }
                        break;
                    }
                }
            }
            if (idx < 0) idx = rint_(L);
            S[idx] = (S[idx] + 1 + rint_(G_ - 1)) % G_;
        }
        build_nbr();
        long long nc = evaluate(cand) + PEN * (long long)dupcount();
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
            u32 *tp = cur; cur = cand; cand = tp;
            if (cost < bestc) { bestc = cost; last_imp = it; }
        } else {
            memcpy(P, Pold, sizeof(int) * L);
            memcpy(S, Sold, sizeof(int) * L);
            build_nbr();
        }
    }
    return cost == 0;
}

static void save_edges(void) {
    int A = K_ * G_;
    int cnt = A * d_;
    free(bestU); free(bestV);
    bestU = malloc(sizeof(int) * (size_t)cnt);
    bestV = malloc(sizeof(int) * (size_t)cnt);
    int e = 0;
    for (int v = 0; v < A; v++)
        for (int l = 0; l < d_; l++) {
            bestU[e] = v;
            bestV[e] = nbr[(size_t)v * d_ + l];
            e++;
        }
    best_m = e;
}

static void free_trial(void) {
    free(ga); free(gb); free(powr); free(P); free(S); free(Pold); free(Sold);
    free(nbr); free(cur); free(cand); free(wa); free(wb);
    ga = gb = powr = P = S = Pold = Sold = nbr = NULL;
    cur = cand = wa = wb = NULL;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int w = 0; w < 10; w++) rnd();
    limit = atof(argv[4]);
    int lower = atoi(argv[5]);
    if (d_ < 2 || D_ < 2 || limit <= 0) { printf("0 0\n"); return 0; }
    best_n = lower;
    c0 = clock();

    while (elapsed() < limit) {
        K_ = 1 + rint_(6);
        int minG = best_n / (2 * K_) + 1;
        int Gt = minG + rint_(1 + minG / 40);
        int mm, kk, rr;
        if (!sample_group(Gt, &mm, &kk, &rr)) continue;
        m_ = mm; k2_ = kk; G_ = mm * kk; N_ = 2 * K_ * G_;
        int L = d_ * K_;
        ga = malloc(sizeof(int) * G_);
        gb = malloc(sizeof(int) * G_);
        powr = malloc(sizeof(int) * k2_);
        P = malloc(sizeof(int) * L);
        S = malloc(sizeof(int) * L);
        Pold = malloc(sizeof(int) * L);
        Sold = malloc(sizeof(int) * L);
        nbr = malloc(sizeof(int) * (size_t)N_ * d_);
        cur = malloc(sizeof(u32) * N_);
        cand = malloc(sizeof(u32) * N_);
        wa = malloc(sizeof(u32) * N_);
        wb = malloc(sizeof(u32) * N_);
        if (!ga || !gb || !powr || !P || !S || !Pold || !Sold || !nbr ||
            !cur || !cand || !wa || !wb) {
            free_trial();
            continue;
        }
        for (int x = 0; x < G_; x++) { ga[x] = x / k2_; gb[x] = x % k2_; }
        for (int b = 0; b < k2_; b++) powr[b] = (int)powmod(rr, b, m_);
        for (int l = 0; l < d_; l++) {
            for (int i = 0; i < K_; i++) P[l * K_ + i] = i;
            for (int i = K_ - 1; i > 0; i--) {
                int j = rint_(i + 1);
                int t = P[l * K_ + i]; P[l * K_ + i] = P[l * K_ + j]; P[l * K_ + j] = t;
            }
        }
        for (int idx = 0; idx < L; idx++) S[idx] = rint_(G_);

        int ok = run_trial(40000, 10000, 6.0, 0.3);
        if (ok && N_ > best_n) {
            save_edges();
            best_n = N_;
            found = 1;
        }
        free_trial();
    }

    if (!found) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int e = 0; e < best_m; e++) printf("%d %d\n", bestU[e], bestV[e]);
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            # Calibration: the projective plane is exact when d-1 is a prime power.
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 3 and d >= 2:
        budget = time_limit - (time.monotonic() - t0) - 5.0
        if budget >= 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, int(seed), f"{budget:.2f}", best[0]],
                                timeout=budget + 25.0)
                consider(*lib.parse_graph_text(out))
            except Exception:
                pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
