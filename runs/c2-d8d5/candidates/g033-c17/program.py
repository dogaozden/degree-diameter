import time

import lib


# ----------------------------------------------------------------------------
# C engine: annealing over bi-Cayley lifts with semidirect-product groups.
#
# A bipartite graph is given by base blocks A_0..A_{k-1}, B_0..B_{k-1} with
# G = m*k2 vertices each, and d layers. Layer l sends A_i to B_{sig_l(i)} with
# voltage s_{l,i}: A(i,g) ~ B(sig_l(i), g*s_{l,i}). The group acts by left
# multiplication, which is an automorphism, so every vertex of a block looks
# the same. The diameter is at most D iff each of the 2k block identities
# reaches every vertex within D steps. Reach sets are 2k-bit masks, so one
# evaluation is D*N*d word operations. Cost = unreached (block, vertex) pairs
# plus a penalty per duplicate edge. Groups Z_m x| Z_k2 are sampled with
# order just above the best known order, so the search climbs.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define KMAX 6
#define PEN 40
#define STEPS 40000

static u64 rs = 88172645463325252ULL;
static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd64() % (u64)n); }
static double rndd(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, G_, m_, k2_, N_;
static u64 FULL;
static int *nbr = NULL, *sig = NULL, *volt = NULL, *pw = NULL;
static u64 *R1 = NULL, *R2 = NULL, *ACC = NULL;
static int *bestE = NULL;
static int bestN = 0, bestM = 0;
static clock_t c0;

static double elapsed(void) { return (double)(clock() - c0) / CLOCKS_PER_SEC; }

static int popc(u64 x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static int gcdi(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Element (a, b) of Z_m x| Z_k2 is coded as a*k2 + b, with (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_;
    int c = y / k2_, e = y % k2_;
    long long t = ((long long)a + (long long)pw[b] * c) % m_;
    return (int)t * k2_ + (b + e) % k2_;
}

static int ginv(int x) {
    int a = x / k2_, b = x % k2_;
    int nb = (k2_ - b) % k2_;
    long long t = (-(long long)pw[nb] * a) % m_;
    if (t < 0) t += m_;
    return (int)t * k2_ + nb;
}

static void set_dart(int l, int i) {
    int idx = l * k_ + i;
    int j = sig[idx], s = volt[idx];
    int si = ginv(s);
    for (int g = 0; g < G_; g++) {
        int v = i * G_ + g;
        nbr[(size_t)v * d_ + l] = (k_ + j) * G_ + gmul(g, s);
        int w = (k_ + j) * G_ + g;
        nbr[(size_t)w * d_ + l] = i * G_ + gmul(g, si);
    }
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < k_; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = l + 1; l2 < d_; l2++)
                if (sig[l * k_ + i] == sig[l2 * k_ + i] && volt[l * k_ + i] == volt[l2 * k_ + i])
                    c++;
    return c;
}

static u64 *eval(long long *cost) {
    int N = N_, nb2 = 2 * k_;
    u64 *cur = R1, *nxt = R2;
    memset(cur, 0, sizeof(u64) * (size_t)N);
    for (int b = 0; b < nb2; b++) cur[(size_t)b * G_] |= 1ULL << b;
    for (int t = 0; t < D_; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 x = cur[v];
            const int *nv = nbr + (size_t)v * d_;
            for (int l = 0; l < d_; l++) x |= cur[nv[l]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        u64 *tp = cur; cur = nxt; nxt = tp;
        if (!changed) break;
    }
    long long c = 0;
    for (int v = 0; v < N; v++) c += nb2 - popc(cur[v]);
    c += (long long)PEN * dupcount();
    *cost = c;
    return cur;
}

static int anneal(double T0, double T1, double tlimit) {
    long long cost;
    int N = N_;
    u64 *r = eval(&cost);
    memcpy(ACC, r, sizeof(u64) * (size_t)N);
    for (long long t = 0; t < STEPS && cost > 0; t++) {
        if ((t & 511) == 0 && elapsed() > tlimit) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)STEPS);
        if (k_ >= 2 && rndi(10) < 2) {
            int l = rndi(d_);
            int i1 = rndi(k_), i2 = rndi(k_ - 1);
            if (i2 >= i1) i2++;
            int a = l * k_ + i1, b = l * k_ + i2;
            int tmp = sig[a]; sig[a] = sig[b]; sig[b] = tmp;
            set_dart(l, i1); set_dart(l, i2);
            long long nc;
            u64 *rr = eval(&nc);
            if (nc <= cost || rndd() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
                memcpy(ACC, rr, sizeof(u64) * (size_t)N);
            } else {
                tmp = sig[a]; sig[a] = sig[b]; sig[b] = tmp;
                set_dart(l, i1); set_dart(l, i2);
            }
        } else {
            int l = -1, i = -1;
            if (rndi(2) == 0) {
                int v = -1;
                for (int tries = 0; tries < 40; tries++) {
                    int x = rndi(N);
                    if (ACC[x] != FULL) { v = x; break; }
                }
                if (v >= 0) {
                    int b = v / G_;
                    l = rndi(d_);
                    if (b < k_) {
                        i = b;
                    } else {
                        int j = b - k_;
                        for (int ii = 0; ii < k_; ii++)
                            if (sig[l * k_ + ii] == j) { i = ii; break; }
                    }
                }
            }
            if (i < 0) { l = rndi(d_); i = rndi(k_); }
            int idx = l * k_ + i;
            int nv = rndi(G_);
            if (nv == volt[idx]) continue;
            int old = volt[idx];
            volt[idx] = nv;
            set_dart(l, i);
            long long nc;
            u64 *rr = eval(&nc);
            if (nc <= cost || rndd() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
                memcpy(ACC, rr, sizeof(u64) * (size_t)N);
            } else {
                volt[idx] = old;
                set_dart(l, i);
            }
        }
    }
    return cost == 0;
}

static void save_graph(void) {
    int A = k_ * G_;
    int me = A * d_;
    bestE = realloc(bestE, sizeof(int) * 2 * (size_t)me);
    int c = 0;
    for (int v = 0; v < A; v++)
        for (int l = 0; l < d_; l++) {
            bestE[2 * c] = v;
            bestE[2 * c + 1] = nbr[(size_t)v * d_ + l];
            c++;
        }
    bestM = c;
    bestN = N_;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    int startN = argc > 5 ? atoi(argv[5]) : 0;
    if (d_ < 2 || D_ < 1 || limit <= 0) { printf("0 0\n"); return 0; }
    bestN = startN;
    static const int K2S[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    c0 = clock();

    while (elapsed() < limit - 0.3) {
        int k = 1 + rndi(KMAX);
        int Gmin = bestN / (2 * k) + 1;
        if (Gmin < 3) Gmin = 3;
        int Gt = Gmin + rndi(1 + Gmin / 40);
        int k2 = K2S[rndi(20)];
        if (k2 > Gt) k2 = 1;
        int m = (Gt + k2 - 1) / k2;
        if (m < 2) m = 2;
        int G = m * k2;
        int r = 1;
        if (k2 > 1 && m > 2 && rndi(3) > 0) {
            for (int tries = 0; tries < 300; tries++) {
                int c = 2 + rndi(m - 2);
                if (gcdi(c, m) != 1) continue;
                if (powmod(c, k2, m) != 1 % m) continue;
                r = c;
                break;
            }
        }

        k_ = k; k2_ = k2; m_ = m; G_ = G; N_ = 2 * k * G;
        FULL = (1ULL << (2 * k_)) - 1;
        pw = realloc(pw, sizeof(int) * (size_t)k2_);
        nbr = realloc(nbr, sizeof(int) * (size_t)N_ * d_);
        sig = realloc(sig, sizeof(int) * (size_t)k_ * d_);
        volt = realloc(volt, sizeof(int) * (size_t)k_ * d_);
        R1 = realloc(R1, sizeof(u64) * (size_t)N_);
        R2 = realloc(R2, sizeof(u64) * (size_t)N_);
        ACC = realloc(ACC, sizeof(u64) * (size_t)N_);
        if (!pw || !nbr || !sig || !volt || !R1 || !R2 || !ACC) break;

        long long p = 1 % m;
        for (int t = 0; t < k2_; t++) { pw[t] = (int)p; p = p * r % m; }

        for (int l = 0; l < d_; l++) {
            for (int i = 0; i < k_; i++) sig[l * k_ + i] = i;
            for (int i = k_ - 1; i > 0; i--) {
                int j = rndi(i + 1);
                int tmp = sig[l * k_ + i]; sig[l * k_ + i] = sig[l * k_ + j]; sig[l * k_ + j] = tmp;
            }
        }
        for (int idx = 0; idx < k_ * d_; idx++) volt[idx] = rndi(G_);
        for (int l = 0; l < d_; l++)
            for (int i = 0; i < k_; i++) set_dart(l, i);

        int ok = anneal(4.0, 0.15, limit);
        if (ok && 2 * k * G > bestN) save_graph();
    }

    if (bestM == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestE[2 * i], bestE[2 * i + 1]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: fallback constructions, then one C run for the bi-Cayley search.
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

    # Bi-Cayley lift search in C, climbing from the current fallback order.
    budget = min(0.85 * time_limit, time_limit - 7.0) - (time.monotonic() - t0)
    if budget >= 2.0 and d >= 2:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best[0]],
                            timeout=budget + 5.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
