import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley voltage-lift annealer over semidirect products
# Z_M x| Z_K2 (element a*K2+b). A lift has 2K blocks of G vertices. Layer l is
# a perfect matching of A-blocks to B-blocks, and each dart carries a voltage
# s in G, so A(i,x) ~ B(j, x*s). Left multiplication is an automorphism, so
# the diameter test only needs balls around the 2K identity vertices. These
# are tracked as 2K-bit masks and iterated D times. The annealer minimises the
# number of unreached (block, vertex) pairs plus a penalty for duplicate darts.
# Groups are sampled at order just above the current best, so the search keeps
# pushing the vertex count up.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define TRIAL_ITERS 20000

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) { return (double)clock() / CLOCKS_PER_SEC; }

static const int KLIST[] = {1,1,2,2,3,3,4,5,6,8,9,10,12,15,16,19};
static const int K2LIST[] = {1,1,2,2,3,4,5,6,7,8,9,10,12,14,16,18,20,24,30,36};

static int d_, D_;
static int K, G, N;
static int M_, K2_, R_;
static int *rpow, *nbr, *perm, *S;
static u64 *cur, *nxt;

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return (int)r;
}

static int gmul(int x, int y) {
    int a = x / K2_, b = x % K2_;
    int c = y / K2_, e = y % K2_;
    int aa = (int)(((long long)rpow[b] * c + a) % M_);
    int bb = (b + e) % K2_;
    return aa * K2_ + bb;
}

static int ginv(int x) {
    int a = x / K2_, b = x % K2_;
    int nb = (K2_ - b) % K2_;
    long long na = ((long long)(M_ - rpow[nb]) % M_) * a % M_;
    return (int)na * K2_ + nb;
}

static void set_dart(int l, int i) {
    int idx = l * K + i;
    int j = perm[idx], s = S[idx];
    int si = ginv(s);
    for (int x = 0; x < G; x++) {
        int A = i * G + x;
        int B = (K + j) * G + x;
        nbr[(size_t)A * d_ + l] = (K + j) * G + gmul(x, s);
        nbr[(size_t)B * d_ + l] = i * G + gmul(x, si);
    }
}

static long long evaluate(void) {
    int twoK = 2 * K;
    u64 full = (1ULL << twoK) - 1;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < twoK; b++) cur[(size_t)b * G] |= 1ULL << b;
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 x = cur[v];
            const int *nb = nbr + (size_t)v * d_;
            for (int l = 0; l < d_; l++) x |= cur[nb[l]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        u64 *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long long miss = 0;
    for (int v = 0; v < N; v++) miss += __builtin_popcountll(full & ~cur[v]);
    return miss;
}

static long long dupcount(void) {
    long long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++)
                if (perm[l1 * K + i] == perm[l2 * K + i] && S[l1 * K + i] == S[l2 * K + i])
                    c++;
    return c;
}

static int sample_group(int targetG) {
    const int nk2 = (int)(sizeof(K2LIST) / sizeof(K2LIST[0]));
    for (int tr = 0; tr < 300; tr++) {
        int k2 = K2LIST[rint_(nk2)];
        int m = (targetG + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (k2 == 1) { M_ = m; K2_ = 1; R_ = 1; return 1; }
        int r = 1;
        if (m >= 3 && rint_(3) != 0) {
            int ok = 0;
            for (int t = 0; t < 80; t++) {
                int c = 2 + rint_(m - 2);
                if (gcd_(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; ok = 1; break; }
            }
            if (!ok) continue;
        }
        M_ = m; K2_ = k2; R_ = r;
        return 1;
    }
    return 0;
}

static int trial(long long iters, double deadline) {
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K; i++) perm[l * K + i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[l * K + i]; perm[l * K + i] = perm[l * K + j]; perm[l * K + j] = t;
        }
        for (int i = 0; i < K; i++) S[l * K + i] = rint_(G);
    }
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);

    long long pen = 4LL * N + 10;
    long long cost = evaluate() + pen * dupcount();
    double T0 = 2.0 + 0.02 * (double)cost, T1 = 0.3;

    for (long long t = 0; t < iters && cost > 0; t++) {
        if ((t & 127) == 0 && now_s() >= deadline) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        if (K >= 2 && rint_(100) < 25) {
            int l = rint_(d_);
            int i1 = rint_(K), i2 = rint_(K - 1);
            if (i2 >= i1) i2++;
            int *p = perm + l * K;
            int tmp = p[i1]; p[i1] = p[i2]; p[i2] = tmp;
            set_dart(l, i1); set_dart(l, i2);
            long long nc = evaluate() + pen * dupcount();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                tmp = p[i1]; p[i1] = p[i2]; p[i2] = tmp;
                set_dart(l, i1); set_dart(l, i2);
            }
        } else {
            int l = rint_(d_), i = rint_(K);
            int idx = l * K + i;
            int old = S[idx], nw = rint_(G);
            if (nw == old) continue;
            S[idx] = nw;
            set_dart(l, i);
            long long nc = evaluate() + pen * dupcount();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                S[idx] = old;
                set_dart(l, i);
            }
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    if (d_ < 1 || D_ < 1) { printf("0 0\n"); return 0; }
    for (int w = 0; w < 20; w++) rnd();

    int best_n = 0, best_m = 0;
    int *bu = NULL, *bv = NULL;
    const int nk = (int)(sizeof(KLIST) / sizeof(KLIST[0]));

    while (now_s() < limit) {
        K = KLIST[rint_(nk)];
        int minG = best_n / (2 * K) + 1;
        int tG = minG + rint_(minG / 16 + 2);
        if (!sample_group(tG)) continue;
        G = M_ * K2_;
        N = 2 * K * G;
        if (N <= best_n) continue;

        nbr = malloc(sizeof(int) * (size_t)N * d_);
        perm = malloc(sizeof(int) * (size_t)d_ * K);
        S = malloc(sizeof(int) * (size_t)d_ * K);
        cur = malloc(sizeof(u64) * (size_t)N);
        nxt = malloc(sizeof(u64) * (size_t)N);
        rpow = malloc(sizeof(int) * (size_t)K2_);
        if (!nbr || !perm || !S || !cur || !nxt || !rpow) {
            free(nbr); free(perm); free(S); free(cur); free(nxt); free(rpow);
            break;
        }
        for (int b = 0; b < K2_; b++) rpow[b] = powmod(R_, b, M_);

        if (trial(TRIAL_ITERS, limit)) {
            int m = K * G * d_;
            int *nu = malloc(sizeof(int) * (size_t)m);
            int *nv = malloc(sizeof(int) * (size_t)m);
            if (nu && nv) {
                int c = 0;
                for (int v = 0; v < K * G; v++)
                    for (int l = 0; l < d_; l++) {
                        nu[c] = v;
                        nv[c] = nbr[(size_t)v * d_ + l];
                        c++;
                    }
                free(bu); free(bv);
                bu = nu; bv = nv;
                best_n = N; best_m = m;
            } else {
                free(nu); free(nv);
            }
        }
        free(nbr); free(perm); free(S); free(cur); free(nxt); free(rpow);
    }

    if (best_n == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bu[i], bv[i]);
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
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 when d - 1 is a prime power (calibration case).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Main search: C voltage-lift annealer over semidirect-product groups.
    remaining = time_limit - (time.monotonic() - t0)
    budget = remaining - 10.0
    if budget >= 3.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=None, timeout=max(1.0, remaining - 4.0))
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
