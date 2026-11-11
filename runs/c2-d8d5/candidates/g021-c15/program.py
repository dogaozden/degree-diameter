import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts.
#
# A bi-Cayley lift uses the group G = Z_m x| Z_k2 (element a*k2+b, product
# (a,b)(c,d) = (a + r^b c, b+d)) and K blocks per side. Each of the d layers
# is a permutation of blocks plus one voltage per left block. Left vertex
# (i,x) joins right vertex (j, x*s); G acts by left multiplication, so the
# graph has diameter <= D iff every vertex is within D of each block
# representative (b,1). Reach is tracked as a bitmask over 2K blocks, which
# is far cheaper than full-vertex bitsets. The search uses many groups in one
# run, with a bandit over K. The best valid lift is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define DMAX 32
#define KB 8
#define KUSE 6
#define PENALTY 1000LL

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, K_, G_, N_, M_, K2_;
static int *pw_ = NULL;
static int *nbr_ = NULL;
static u64 *rA_ = NULL, *rB_ = NULL, *racc_ = NULL, *rlast_ = NULL;
static int layers_[DMAX][KB];
static int S_[DMAX][KB];
static int best_N = 0, best_d = 0;
static int *best_nbr = NULL;

static long lgcd(long a, long b) { while (b) { long t = a % b; a = b; b = t; } return a; }
static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gmul(int x, int y) {
    int a = x / K2_, b = x % K2_, c = y / K2_, e = y % K2_;
    long t = ((long)a + (long)pw_[b] * c) % M_;
    return (int)(t * K2_ + (b + e) % K2_);
}

static int ginv(int x) {
    int a = x / K2_, b = x % K2_;
    int nb = (K2_ - b) % K2_;
    long t = (long)pw_[nb] * a % M_;
    return (int)(((M_ - t) % M_) * K2_ + nb);
}

/* Left block i joins right block j with voltage s in layer l. */
static void set_dart(int l, int i, int j, int s) {
    const int G = G_, N = N_, K = K_;
    int *nb = nbr_ + (size_t)l * N;
    int si = ginv(s);
    for (int x = 0; x < G; x++) {
        nb[i * G + x] = (K + j) * G + gmul(x, s);
        nb[(K + j) * G + x] = i * G + gmul(x, si);
    }
}

/* Number of (vertex, block) pairs not reached from the block representatives within D. */
static long long unreached(void) {
    const int N = N_, G = G_, nb = 2 * K_, d = d_;
    u64 *cur = rA_, *nxt = rB_;
    memset(cur, 0, sizeof(u64) * (size_t)N);
    for (int b = 0; b < nb; b++) cur[(size_t)b * G] = 1ULL << b;
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr_[(size_t)l * N + v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
        if (!changed) break;
    }
    rlast_ = cur;
    long long unr = 0;
    for (int v = 0; v < N; v++) unr += nb - __builtin_popcountll(cur[v]);
    return unr;
}

/* Number of darts that repeat an earlier (block, target, voltage) key. */
static int dupcount(void) {
    int E = d_ * K_;
    int dup = 0;
    for (int e = 0; e < E; e++) {
        int l1 = e / K_, i1 = e % K_;
        int j1 = layers_[l1][i1], s1 = S_[l1][i1];
        for (int f = 0; f < e; f++) {
            int l2 = f / K_, i2 = f % K_;
            if (i2 == i1 && layers_[l2][i2] == j1 && S_[l2][i2] == s1) { dup++; break; }
        }
    }
    return dup;
}

static double elapsed(clock_t c0) { return (double)(clock() - c0) / CLOCKS_PER_SEC; }

static int sa_run(long iters, long patience, double limit, clock_t c0) {
    const int d = d_, K = K_, G = G_, N = N_;
    const u64 full = (1ULL << (2 * K)) - 1ULL;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) layers_[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = layers_[l][i]; layers_[l][i] = layers_[l][j]; layers_[l][j] = t;
        }
        for (int i = 0; i < K; i++) S_[l][i] = rint_(G);
        for (int i = 0; i < K; i++) set_dart(l, i, layers_[l][i], S_[l][i]);
    }
    long long cost = unreached() + PENALTY * (long long)dupcount();
    memcpy(racc_, rlast_, sizeof(u64) * (size_t)N);
    double c0v = cost > 1 ? (double)cost : 1.0;
    long long bestc = cost;
    long last = 0;
    for (long t = 0; t < iters && cost != 0; t++) {
        if (t - last > patience) break;
        if (elapsed(c0) > limit) break;
        double temp = 0.01 * c0v * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rdbl() < 0.25) {
            int l = rint_(d);
            int i1 = rint_(K), i2 = rint_(K - 1);
            if (i2 >= i1) i2++;
            int t1 = layers_[l][i1]; layers_[l][i1] = layers_[l][i2]; layers_[l][i2] = t1;
            set_dart(l, i1, layers_[l][i1], S_[l][i1]);
            set_dart(l, i2, layers_[l][i2], S_[l][i2]);
            long long c2 = unreached() + PENALTY * (long long)dupcount();
            if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(racc_, rlast_, sizeof(u64) * (size_t)N);
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                t1 = layers_[l][i1]; layers_[l][i1] = layers_[l][i2]; layers_[l][i2] = t1;
                set_dart(l, i1, layers_[l][i1], S_[l][i1]);
                set_dart(l, i2, layers_[l][i2], S_[l][i2]);
            }
            continue;
        }

        int l, i;
        if (rdbl() < 0.4) {
            int u = -1, cnt = 0;
            for (int v = 0; v < N; v++) {
                if (racc_[v] != full) { cnt++; if (rint_(cnt) == 0) u = v; }
            }
            if (u >= 0) {
                int blk = u / G;
                l = rint_(d);
                if (blk < K) i = blk;
                else {
                    i = -1;
                    for (int q = 0; q < K; q++) if (layers_[l][q] == blk - K) { i = q; break; }
                    if (i < 0) i = rint_(K);
                }
            } else { l = rint_(d); i = rint_(K); }
        } else { l = rint_(d); i = rint_(K); }

        int old = S_[l][i];
        int nw = rint_(G);
        if (nw == old) continue;
        S_[l][i] = nw;
        set_dart(l, i, layers_[l][i], nw);
        long long c2 = unreached() + PENALTY * (long long)dupcount();
        if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(racc_, rlast_, sizeof(u64) * (size_t)N);
            if (cost < bestc) { bestc = cost; last = t; }
        } else {
            S_[l][i] = old;
            set_dart(l, i, layers_[l][i], old);
        }
    }
    return cost == 0;
}

static const int K2OPT[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static int sample_group(long target, int *M, int *K2, int *R) {
    for (int att = 0; att < 100; att++) {
        int k2 = K2OPT[rint_(20)];
        long m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (m > 1000000) continue;
        int r = 1;
        if (k2 > 1 && m > 2) {
            int found = 0;
            if (k2 % 2 == 0 && rdbl() < 0.3) {
                long c = m - 1;
                if (lgcd(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = (int)c; found = 1; }
            }
            for (int tr = 0; !found && tr < 60; tr++) {
                long c = 2 + rint_((int)(m - 2));
                if (lgcd(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = (int)c; found = 1; }
            }
        }
        *M = (int)m; *K2 = k2; *R = r;
        return 1;
    }
    return 0;
}

static int group_setup(int M, int K2, int R) {
    M_ = M; K2_ = K2;
    free(pw_);
    pw_ = malloc(sizeof(int) * (size_t)K2);
    if (!pw_) return 0;
    long p = 1 % M;
    for (int b = 0; b < K2; b++) { pw_[b] = (int)p; p = p * R % M; }
    G_ = M * K2;
    return 1;
}

static int alloc_group(void) {
    size_t N = (size_t)N_;
    free(nbr_); free(rA_); free(rB_); free(racc_);
    nbr_ = malloc(sizeof(int) * (size_t)d_ * N);
    rA_ = malloc(sizeof(u64) * N);
    rB_ = malloc(sizeof(u64) * N);
    racc_ = malloc(sizeof(u64) * N);
    return nbr_ && rA_ && rB_ && racc_;
}

static void free_group(void) {
    free(nbr_); free(rA_); free(rB_); free(racc_);
    nbr_ = NULL; rA_ = NULL; rB_ = NULL; racc_ = NULL;
}

static void save_best(void) {
    int N = N_, d = d_;
    if (N <= best_N) return;
    int *nb = malloc(sizeof(int) * (size_t)d * N);
    if (!nb) return;
    memcpy(nb, nbr_, sizeof(int) * (size_t)d * N);
    free(best_nbr);
    best_nbr = nb;
    best_N = N;
    best_d = d;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    long hint = argc > 5 ? atol(argv[5]) : 2L * d_;
    if (d_ < 1 || d_ > DMAX || D_ < 1) { printf("0 0\n"); return 0; }

    clock_t c0 = clock();
    double wins[KB + 1], trials[KB + 1];
    for (int k = 0; k <= KB; k++) { wins[k] = 0; trials[k] = 0; }
    long goal = hint > 2L * d_ ? hint : 2L * d_;
    int fails = 0;

    while (elapsed(c0) < limit) {
        int k;
        if (rdbl() < 0.2) k = 1 + rint_(KUSE);
        else {
            double bv = -1.0;
            k = 1;
            for (int kk = 1; kk <= KUSE; kk++) {
                double v = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rdbl();
                if (v > bv) { bv = v; k = kk; }
            }
        }
        long ref = best_N > 0 ? best_N : goal;
        long base = ref / (2L * k);
        long target = base + 1 + rint_((int)(base / 8 + 2));
        int M, K2, R;
        if (!sample_group(target, &M, &K2, &R)) continue;
        if (!group_setup(M, K2, R)) break;
        K_ = k;
        N_ = 2 * k * G_;
        if (N_ <= best_N) continue;
        if (!alloc_group()) { free_group(); break; }

        trials[k] += 1.0;
        int ok = sa_run(60000, 8000, limit, c0);
        if (ok) {
            wins[k] += 1.0;
            fails = 0;
            save_best();
        } else {
            fails++;
            if (best_N == 0 && fails > 30) {
                goal = goal * 9 / 10;
                if (goal < 2L * d_) goal = 2L * d_;
                fails = 0;
            }
        }
        free_group();
    }

    if (best_N == 0) { printf("0 0\n"); return 0; }
    int half = best_N / 2;
    printf("%d %d\n", best_N, half * best_d);
    for (int u = 0; u < half; u++)
        for (int l = 0; l < best_d; l++)
            printf("%d %d\n", u, best_nbr[(size_t)l * best_N + u]);
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
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact optimum (calibration case)
    if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except ValueError:
            pass

    # Main phase: C search over bi-Cayley lifts with many groups.
    hint = max(2 * d, min(50000, lib.moore_bound(d, D) // 4))
    budget = 0.8 * time_limit if time_limit >= 15 else 0.5 * time_limit
    budget -= time.monotonic() - t0
    if budget >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", hint],
                            timeout=budget + 6.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
