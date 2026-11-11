"""Bi-Cayley lift search with an identity-source BFS cost.

Idea (new in this version): a voltage lift over a semidirect product G = Z_m x| Z_k2
with k base vertices per side is G-symmetric. Left multiplication by any group
element is an automorphism of the lift, and it acts regularly on each block. So
the lift has diameter <= D iff every one of the 2k identity vertices reaches the
whole graph within D steps. The C engine therefore runs only 2k BFS per move,
instead of one bitset expansion from all N vertices. It anneals random layer
permutations and voltages, and it samples new groups and base sizes whenever a
target order is reached. Each success raises the target order.
"""
import time

import lib


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

#define MAXD 16
#define MAXK 6
#define ITERS 30000

static int d_, D_;
static int K, G, M, K2, NV;
static long long powr[64];
static int sig[MAXD][MAXK], volt[MAXD][MAXK], vinv[MAXD][MAXK];
static int *nbr, *queue_, *stamp_, *dist_;
static int curstamp = 0;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;
static long long PEN = 40;

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static long long powmod_(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Element x = a*K2 + b of Z_M x| Z_K2, with (a,b)*(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long aa = (a + powr[b] * c) % M;
    int bb = (b + e) % K2;
    return (int)aa * K2 + bb;
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long long aa = (-(powr[nb] * a)) % M;
    if (aa < 0) aa += M;
    return (int)aa * K2 + nb;
}

/* Choose a random group Z_m x| Z_k2 of order at least target. */
static int setup_group(int target) {
    static const int opts[] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 16, 18, 20, 24};
    for (int tries = 0; tries < 200; tries++) {
        int k2 = opts[rint_(17)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = 1;
        if (k2 > 1) {
            r = -1;
            for (int t = 0; t < 300; t++) {
                int c = (m > 2) ? 2 + rint_(m - 2) : 1;
                if (gcd_(c, m) == 1 && powmod_(c, k2, m) == 1 % m) { r = c; break; }
            }
            if (r < 0) continue;
        }
        K2 = k2; M = m; G = m * k2;
        powr[0] = 1 % m;
        for (int b = 1; b < k2; b++) powr[b] = powr[b - 1] * r % m;
        return 1;
    }
    return 0;
}

/* Recompute the neighbour entries of layer l for all vertices. */
static void rebuild_layer(int l) {
    for (int i = 0; i < K; i++) {
        int j = sig[l][i], s = volt[l][i], si = vinv[l][i];
        for (int g = 0; g < G; g++) {
            int A = i * G + g;
            int B = (K + j) * G + g;
            nbr[(size_t)A * d_ + l] = (K + j) * G + gmul(g, s);
            nbr[(size_t)B * d_ + l] = i * G + gmul(g, si);
        }
    }
}

/* Multi-edges appear when two layers share both target block and voltage at one A block. */
static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = l + 1; l2 < d_; l2++)
                if (sig[l][i] == sig[l2][i] && volt[l][i] == volt[l2][i]) c++;
    return c;
}

/* Unreached (source, target) pairs over the 2K identity sources. */
static long long cost_fn(void) {
    long long unr = 0;
    for (int b = 0; b < 2 * K; b++) {
        int src = b * G;
        curstamp++;
        int head = 0, tail = 0;
        queue_[tail++] = src;
        stamp_[src] = curstamp;
        dist_[src] = 0;
        while (head < tail) {
            int v = queue_[head++];
            if (dist_[v] >= D_) continue;
            const int *nv = nbr + (size_t)v * d_;
            for (int l = 0; l < d_; l++) {
                int u = nv[l];
                if (stamp_[u] != curstamp) {
                    stamp_[u] = curstamp;
                    dist_[u] = dist_[v] + 1;
                    queue_[tail++] = u;
                }
            }
        }
        unr += NV - tail;
    }
    return unr;
}

static long long full_cost(void) {
    return cost_fn() + PEN * (long long)dupcount();
}

static int anneal(long long iters, double T0, double T1, clock_t c0, double limit) {
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K; i++) sig[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = sig[l][i]; sig[l][i] = sig[l][j]; sig[l][j] = t;
        }
        for (int i = 0; i < K; i++) {
            volt[l][i] = rint_(G);
            vinv[l][i] = ginv(volt[l][i]);
        }
        rebuild_layer(l);
    }
    long long cost = full_cost();
    for (long long t = 0; t < iters && cost > 0; t++) {
        if ((t & 63) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= limit) return 0;
        }
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        int l = rint_(d_);
        if (rint_(10) < 6) {
            int i = rint_(K);
            int old = volt[l][i], nw = rint_(G);
            if (nw == old) continue;
            volt[l][i] = nw; vinv[l][i] = ginv(nw);
            rebuild_layer(l);
            long long c2 = full_cost();
            long long dl = c2 - cost;
            if (dl <= 0 || rdbl() < exp(-(double)dl / T)) {
                cost = c2;
            } else {
                volt[l][i] = old; vinv[l][i] = ginv(old);
                rebuild_layer(l);
            }
        } else {
            if (K < 2) continue;
            int i1 = rint_(K), i2 = rint_(K - 1);
            if (i2 >= i1) i2++;
            int t1 = sig[l][i1]; sig[l][i1] = sig[l][i2]; sig[l][i2] = t1;
            rebuild_layer(l);
            long long c2 = full_cost();
            long long dl = c2 - cost;
            if (dl <= 0 || rdbl() < exp(-(double)dl / T)) {
                cost = c2;
            } else {
                t1 = sig[l][i1]; sig[l][i1] = sig[l][i2]; sig[l][i2] = t1;
                rebuild_layer(l);
            }
        }
    }
    return cost == 0;
}

static void save_best(void) {
    int cap = K * G * d_;
    int *ne = malloc(sizeof(int) * 2 * (size_t)cap);
    if (!ne) return;
    int m = 0;
    for (int v = 0; v < K * G; v++)
        for (int l = 0; l < d_; l++) {
            ne[2 * m] = v;
            ne[2 * m + 1] = nbr[(size_t)v * d_ + l];
            m++;
        }
    free(best_e);
    best_e = ne;
    best_m = m;
    best_n = NV;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    int base_n = argc > 5 ? atoi(argv[5]) : 0;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    (void)n0; (void)m0;

    if (d_ < 2 || d_ > MAXD || D_ < 1) {
        printf("0 0\n");
        return 0;
    }

    best_n = base_n;
    best_m = 0;
    best_e = NULL;
    clock_t c0 = clock();
    static const int Kopts[] = {1, 2, 2, 3, 3, 3, 4, 4, 5, 6};

    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;

        int Kc = Kopts[rint_(10)];
        if (Kc > MAXK) Kc = MAXK;
        long long want = (long long)best_n + 2 + rint_(best_n / 8 + 4);
        int Gt = (int)((want + 2 * Kc - 1) / (2 * Kc));
        if (Gt < 2) Gt = 2;
        if (!setup_group(Gt)) continue;

        K = Kc;
        NV = 2 * K * G;
        if (NV <= best_n) continue;
        if (NV > 400000) continue;

        nbr = malloc(sizeof(int) * (size_t)NV * d_);
        queue_ = malloc(sizeof(int) * (size_t)NV);
        stamp_ = calloc((size_t)NV, sizeof(int));
        dist_ = malloc(sizeof(int) * (size_t)NV);
        if (!nbr || !queue_ || !stamp_ || !dist_) {
            free(nbr); free(queue_); free(stamp_); free(dist_);
            break;
        }

        int ok = anneal(ITERS, 8.0, 0.2, c0, limit);
        if (ok) save_best();

        free(nbr); free(queue_); free(stamp_); free(dist_);
        nbr = NULL; queue_ = NULL; stamp_ = NULL; dist_ = NULL;
    }

    if (best_e == NULL || best_n == 0 || best_m == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++)
        printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
    free(best_e);
    return 0;
}
"""


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

    # Exact construction for D = 3 with d - 1 a prime power (calibration case).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Bi-Cayley lift search in C. Keep a margin for compilation and output.
    margin = max(4.0, 0.1 * time_limit)
    budget = time_limit - (time.monotonic() - t0) - margin
    if budget >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best[0]],
                            timeout=budget + 6.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
