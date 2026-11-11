import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts.
#
# A candidate graph is a lift of a base with K blocks on each side over a
# group G = Z_m x| Z_k2 (element (a,b) coded as a*k2+b, product
# (a,b)(c,e) = (a + r^b c, b+e)). Dart (l, i) sends left block i to right
# block lay[l][i] via x -> x*s[l][i]. Each layer l is a permutation of the
# blocks, so every vertex gets exactly one edge per layer.
#
# Left multiplication by G is an automorphism, so it is enough to run BFS
# from one identity vertex per block. Validity means every block's identity
# reaches all NV vertices within D steps. Cost = total unreached count over
# those 2K BFS runs, plus a penalty per duplicate dart.
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
#define GMAX 2000
#define NVMAX (2 * KMAX * GMAX)

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int d_, D_, K_, G_, NV_, pen_;
static int *mt, *lay, *sh, *nbr, *stamp, *queue, *bestU, *bestV;
static int curstamp = 0, best_n = 0, best_m = 0;

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int powmod_(long long b, int e, int m) {
    long long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return (int)r;
}

static void make_group(int m, int k2, int r) {
    int powr[64];
    G_ = m * k2;
    powr[0] = 1 % m;
    for (int b = 1; b < k2; b++) powr[b] = (int)((long long)powr[b - 1] * r % m);
    for (int x = 0; x < G_; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G_; y++) {
            int c = y / k2, e = y % k2;
            int first = (int)((a + (long long)powr[b] * c) % m);
            int second = (b + e) % k2;
            mt[x * G_ + y] = first * k2 + second;
        }
    }
}

/* Write both endpoints of every edge of dart (l, i). */
static void set_dart(int l, int i) {
    int j = lay[l * K_ + i], s = sh[l * K_ + i];
    for (int x = 0; x < G_; x++) {
        int y = mt[x * G_ + s];
        int lv = i * G_ + x, rv = (K_ + j) * G_ + y;
        nbr[(size_t)lv * d_ + l] = rv;
        nbr[(size_t)rv * d_ + l] = lv;
    }
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K_; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (lay[l * K_ + i] == lay[l2 * K_ + i] && sh[l * K_ + i] == sh[l2 * K_ + i]) c++;
    return c;
}

/* Number of vertices at distance > D_ from src. */
static int bfs_unreached(int src) {
    curstamp++;
    int h = 0, t = 0;
    queue[t++] = src;
    stamp[src] = curstamp;
    int lev = 0;
    while (h < t && lev < D_) {
        int end = t;
        while (h < end) {
            int v = queue[h++];
            const int *nb = nbr + (size_t)v * d_;
            for (int l = 0; l < d_; l++) {
                int u = nb[l];
                if (stamp[u] != curstamp) {
                    stamp[u] = curstamp;
                    queue[t++] = u;
                }
            }
        }
        lev++;
    }
    return NV_ - t;
}

static long long eval_cost(void) {
    long long c = 0;
    for (int b = 0; b < 2 * K_; b++) c += bfs_unreached(b * G_);
    return c + (long long)pen_ * dupcount();
}

static int anneal(long long maxit, double tslice) {
    for (int l = 0; l < d_; l++) {
        int *p = lay + l * K_;
        for (int i = 0; i < K_; i++) p[i] = i;
        for (int i = K_ - 1; i > 0; i--) {
            int j = rint_(i + 1), t = p[i];
            p[i] = p[j];
            p[j] = t;
        }
        for (int i = 0; i < K_; i++) sh[l * K_ + i] = rint_(G_);
    }
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < K_; i++) set_dart(l, i);

    long long cost = eval_cost();
    if (cost == 0) return 1;
    double T0 = 0.05 * (double)cost;
    if (T0 < 10.0) T0 = 10.0;
    const double T1 = 0.5;
    double ts = now();

    for (long long it = 0; it < maxit && cost != 0; it++) {
        if ((it & 255) == 0 && now() - ts > tslice) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)maxit);
        if (K_ >= 2 && rdbl() < 0.3) {
            int l = rint_(d_), i1 = rint_(K_), i2 = rint_(K_ - 1);
            if (i2 >= i1) i2++;
            int *p = lay + l * K_;
            int t = p[i1];
            p[i1] = p[i2];
            p[i2] = t;
            set_dart(l, i1);
            set_dart(l, i2);
            long long c2 = eval_cost();
            if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                t = p[i1];
                p[i1] = p[i2];
                p[i2] = t;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            int l = rint_(d_), i = rint_(K_), idx = l * K_ + i;
            int old = sh[idx], nw = rint_(G_);
            if (nw == old) continue;
            sh[idx] = nw;
            set_dart(l, i);
            long long c2 = eval_cost();
            if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                sh[idx] = old;
                set_dart(l, i);
            }
        }
    }
    return cost == 0;
}

static void emit_best(void) {
    int m = 0, left = K_ * G_;
    for (int v = 0; v < left; v++)
        for (int l = 0; l < d_; l++) {
            bestU[m] = v;
            bestV[m] = nbr[(size_t)v * d_ + l];
            m++;
        }
    best_n = NV_;
    best_m = m;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    if (d_ < 1 || D_ < 1) { printf("0 0\n"); return 0; }

    mt = malloc(sizeof(int) * (size_t)GMAX * GMAX);
    lay = malloc(sizeof(int) * (size_t)d_ * KMAX);
    sh = malloc(sizeof(int) * (size_t)d_ * KMAX);
    nbr = malloc(sizeof(int) * (size_t)NVMAX * d_);
    stamp = calloc(NVMAX, sizeof(int));
    queue = malloc(sizeof(int) * NVMAX);
    bestU = malloc(sizeof(int) * (size_t)NVMAX * d_);
    bestV = malloc(sizeof(int) * (size_t)NVMAX * d_);
    if (!mt || !lay || !sh || !nbr || !stamp || !queue || !bestU || !bestV) {
        printf("0 0\n");
        return 0;
    }

    static const int KS[] = {1, 2, 3, 4, 6};
    static const int KS2[] = {1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 28, 30, 36};
    int lo[KMAX + 1];
    double step[KMAX + 1];
    for (int k = 0; k <= KMAX; k++) { lo[k] = 0; step[k] = 8.0; }

    while (1) {
        double rem = limit - now();
        if (rem < 0.5) break;

        int K = KS[rint_(5)];
        int GCAP = GMAX;
        if (NVMAX / (2 * K) < GCAP) GCAP = NVMAX / (2 * K);
        double tg = lo[K] + step[K] * (0.5 + rdbl());
        int Gt = (int)tg;
        if (Gt < 2) Gt = 2;
        if (Gt > GCAP) Gt = GCAP;

        int k2 = KS2[rint_(20)];
        if (k2 > Gt) k2 = 1;
        int m = (Gt + k2 - 1) / k2;
        if (m < 2 || m * k2 > GCAP) { k2 = 1; m = Gt; }

        int r = 1;
        if (k2 > 1 && m >= 3 && rdbl() < 0.6) {
            int found = 0;
            for (int t = 0; t < 200 && !found; t++) {
                int c = 2 + rint_(m - 2);
                if (gcd_(c, m) == 1 && powmod_(c, k2, m) == 1 % m) { r = c; found = 1; }
            }
        }

        make_group(m, k2, r);
        int G = G_;
        K_ = K;
        NV_ = 2 * K * G;
        pen_ = G / 4 + 4;

        double slice = rem - 0.3;
        if (slice > 3.0) slice = 3.0;
        int ok = anneal(150000, slice);

        if (ok) {
            if (G > lo[K]) lo[K] = G;
            step[K] *= 1.5;
            double cap = lo[K] / 20.0;
            if (step[K] > cap) step[K] = cap;
            if (step[K] < 1.0) step[K] = 1.0;
            if (NV_ > best_n) emit_best();
        } else {
            step[K] *= 0.5;
            if (step[K] < 1.0) step[K] = 1.0;
        }
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue and exact constructions.
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
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: diameter 2, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d == 2:
        n = 2 * D  # even cycle C_{2D}: bipartite, degree 2, diameter D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best

    if D == 2:
        return best  # K_{d,d} meets the Moore bound 2d for D = 2

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best  # exact Moore-bound graph

    budget = time_limit - (time.monotonic() - t0) - 6.0
    if budget >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, int(seed), f"{budget:.2f}"],
                            timeout=budget + 20.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
