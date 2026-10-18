import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lift annealer over semidirect products Z_m x| Z_k2.
#
# A candidate is a lift with k base vertices per side and d layers. Layer l
# joins A_i to B_{P[l][i]} through voltage S[l][i]: A_i x ~ B_{P[l][i]} (x*s).
# Each P[l] is a permutation, so the lift is d-regular and bipartite. The group
# acts regularly on every fibre, so the diameter check needs only one BFS per
# base vertex (2k sources). Cost = unreached (source, vertex) pairs plus a
# penalty for duplicate darts. Zero cost means a valid graph of order 2kG.
# Each attempt picks a fresh group and k, aiming just above the best order so far.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXV 60000
#define MAXDEG 16
#define MAXK 6
#define MAXG 1500

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, G_, m_, k2_;
static int N_ = 0, bestN = 0, bestM = 0;
static int powr[MAXG + 1];
static int *MT;
static int IV[MAXG + 1];
static int P[MAXDEG][MAXK], S[MAXDEG][MAXK], Si[MAXDEG][MAXK];
static int *nbr, *stampArr, *queueArr, *bestU, *bestV;
static int stamp_ = 0;
static double tlimit;
static clock_t c0;

static double elapsed(void) { return (double)(clock() - c0) / CLOCKS_PER_SEC; }

static long long pmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m; if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

/* (a,b)*(c,e) = (a + r^b c, b + e) with element index a*k2 + b. */
static int gmul(int x, int y) {
    int a = x / k2_, b = x - a * k2_;
    int c = y / k2_, e = y - c * k2_;
    long long ra = ((long long)a + (long long)powr[b] * c) % m_;
    int rb = b + e;
    if (rb >= k2_) rb -= k2_;
    return (int)ra * k2_ + rb;
}

/* Inverse of (a,b) is (-r^{-b} a, -b). */
static int ginv(int x) {
    int a = x / k2_, b = x - a * k2_;
    int nb = (k2_ - b) % k2_;
    long long t = ((long long)powr[nb] * a) % m_;
    long long c = ((long long)m_ - t) % m_;
    return (int)c * k2_ + nb;
}

static void set_group(int G, int k2, int r) {
    G_ = G; k2_ = k2; m_ = G / k2;
    powr[0] = 1 % m_;
    for (int b = 1; b < k2_; b++) powr[b] = (int)((long long)powr[b - 1] * r % m_);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            MT[x * G + y] = gmul(x, y);
    for (int x = 0; x < G; x++) IV[x] = ginv(x);
}

static void build_nbr(void) {
    int k = k_, d = d_, G = G_;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) {
            int p = P[l][i], s = S[l][i], si = Si[l][i];
            for (int x = 0; x < G; x++) {
                int y = MT[x * G + s];
                nbr[(size_t)(i * G + x) * d + l] = (k + p) * G + y;
                nbr[(size_t)((k + p) * G + y) * d + l] = i * G + MT[y * G + si];
            }
        }
}

static int dupcount(void) {
    int c = 0;
    for (int l = 1; l < d_; l++)
        for (int i = 0; i < k_; i++)
            for (int l2 = 0; l2 < l; l2++)
                if (P[l2][i] == P[l][i] && S[l2][i] == S[l][i]) c++;
    return c;
}

/* Sum over the 2k base sources of vertices not reached within D_ steps. */
static long long eval_cost(void) {
    int N = N_, d = d_;
    long long cost = 0;
    for (int t = 0; t < 2 * k_; t++) {
        int src = t * G_;
        stamp_++;
        if (stamp_ == 0x7ffffff0) {
            memset(stampArr, 0, sizeof(int) * MAXV);
            stamp_ = 1;
        }
        int head = 0, tail = 0;
        queueArr[tail++] = src;
        stampArr[src] = stamp_;
        for (int lev = 0; lev < D_ && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                const int *nb = nbr + (size_t)queueArr[head++] * d;
                for (int j = 0; j < d; j++) {
                    int u = nb[j];
                    if (stampArr[u] != stamp_) {
                        stampArr[u] = stamp_;
                        queueArr[tail++] = u;
                    }
                }
            }
        }
        cost += N - tail;
    }
    return cost;
}

static long long full_cost(void) {
    build_nbr();
    long long pen = (long long)dupcount() * (long long)(2 * N_);
    return eval_cost() + pen;
}

static void save_best(void) {
    int d = d_, m = 0;
    int A = k_ * G_;
    for (int v = 0; v < A; v++)
        for (int l = 0; l < d; l++) {
            bestU[m] = v;
            bestV[m] = nbr[(size_t)v * d + l];
            m++;
        }
    bestN = N_;
    bestM = m;
}

static int run_attempt(int iters, double T0, double T1) {
    int k = k_, d = d_, G = G_;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) P[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rint_(i + 1), t = P[l][i];
            P[l][i] = P[l][j];
            P[l][j] = t;
        }
        for (int i = 0; i < k; i++) {
            S[l][i] = rint_(G);
            Si[l][i] = IV[S[l][i]];
        }
    }
    long long cost = full_cost();
    if (cost == 0) { save_best(); return 1; }
    for (int it = 0; it < iters; it++) {
        if ((it & 63) == 0 && elapsed() > tlimit) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int l = rint_(d);
        if (rint_(3) < 2) {
            int i = rint_(k);
            int nw = rint_(G);
            if (nw == S[l][i]) continue;
            int old = S[l][i], oldi = Si[l][i];
            S[l][i] = nw;
            Si[l][i] = IV[nw];
            long long nc = full_cost();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                S[l][i] = old;
                Si[l][i] = oldi;
            }
        } else {
            if (k < 2) continue;
            int i1 = rint_(k), i2 = rint_(k);
            if (i1 == i2) continue;
            int t = P[l][i1];
            P[l][i1] = P[l][i2];
            P[l][i2] = t;
            long long nc = full_cost();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                t = P[l][i1];
                P[l][i1] = P[l][i2];
                P[l][i2] = t;
            }
        }
        if (cost == 0) { save_best(); return 1; }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    tlimit = atof(argv[4]);
    bestN = argc > 5 ? atoi(argv[5]) : 0;
    if (d_ < 3 || d_ > MAXDEG || D_ < 3) { printf("0 0\n"); return 0; }

    nbr = malloc(sizeof(int) * (size_t)MAXV * MAXDEG);
    stampArr = calloc(MAXV, sizeof(int));
    queueArr = malloc(sizeof(int) * MAXV);
    bestU = malloc(sizeof(int) * (size_t)MAXV * MAXDEG);
    bestV = malloc(sizeof(int) * (size_t)MAXV * MAXDEG);
    MT = malloc(sizeof(int) * (size_t)MAXG * MAXG);
    if (!nbr || !stampArr || !queueArr || !bestU || !bestV || !MT) {
        printf("0 0\n");
        return 0;
    }

    c0 = clock();
    int divs[256];
    while (elapsed() < tlimit) {
        int k = 1 + rint_(MAXK);
        int nLow = bestN / (2 * k) + 1;
        if (2 * k * nLow > MAXV) break;
        int spread = 1 + nLow / 40;
        int G = nLow + rint_(spread);
        if (G < 2) G = 2;
        if (G > MAXG) continue;

        int nd = 0;
        for (int q = 1; q <= G && nd < 256; q++)
            if (G % q == 0) divs[nd++] = q;
        int k2 = (rint_(3) == 0) ? 1 : divs[rint_(nd)];
        int m = G / k2;
        int r = 1;
        if (k2 > 1 && m > 2) {
            for (int tr = 0; tr < 200; tr++) {
                int c = 2 + rint_(m - 2);
                if (gcd_(c, m) == 1 && pmod(c, k2, m) == 1 % m) { r = c; break; }
            }
        }
        set_group(G, k2, r);
        k_ = k;
        N_ = 2 * k * G;
        run_attempt(30000, 4.0, 0.2);
    }

    if (bestM == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestU[i], bestV[i]);
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
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle C_{2D}: bipartite, diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2, always valid here
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        try:
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    pg = _best_pg(d)
    if pg is not None:
        consider(*pg)
    if D == 3:
        if pg is not None and lib.is_prime_power(d - 1):
            return best  # exact Moore-bound graph; calibration case returns at once
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    # Main search: bi-Cayley lifts over semidirect products, run in C.
    left = time_limit - (time.monotonic() - t0)
    budget = min(0.8 * time_limit, left - 6.0)
    if d <= 16 and budget >= 2.0:
        try:
            out = lib.run_c(C_SOURCE,
                            [d, D, int(seed) % (1 << 40) + 1, f"{budget:.2f}", best[0]],
                            stdin_graph=None, timeout=budget + 8.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass  # keep the valid fallback

    return best
