"""Bi-Cayley lift annealer in C over semidirect groups Z_m x| Z_k2 with k base blocks per side.

New idea: left multiplication by a group element is an automorphism of every lift, so the
ball around any vertex is a translate of the ball around its block representative. A vertex
pair is within distance D iff each representative reaches every vertex within D. The cost
is therefore evaluated with one 2k-bit mask per vertex (cheap), while every accepted graph
is re-checked with a full bitset diameter test. Targets ratchet above the best order found.
"""
import time

import lib


LIFT_C = r'''
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXK 4
#define MAXN 12288
#define PEN 1000

static int d, D;
static double t_end;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndf(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

/* Group Z_M x| Z_K2, element (a,b) coded as a*K2+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int M, K2, pw[64];
static int KB, G, NN;           /* KB base blocks per side, G group order, NN = 2*KB*G */
static int perm[MAXD][MAXK];    /* layer l: A block i joins B block perm[l][i] */
static int S[MAXD][MAXK];       /* voltage of dart (l, i) */
static int nbr[MAXD][MAXN];
static uint8_t reachA[MAXN], reachB[MAXN];
static uint8_t *RC = reachA;
static int bestNbr[MAXD][MAXN];
static int bestN = 0;

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    int aa = (int)(((long)a + (long)pw[b] * c) % M);
    int ee = b + e;
    if (ee >= K2) ee -= K2;
    return aa * K2 + ee;
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long t = (-((long)pw[nb] * a)) % M;
    if (t < 0) t += M;
    return (int)t * K2 + nb;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int setup_group(int target, int kb) {
    static const int K2S[] = {1, 2, 2, 3, 4, 4, 5, 6, 6, 8, 9, 10, 12};
    K2 = K2S[rndi(13)];
    long per = 2L * kb * K2;
    long m = (target + per - 1) / per + rndi(3);
    if (m < 2) m = 2;
    if (m > MAXN) return 0;
    M = (int)m;
    int r = -1;
    if (K2 == 1) {
        r = 1;
    } else {
        for (int tries = 0; tries < 200 && r < 0; tries++) {
            int c;
            if (tries == 0) c = M - 1;
            else if (tries == 1) c = 1;
            else c = 2 + rndi(M > 2 ? M - 2 : 1);
            if (c < 1 || c >= M) continue;
            if (gcd_i(c, M) != 1) continue;
            if (powmod(c, K2, M) != 1 % M) continue;
            r = c;
        }
    }
    if (r < 0) return 0;
    pw[0] = 1 % M;
    for (int t = 1; t < K2; t++) pw[t] = (int)((long)pw[t - 1] * r % M);
    KB = kb;
    G = M * K2;
    NN = 2 * KB * G;
    if (NN > MAXN) return 0;
    return 1;
}

/* Rewrite both halves of dart (l, i): A rows of block i and the B rows of its partner block. */
static void set_row(int l, int i) {
    int j = perm[l][i], s = S[l][i], si = ginv(s);
    int Ai = i * G, Bj = (KB + j) * G;
    for (int g = 0; g < G; g++) {
        nbr[l][Ai + g] = Bj + gmul(g, s);
        nbr[l][Bj + g] = Ai + gmul(g, si);
    }
}

static void random_init(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < KB; i++) perm[l][i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = t;
        }
        for (int i = 0; i < KB; i++) S[l][i] = rndi(G);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < KB; i++) set_row(l, i);
}

/* Number of duplicated darts: same (i, j, s) used in two layers gives a double edge. */
static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < KB; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1][i] == perm[l2][i] && S[l1][i] == S[l2][i]) c++;
    return c;
}

/* Sum over vertices of unreached block representatives (uses left-invariance). */
static long evalcost(void) {
    int bits = 2 * KB;
    for (int v = 0; v < NN; v++) reachA[v] = 0;
    for (int b = 0; b < bits; b++) reachA[b * G] |= (uint8_t)(1u << b);
    uint8_t *cur = reachA, *nx = reachB;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < NN; v++) {
            uint8_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nx[v] = x;
            changed |= (x != cur[v]);
        }
        uint8_t *t = cur;
        cur = nx;
        nx = t;
        if (!changed) break;
    }
    RC = cur;
    long un = 0;
    for (int v = 0; v < NN; v++) un += bits - __builtin_popcount(cur[v]);
    return un;
}

static long total_cost(void) {
    long u = evalcost();
    return u + (long)PEN * dupcount();
}

/* Exact check of the whole lift with bitsets: bipartite, simple, degree d, diameter <= D. */
static int full_check(void) {
    int N = NN, W = (N + 63) / 64;
    int half = KB * G;
    if (dupcount() != 0) return 0;
    for (int v = 0; v < N; v++)
        for (int l = 0; l < d; l++) {
            int u = nbr[l][v];
            if (u < 0 || u >= N || u == v) return 0;
            if ((v < half) == (u < half)) return 0;
        }
    uint64_t *A = malloc(sizeof(uint64_t) * (size_t)N * W);
    uint64_t *B = malloc(sizeof(uint64_t) * (size_t)N * W);
    if (!A || !B) {
        free(A);
        free(B);
        return 0;
    }
    memset(A, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) A[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = B + (size_t)v * W;
            memcpy(dst, A + (size_t)v * W, sizeof(uint64_t) * W);
            for (int l = 0; l < d; l++) {
                const uint64_t *src = A + (size_t)nbr[l][v] * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t *t = A;
        A = B;
        B = t;
    }
    int ok = 1;
    for (int v = 0; v < N && ok; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(A[(size_t)v * W + w]);
        if (c != N) ok = 0;
    }
    free(A);
    free(B);
    return ok;
}

/* Choose a dart near an unreached pair, if one can be found quickly. */
static void pick_dart(int *lout, int *iout) {
    int full = (1 << (2 * KB)) - 1;
    int l = rndi(d), i = rndi(KB);
    for (int tr = 0; tr < 64; tr++) {
        int v = rndi(NN);
        if (RC[v] == full) continue;
        int block = v / G;
        if (block < KB) {
            i = block;
            l = rndi(d);
        } else {
            int j = block - KB;
            l = rndi(d);
            for (int q = 0; q < KB; q++)
                if (perm[l][q] == j) {
                    i = q;
                    break;
                }
        }
        break;
    }
    *lout = l;
    *iout = i;
}

/* Simulated annealing over voltages and layer permutations. Returns 1 if cost reaches 0. */
static int anneal(long iters, long patience) {
    long cost = total_cost();
    long c0 = cost > 1 ? cost : 1;
    long bestc = cost, last = 0;
    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 31) == 0 && now_s() > t_end) break;
        if (t - last > patience) break;
        double T = 0.05 * (double)c0 * (1.0 - (double)t / (double)iters) + 0.3;
        long nc;
        if (KB >= 2 && rndf() < 0.2) {
            int l = rndi(d), i1 = rndi(KB), i2 = rndi(KB - 1);
            if (i2 >= i1) i2++;
            int tmp = perm[l][i1];
            perm[l][i1] = perm[l][i2];
            perm[l][i2] = tmp;
            set_row(l, i1);
            set_row(l, i2);
            nc = total_cost();
            if (nc <= cost || rndf() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                tmp = perm[l][i1];
                perm[l][i1] = perm[l][i2];
                perm[l][i2] = tmp;
                set_row(l, i1);
                set_row(l, i2);
            }
        } else {
            int l, i;
            if (rndf() < 0.5) pick_dart(&l, &i);
            else {
                l = rndi(d);
                i = rndi(KB);
            }
            int old = S[l][i];
            int nw = rndi(G);
            if (nw == old) continue;
            S[l][i] = nw;
            set_row(l, i);
            nc = total_cost();
            if (nc <= cost || rndf() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                S[l][i] = old;
                set_row(l, i);
            }
        }
        if (cost < bestc) {
            bestc = cost;
            last = t;
        }
    }
    return cost == 0;
}

static long moore_bound(void) {
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000L) break;
    }
    return 2 * s;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit\n");
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now_s();
    t_end = t0 + limit * 0.97 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    long moore = moore_bound();
    while (now_s() < t_end && bestN < moore) {
        int target;
        double u = rndf();
        if (bestN == 0) target = 4 * d;
        else if (u < 0.2) target = (int)(bestN * 1.05) + 1;
        else target = (int)(bestN * (1.0 + 0.005 + 0.02 * rndf())) + 2;
        if (target > MAXN - 2) target = MAXN - 2;
        if (target > moore) target = (int)moore;
        int kb = 1 + rndi(MAXK);
        if (!setup_group(target, kb)) continue;
        random_init();
        int ok = anneal(4000, 900);
        if (ok && NN > bestN && full_check()) {
            memcpy(bestNbr, nbr, sizeof(nbr));
            bestN = NN;
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    long m = 0;
    for (int v = 0; v < bestN; v++)
        for (int l = 0; l < d; l++)
            if (v < bestNbr[l][v]) m++;
    printf("%d %ld\n", bestN, m);
    for (int v = 0; v < bestN; v++)
        for (int l = 0; l < d; l++)
            if (v < bestNbr[l][v]) printf("%d %d\n", v, bestNbr[l][v]);
    return 0;
}
'''


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

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # d = 2: the even cycle C_{2D} meets the Moore bound.
    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best

    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Bi-Cayley lift annealing in C, using the remaining time (leave room for Python validation).
    total = max(0.0, 0.85 * time_limit - 1.5)
    budget = total - 2.5
    if budget > 2.0:
        try:
            text = lib.run_c(LIFT_C, [d, D, seed, round(budget, 2)], timeout=budget + 15)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
