import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over Z_m x| Z_K lifts of small bipartite base
# graphs. A base has kb blocks per side and d layers. Each layer is a
# permutation P_l from A-blocks to B-blocks with a voltage S_l(i) in the group.
# The lift has 2*kb*G vertices and is d-regular. Left multiplication is an
# automorphism, so the diameter test only needs BFS from the 2*kb block
# representatives (b, identity). Cost = unreached ordered pairs + penalty per
# duplicate dart. Acceptance uses an early-abort threshold.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#include <limits.h>

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

#define KMAX 6
#define PEN 30LL

static int d_, D_;
static int kb, G, gm, gK, NV;
static int *pw, *P, *S, *Ainv, *sinv, *nbr, *vis, *que;
static int stamp = 0;

static int best_n = 0, best_m = 0;
static int *best_e = NULL;

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

/* Semidirect product Z_gm x| Z_gK, element a*gK+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int gmul(int x, int y) {
    int a = x / gK, b = x % gK, c = y / gK, e = y % gK;
    long long t = (long long)a + (long long)pw[b] * c;
    return (int)(t % gm) * gK + (b + e) % gK;
}
static int ginv(int x) {
    int a = x / gK, b = x % gK;
    int nb = (gK - b) % gK;
    long long t = (long long)pw[nb] * a % gm;
    return (int)((gm - t) % gm) * gK + nb;
}

static void refreshA(int i, int l) {
    int idx = l * kb + i;
    int j = P[idx], s = S[idx];
    int base = (kb + j) * G;
    for (int g = 0; g < G; g++)
        nbr[(i * G + g) * d_ + l] = base + gmul(g, s);
}

static void refreshB(int j, int l) {
    int i = Ainv[l * kb + j];
    int s = sinv[l * kb + i];
    int base = i * G;
    for (int h = 0; h < G; h++)
        nbr[((kb + j) * G + h) * d_ + l] = base + gmul(h, s);
}

static void build_all(void) {
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < kb; i++) {
            Ainv[l * kb + P[l * kb + i]] = i;
            sinv[l * kb + i] = ginv(S[l * kb + i]);
        }
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < kb; i++) refreshA(i, l);
        for (int j = 0; j < kb; j++) refreshB(j, l);
    }
}

static long long count_dups(void) {
    long long c = 0;
    for (int i = 0; i < kb; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++)
                if (P[l1 * kb + i] == P[l2 * kb + i] && S[l1 * kb + i] == S[l2 * kb + i]) c++;
    return c;
}

/* Vertices not within distance D_ of src. */
static int unreached(int src) {
    stamp++;
    if (stamp == INT_MAX) {
        memset(vis, 0, sizeof(int) * (size_t)NV);
        stamp = 1;
    }
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp;
    for (int lev = 0; lev < D_; lev++) {
        int end = tail;
        if (head == end) break;
        while (head < end) {
            int v = que[head++];
            const int *nb = nbr + (size_t)v * d_;
            for (int l = 0; l < d_; l++) {
                int u = nb[l];
                if (vis[u] != stamp) {
                    vis[u] = stamp;
                    que[tail++] = u;
                }
            }
        }
    }
    return NV - tail;
}

/* Cost with early abort once it exceeds limit. */
static long long evalcost_lim(long long limit, int *aborted) {
    long long c = PEN * count_dups();
    *aborted = 0;
    if (c > limit) { *aborted = 1; return c; }
    for (int b = 0; b < 2 * kb; b++) {
        c += unreached(b * G);
        if (c > limit) { *aborted = 1; return c; }
    }
    return c;
}

static void random_init(void) {
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < kb; i++) P[l * kb + i] = i;
        for (int i = kb - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = P[l * kb + i];
            P[l * kb + i] = P[l * kb + j];
            P[l * kb + j] = t;
        }
        for (int i = 0; i < kb; i++) S[l * kb + i] = rint_(G);
    }
}

static int anneal(long long iters, clock_t t_end) {
    random_init();
    build_all();
    int ab;
    long long cost = evalcost_lim(1LL << 60, &ab);
    if (cost == 0) return 1;
    const double T0 = 30.0, T1 = 0.3;
    for (long long t = 0; t < iters; t++) {
        if ((t & 127) == 0 && clock() >= t_end) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        double u = rdbl();
        long long lim = cost + (long long)(-T * log(u + 1e-300));
        int l = rint_(d_);
        if (kb > 1 && (rnd() & 1)) {
            int i1 = rint_(kb), i2 = rint_(kb - 1);
            if (i2 >= i1) i2++;
            int a = l * kb + i1, b = l * kb + i2;
            int j1 = P[a], j2 = P[b];
            P[a] = j2; P[b] = j1;
            Ainv[l * kb + j2] = i1; Ainv[l * kb + j1] = i2;
            refreshA(i1, l); refreshA(i2, l); refreshB(j1, l); refreshB(j2, l);
            long long nc = evalcost_lim(lim, &ab);
            if (!ab) {
                cost = nc;
                if (cost == 0) return 1;
            } else {
                P[a] = j1; P[b] = j2;
                Ainv[l * kb + j1] = i1; Ainv[l * kb + j2] = i2;
                refreshA(i1, l); refreshA(i2, l); refreshB(j1, l); refreshB(j2, l);
            }
        } else {
            int i = rint_(kb);
            int idx = l * kb + i;
            int old = S[idx];
            int nw = rint_(G);
            if (nw == old) continue;
            S[idx] = nw;
            sinv[idx] = ginv(nw);
            refreshA(i, l);
            refreshB(P[idx], l);
            long long nc = evalcost_lim(lim, &ab);
            if (!ab) {
                cost = nc;
                if (cost == 0) return 1;
            } else {
                S[idx] = old;
                sinv[idx] = ginv(old);
                refreshA(i, l);
                refreshB(P[idx], l);
            }
        }
    }
    return 0;
}

static void save_best(void) {
    int A = kb * G;
    int m = A * d_;
    int *e = malloc(sizeof(int) * 2 * (size_t)m);
    if (!e) return;
    int c = 0;
    for (int v = 0; v < A; v++)
        for (int l = 0; l < d_; l++) {
            e[2 * c] = v;
            e[2 * c + 1] = nbr[v * d_ + l];
            c++;
        }
    free(best_e);
    best_e = e;
    best_n = NV;
    best_m = m;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int w = 0; w < 20; w++) rnd();
    double limit = atof(argv[4]);
    int kmax = argc > 5 ? atoi(argv[5]) : 4;
    if (kmax < 1) kmax = 1;
    if (kmax > KMAX) kmax = KMAX;
    if (d_ < 1 || D_ < 1 || limit <= 0) { printf("0 0\n"); return 0; }

    static const int KL[] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16};
    const int NK = (int)(sizeof(KL) / sizeof(KL[0]));
    long long trials[KMAX + 1], wins[KMAX + 1];
    memset(trials, 0, sizeof(trials));
    memset(wins, 0, sizeof(wins));

    clock_t t_end = clock() + (clock_t)(limit * CLOCKS_PER_SEC);
    const long long iters = 20000;

    while (clock() < t_end) {
        int k;
        if (rnd() % 4 == 0) {
            k = 1 + rint_(kmax);
        } else {
            double bestv = -1.0;
            k = 1;
            for (int c = 1; c <= kmax; c++) {
                double v = (wins[c] + 1.0) / (trials[c] + 2.0) + 0.05 * rdbl();
                if (v > bestv) { bestv = v; k = c; }
            }
        }
        int half = best_n / (2 * k);
        int Gt = half + 1 + rint_(1 + half / 40);
        if (Gt < 2) Gt = 2;
        int K = KL[rint_(NK)];
        int m = (Gt + K - 1) / K;
        if (m < 2) m = 2;
        int r = 1;
        if (K > 1 && m > 2) {
            for (int t = 0; t < 80; t++) {
                int c = 2 + rint_(m - 2);
                if (gcd_(c, m) == 1 && powmod_(c, K, m) == 1 % m) { r = c; break; }
            }
        }
        gm = m; gK = K; G = m * K; kb = k; NV = 2 * kb * G;

        pw = malloc(sizeof(int) * (size_t)K);
        P = malloc(sizeof(int) * (size_t)d_ * kb);
        S = malloc(sizeof(int) * (size_t)d_ * kb);
        Ainv = malloc(sizeof(int) * (size_t)d_ * kb);
        sinv = malloc(sizeof(int) * (size_t)d_ * kb);
        nbr = malloc(sizeof(int) * (size_t)NV * d_);
        vis = calloc((size_t)NV, sizeof(int));
        que = malloc(sizeof(int) * (size_t)NV);
        if (!pw || !P || !S || !Ainv || !sinv || !nbr || !vis || !que) {
            free(pw); free(P); free(S); free(Ainv); free(sinv); free(nbr); free(vis); free(que);
            break;
        }
        pw[0] = 1 % m;
        for (int b = 1; b < K; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);

        trials[k]++;
        int ok = anneal(iters, t_end);
        if (ok) {
            wins[k]++;
            if (NV > best_n) save_best();
        }
        free(pw); free(P); free(S); free(Ainv); free(sinv); free(nbr); free(vis); free(que);
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++)
        printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
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

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions. A PG(2,q) incidence graph has diameter 3, so it is valid for any D >= 3.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Search budget: leave room for compilation, parsing and validation.
    if time_limit >= 20:
        budget = time_limit - 12.0
    else:
        budget = 0.5 * time_limit
    budget -= time.monotonic() - t0

    if budget >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", 4],
                            stdin_graph=None, timeout=budget + 30.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
