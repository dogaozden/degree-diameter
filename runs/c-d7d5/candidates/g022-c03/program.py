import time

import lib


# ----------------------------------------------------------------------------
# Exact baseline: incidence graph of PG(2, q), diameter 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# C engine: simulated annealing over group lifts (voltage graphs).
#
# Each graph is a bi-regular lift over a group G of order G = m*k, realised as
# the semidirect product Z_m x|_r Z_k (r = 1 gives the direct product). The
# base graph has K vertices per side and Dd dart layers. Layer l is a
# permutation P[l] of the K base vertices together with voltages S[l][i] in G:
#   A_{i,g} is joined to B_{P[l][i], g * S[l][i]} for every layer l.
# Every vertex then has degree exactly Dd. Left translation by G is an
# automorphism, so distances only need to be measured from the 2K vertices
# A_{i,e} and B_{j,e}.
#
# Cost = (number of unreached (source, vertex) pairs within DD steps)
#        + PEN * (number of duplicate darts). Cost 0 means a valid graph.
#
# Unlike the earlier breakout search, each group gets a fresh annealing run
# with a geometric temperature schedule, and the group order is ratcheted
# upward from the best order found so far. Group families are sampled from
# all divisors of the target order up to 64.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 4
#define PEN 40
#define ITERS 60000L
#define RUNS 2

static int Dd = 3, DD = 3, K = 1;
static int GM = 1, GK = 1, GR = 1, GG = 1;
static int gpow[64];
static int P[MAXD][MAXK], S[MAXD][MAXK];
static int bestP[MAXD][MAXK], bestS[MAXD][MAXK];
static int *adjv = NULL, *vis = NULL, *qu = NULL;
static int capN = 0, stamp = 1;
static int g_dup = 0, g_unr = 0;
static double deadline = 0.0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double rnd01(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static long long gcdll(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GR = r;
    GG = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = (int)p;
        p = (p * r) % m;
    }
}

/* Semidirect product: (a,b)*(c,d) = (a + r^b c, b + d), element coded a*GK + b. */
static inline int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static void ensure_cap(int N) {
    if (N <= capN) return;
    free(adjv);
    free(vis);
    free(qu);
    capN = N;
    adjv = malloc(sizeof(int) * (size_t)N * MAXD);
    vis = calloc((size_t)N, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)N);
    if (!adjv || !vis || !qu) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    stamp = 1;
}

/* Full evaluation of the current (P, S) state. */
static long long eval_cost(void) {
    int G = GG, N = 2 * K * G;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = P[l][i], s = S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                adjv[(size_t)a * Dd + l] = b;
                adjv[(size_t)b * Dd + l] = a;
            }
        }
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (P[l1][i] == P[l2][i] && S[l1][i] == S[l2][i]) dup++;

    if (stamp > 1000000000) {
        memset(vis, 0, sizeof(int) * (size_t)capN);
        stamp = 1;
    }
    long long unr = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        stamp++;
        int head = 0, tail = 0;
        vis[src] = stamp;
        qu[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = qu[head++];
                const int *nb = adjv + (size_t)u * Dd;
                for (int t = 0; t < Dd; t++) {
                    int v = nb[t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        qu[tail++] = v;
                    }
                }
            }
        }
        unr += N - tail;
    }
    g_dup = dup;
    g_unr = (int)unr;
    return unr + (long long)PEN * dup;
}

static void copy_best(void) {
    memcpy(bestP, P, sizeof P);
    memcpy(bestS, S, sizeof S);
}

static void random_init(void) {
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) P[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = P[l][i];
            P[l][i] = P[l][j];
            P[l][j] = t;
        }
        for (int i = 0; i < K; i++) S[l][i] = rint_(GG);
    }
}

/* Simulated annealing from the current state. Returns the best cost seen;
   bestP/bestS hold the matching state. */
static long long run_sa(long iters) {
    long long c = eval_cost();
    long long bc = c;
    copy_best();
    const double T0 = 3.0, T1 = 0.2;
    for (long it = 0; it < iters && bc > 0; it++) {
        if ((it & 255) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int l = rint_(Dd);
        int i = rint_(K);
        int swp = (K >= 2 && rint_(3) == 0);
        int i2 = i, old = 0, tmp = 0;
        if (swp) {
            i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            tmp = P[l][i];
            P[l][i] = P[l][i2];
            P[l][i2] = tmp;
        } else {
            old = S[l][i];
            S[l][i] = rint_(GG);
        }
        long long c2 = eval_cost();
        if (c2 <= c || rnd01() < exp((double)(c - c2) / T)) {
            c = c2;
            if (c < bc) {
                bc = c;
                copy_best();
            }
        } else {
            if (swp) {
                tmp = P[l][i];
                P[l][i] = P[l][i2];
                P[l][i2] = tmp;
            } else {
                S[l][i] = old;
            }
        }
    }
    return bc;
}

/* Pick a group of order exactly G as Z_m x|_r Z_k with k | G, k <= 64. */
static void sample_group(int G, int *om, int *ok, int *orr) {
    int divs[64], nd = 0;
    for (int k = 1; k <= 64 && k <= G; k++)
        if (G % k == 0) divs[nd++] = k;
    int idx = 0;
    if (nd > 1 && rint_(10) < 7) idx = 1 + rint_(nd - 1);
    int k = divs[idx];
    int m = G / k;
    int r = 1;
    if (k > 1 && m > 2) {
        for (int t = 0; t < 300; t++) {
            long long c = 2 + (long long)rint_(m - 2);
            if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                r = (int)c;
                break;
            }
        }
    }
    *om = m;
    *ok = k;
    *orr = r;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int min_n = argc > 5 ? atoi(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;

    int best_n = min_n;
    int have = 0;
    int oK = 1, oM = 1, oKk = 1, oR = 1;
    static int outP[MAXD][MAXK], outS[MAXD][MAXK];

    while (now_s() < deadline) {
        int roll = rint_(10);
        int Kc = roll < 5 ? 1 : (roll < 8 ? 2 : (roll < 9 ? 3 : 4));
        long long G0 = (long long)best_n / (2LL * Kc) + 1;
        long long span = G0 / 40 + 3;
        long long G = G0 + (long long)rint_((int)span);
        if (G > 2000) G = 2000;

        int m, k, r;
        sample_group((int)G, &m, &k, &r);
        set_group(m, k, r);
        K = Kc;
        int N = 2 * K * GG;
        ensure_cap(N);

        int found = 0;
        for (int run = 0; run < RUNS && !found && now_s() < deadline; run++) {
            random_init();
            long long bc = run_sa(ITERS);
            if (bc == 0) found = 1;
        }
        if (found) {
            best_n = N;
            have = 1;
            oK = K;
            oM = GM;
            oKk = GK;
            oR = GR;
            memcpy(outP, bestP, sizeof bestP);
            memcpy(outS, bestS, sizeof bestS);
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }

    K = oK;
    set_group(oM, oKk, oR);
    memcpy(P, outP, sizeof P);
    memcpy(S, outS, sizeof S);
    int G = GG;
    int n = 2 * K * G;
    long m = (long)Dd * K * G;
    printf("%d %ld\n", n, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = P[l][i], s = S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                printf("%d %d\n", a, b);
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact baseline first, then the annealing search, with a
# guaranteed-valid fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    hard_end = start + max(2.0, min(0.85 * tl, tl - 7.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    if D >= 3:
        try:
            pg = _best_pg(d)
        except Exception:
            pg = None
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if d >= 3 and D >= 3:
        c_budget = hard_end - time.monotonic() - 1.0
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                timeout=min(c_budget + 6.0, tl - 2.0))
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
