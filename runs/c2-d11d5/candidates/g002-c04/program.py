import math
import time

import lib


# The C engine searches bi-Cayley lifts over semidirect products Z_m x| Z_k2
# with k base vertices per side and d perfect-matching layers. Every vertex has
# degree d. Diameter is checked with bitmasks over the 2k block representatives
# (left translations are automorphisms). Simulated annealing runs entirely in C,
# so each evaluation is far cheaper than the Python/numpy version. The program
# prints the largest valid graph it finds, or "0 0" if nothing beats the lower
# bound passed in.
_C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 40
#define MAXK 4
#define MAXN 60000
#define PEN 1000L

typedef unsigned long long u64;

static u64 rs = 88172645463325252ULL;

static u64 rnext(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) { return (int)(rnext() % (u64)n); }

static double rnd01(void) { return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int dd, DD, KK, GG, NN, MM, K2;
static int pwv[64];
static int Lp[MAXD][MAXK], Linv[MAXD][MAXK], Sv[MAXD][MAXK];
static int nbr[MAXD * MAXN];
static unsigned char reachCur[MAXN], reachTmp[MAXN], reachPrev[MAXN];

static int *bestE = NULL;
static int bestEm = 0;
static int bestN = 0;

static int pc8(unsigned x) {
    int c = 0;
    while (x) {
        c += (int)(x & 1u);
        x >>= 1;
    }
    return c;
}

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long pow_mod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Semidirect product: element a*K2+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long t = ((long long)a + (long long)pwv[b] * (long long)c) % MM;
    int bb = (b + e) % K2;
    return (int)t * K2 + bb;
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long long t = ((long long)pwv[nb] * (long long)a) % MM;
    long long na = ((long long)MM - t) % MM;
    return (int)na * K2 + nb;
}

/* Write layer l's neighbours for A-block i and B-block Lp[l][i]. */
static void set_dart(int l, int i) {
    int j = Lp[l][i];
    int s = Sv[l][i];
    int is = ginv(s);
    int *row = &nbr[(size_t)l * NN];
    int abase = i * GG;
    int bbase = (KK + j) * GG;
    for (int g = 0; g < GG; g++) {
        row[abase + g] = bbase + gmul(g, s);
        row[bbase + g] = abase + gmul(g, is);
    }
}

static void swap_layer(int l, int i1, int i2) {
    int t = Lp[l][i1];
    Lp[l][i1] = Lp[l][i2];
    Lp[l][i2] = t;
    Linv[l][Lp[l][i1]] = i1;
    Linv[l][Lp[l][i2]] = i2;
    set_dart(l, i1);
    set_dart(l, i2);
}

/* Cost = unreached (block representative, vertex) pairs + PEN * duplicate darts. */
static long eval_cost(void) {
    int nb = 2 * KK;
    memset(reachCur, 0, (size_t)NN);
    for (int b = 0; b < nb; b++) reachCur[b * GG] |= (unsigned char)(1u << b);
    for (int t = 0; t < DD; t++) {
        int changed = 0;
        for (int u = 0; u < NN; u++) {
            unsigned x = reachCur[u];
            for (int l = 0; l < dd; l++) x |= reachCur[nbr[(size_t)l * NN + u]];
            reachTmp[u] = (unsigned char)x;
            if (x != (unsigned)reachCur[u]) changed = 1;
        }
        if (!changed) break;
        memcpy(reachCur, reachTmp, (size_t)NN);
    }
    long unr = 0;
    for (int u = 0; u < NN; u++) unr += nb - pc8(reachCur[u]);
    long dup = 0;
    for (int i = 0; i < KK; i++)
        for (int l1 = 0; l1 < dd; l1++)
            for (int l2 = 0; l2 < l1; l2++)
                if (Lp[l1][i] == Lp[l2][i] && Sv[l1][i] == Sv[l2][i]) dup++;
    return unr + PEN * dup;
}

static void random_init(void) {
    for (int l = 0; l < dd; l++) {
        for (int i = 0; i < KK; i++) Lp[l][i] = i;
        for (int i = KK - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = Lp[l][i];
            Lp[l][i] = Lp[l][j];
            Lp[l][j] = t;
        }
        for (int i = 0; i < KK; i++) Linv[l][Lp[l][i]] = i;
        for (int i = 0; i < KK; i++) Sv[l][i] = rndint(GG);
    }
    for (int l = 0; l < dd; l++)
        for (int i = 0; i < KK; i++) set_dart(l, i);
}

static int pick_r(int m, int k2) {
    if (k2 == 1 || m < 3) return 1;
    int t = rndint(3);
    if (t == 0) {
        if (k2 == 2) return m - 1;
        return 1;
    }
    if (t == 1) return 1;
    for (int tr = 0; tr < 300; tr++) {
        int c = 2 + rndint(m - 2);
        if (gcd_i(c, m) == 1 && pow_mod(c, k2, m) == 1 % m) return c;
    }
    return 1;
}

static int run_search(int maxit, int pat, double tend) {
    random_init();
    long cost = eval_cost();
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best = cost;
    int last = 0;
    int full = (1 << (2 * KK)) - 1;
    for (int t = 0; t < maxit && cost > 0; t++) {
        if (t - last > pat) break;
        if ((t & 15) == 0 && now_s() > tend) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)maxit);
        if (temp < 0.5) temp = 0.5;
        memcpy(reachPrev, reachCur, (size_t)NN);
        if (KK >= 2 && rnd01() < 0.2) {
            int l = rndint(dd);
            int i1 = rndint(KK);
            int i2 = rndint(KK - 1);
            if (i2 >= i1) i2++;
            swap_layer(l, i1, i2);
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < best) {
                    best = cost;
                    last = t;
                }
            } else {
                swap_layer(l, i1, i2);
                memcpy(reachCur, reachPrev, (size_t)NN);
            }
            continue;
        }
        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            for (int tr = 0; tr < 30; tr++) {
                int u = rndint(NN);
                if (reachCur[u] != full) {
                    if (u < KK * GG) {
                        i = u / GG;
                        l = rndint(dd);
                    } else {
                        int j = u / GG - KK;
                        l = rndint(dd);
                        i = Linv[l][j];
                    }
                    break;
                }
            }
        }
        if (l < 0) {
            l = rndint(dd);
            i = rndint(KK);
        }
        int sold = Sv[l][i];
        int snew = rndint(GG);
        if (snew == sold) continue;
        Sv[l][i] = snew;
        set_dart(l, i);
        long c2 = eval_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < best) {
                best = cost;
                last = t;
            }
        } else {
            Sv[l][i] = sold;
            set_dart(l, i);
            memcpy(reachCur, reachPrev, (size_t)NN);
        }
    }
    return cost == 0;
}

static int save_solution(void) {
    int nA = KK * GG;
    for (int u = 0; u < nA; u++)
        for (int l1 = 0; l1 < dd; l1++)
            for (int l2 = 0; l2 < l1; l2++)
                if (nbr[(size_t)l1 * NN + u] == nbr[(size_t)l2 * NN + u]) return 0;
    int m = nA * dd;
    int *E = (int *)malloc(sizeof(int) * 2 * (size_t)m);
    if (!E) return 0;
    int p = 0;
    for (int u = 0; u < nA; u++)
        for (int l = 0; l < dd; l++) {
            E[p++] = u;
            E[p++] = nbr[(size_t)l * NN + u];
        }
    free(bestE);
    bestE = E;
    bestEm = m;
    bestN = NN;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    u64 sd = strtoull(argv[3], NULL, 10);
    rs ^= sd * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    int lb = argc > 5 ? atoi(argv[5]) : 0;
    if (dd < 1 || dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    bestN = lb;
    double tend = now_s() + budget;
    static const int K2S[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8,
                                9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    while (now_s() < tend) {
        int k = 1 + rndint(MAXK);
        int gmin = bestN / (2 * k) + 1;
        int gt = gmin + rndint(gmin / 10 + 2);
        if (gt < 2) gt = 2;
        int k2 = K2S[rndint(20)];
        if (k2 > gt) k2 = 1;
        int m = (gt + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = pick_r(m, k2);
        long long Nl = 2LL * k * m * k2;
        if (Nl > MAXN) continue;
        if (Nl <= bestN) continue;
        KK = k;
        K2 = k2;
        MM = m;
        GG = m * k2;
        NN = 2 * k * GG;
        pwv[0] = 1 % m;
        for (int b = 1; b < K2; b++) pwv[b] = (int)((long long)pwv[b - 1] * r % m);
        if (run_search(4000, 1200, tend) && NN > bestN) save_solution();
    }
    if (bestE && bestEm > 0) {
        printf("%d %d\n", bestN, bestEm);
        for (int e = 0; e < bestEm; e++) printf("%d %d\n", bestE[2 * e], bestE[2 * e + 1]);
    } else {
        printf("0 0\n");
    }
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
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n:
            try:
                ok = lib.is_valid(n, e, d, D)
            except Exception:
                ok = False
            if ok:
                best = (n, [tuple(x) for x in e])
                best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            al = lib.araujo_lopez_graph(d - 2)
        except Exception:
            al = None
        if al is not None:
            consider(al[0], al[1])

    # C bi-Cayley search: give it most of the time budget, leave margin for
    # compilation, parsing and validity checking.
    budget = min(0.8 * time_limit - 2.0, time_limit - 10.0)
    if budget >= 2.0 and D >= 3:
        try:
            out = lib.run_c(
                _C_SOURCE,
                [d, D, int(seed) & 0x7FFFFFFF, round(budget, 2), best_n],
                stdin_graph=None,
                timeout=max(budget + 5.0, time_limit - 3.0),
            )
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
