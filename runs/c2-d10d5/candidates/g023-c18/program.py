"""Bi-Cayley search over nonabelian semidirect groups (Z_m x|_r Z_k2).

Approach: the graph is a bi-Cayley graph. Vertices are A_g and B_g for g in a group G of
order M*K2. Edges are A_g -- B_{g s} for s in a connection set S of size d. Left
multiplication is an automorphism, so the diameter is at most D exactly when every vertex
is within distance D of A_1 and of B_1. Each candidate is scored by two BFS runs, and a
simulated-annealing walk swaps elements of S. The group order grows as successes accumulate.
An iterated-local-search memory restarts from the best near miss with a few random kicks.

Fallback: K_{d,d} (diameter 2) and PG(2,q) for D = 3. Every returned graph is checked with lib.is_valid.
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

#define MAXDEG 48
#define NKCH 17
#define FRESH_ITERS 5000
#define ILS_ITERS 3000

static const int KCH[NKCH] = {1,2,2,3,4,5,6,7,8,9,10,12,14,16,18,20,24};

static uint64_t rs;
static uint64_t rnd64(void) {
    uint64_t x = rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rs = x;
    return x * 2685821657736338717ULL;
}
static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}
static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static int DEG, DIAM, CAP;
static double TL, tstart;
static int timed_out = 0;

/* group Z_M x|_R Z_K2, order G = M*K2; element (a,b) coded a*K2+b */
static int M, K2, R, G;
static int64_t PWR[64];
static int *AA, *BB, *dist, *qu;

static int S[MAXDEG], Sinv[MAXDEG];
static int runS[MAXDEG];
static int winS[MAXDEG];

static double elapsed(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
}

static int64_t powmod(int64_t b, int64_t e, int64_t m) {
    int64_t r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int64_t gcd64(int64_t a, int64_t b) {
    while (b) {
        int64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int sample_group(int64_t target) {
    for (int att = 0; att < 200; att++) {
        int k2 = KCH[rndint(NKCH)];
        int64_t m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int64_t r = -1;
        if (k2 == 1) {
            r = 1;
        } else if (rnd01() < 0.25) {
            r = 1;
        } else if (k2 == 2 && rnd01() < 0.5) {
            r = m - 1;
        } else {
            for (int tries = 0; tries < 80; tries++) {
                int64_t c = (m > 2) ? 2 + (int64_t)rndint((int)(m - 2)) : 1;
                if (gcd64(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                    r = c;
                    break;
                }
            }
        }
        if (r < 0) continue;
        M = (int)m;
        K2 = k2;
        R = (int)r;
        G = M * K2;
        return 1;
    }
    return 0;
}

static void setup_group(void) {
    for (int t = 0; t < K2; t++) PWR[t] = powmod(R, t, M);
    for (int x = 0; x < G; x++) {
        AA[x] = x / K2;
        BB[x] = x % K2;
    }
}

/* (a,b)(c,e) = (a + r^b c, b + e) */
static int gmul(int x, int y) {
    int bx = BB[x];
    int64_t a2 = (AA[x] + PWR[bx] * (int64_t)AA[y]) % M;
    int b2 = (bx + BB[y]) % K2;
    return (int)(a2 * K2 + b2);
}

/* inverse of (a,b) is (-r^{-b} a, -b) */
static int ginv(int x) {
    int b = BB[x];
    int nb = (K2 - b) % K2;
    int64_t a2 = (M - (PWR[nb] * (int64_t)AA[x]) % M) % M;
    return (int)(a2 * K2 + nb);
}

static int in_prefix(int x, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == x) return 1;
    return 0;
}

static void random_S(void) {
    for (int j = 0; j < DEG; j++) {
        int x;
        do {
            x = rndint(G);
        } while (in_prefix(x, j));
        S[j] = x;
        Sinv[j] = ginv(x);
    }
}

/* Unreached vertices from src within DIAM steps. Vertices 0..G-1 are A, G..2G-1 are B.
   A_g ~ B_{g s} for s in S; B_h ~ A_{h s^{-1}}. */
static int bfs_unreached(int src) {
    int NN = 2 * G;
    for (int v = 0; v < NN; v++) dist[v] = -1;
    int head = 0, tail = 0;
    qu[tail++] = src;
    dist[src] = 0;
    while (head < tail) {
        int v = qu[head++];
        int dv = dist[v];
        if (dv >= DIAM) continue;
        if (v < G) {
            for (int j = 0; j < DEG; j++) {
                int w = G + gmul(v, S[j]);
                if (dist[w] < 0) {
                    dist[w] = dv + 1;
                    qu[tail++] = w;
                }
            }
        } else {
            int h = v - G;
            for (int j = 0; j < DEG; j++) {
                int w = gmul(h, Sinv[j]);
                if (dist[w] < 0) {
                    dist[w] = dv + 1;
                    qu[tail++] = w;
                }
            }
        }
    }
    return NN - tail;
}

static int64_t cost_now(void) {
    return (int64_t)bfs_unreached(0) + (int64_t)bfs_unreached(G);
}

static int in_S(int x) {
    return in_prefix(x, DEG);
}

/* Simulated annealing on S for the current group. Leaves S at its best state. */
static int64_t run_sa(int iters, int reinit, double tfac) {
    if (reinit) random_S();
    int64_t cur = cost_now();
    int64_t bestc = cur;
    memcpy(runS, S, sizeof(int) * DEG);
    double T0 = tfac * (1.0 + 0.02 * (double)cur);
    for (int t = 0; t < iters && cur > 0; t++) {
        if ((t & 63) == 0 && elapsed() > TL) {
            timed_out = 1;
            break;
        }
        int j = rndint(DEG);
        int old = S[j], oldi = Sinv[j];
        int x;
        do {
            x = rndint(G);
        } while (in_S(x));
        S[j] = x;
        Sinv[j] = ginv(x);
        int64_t c2 = cost_now();
        double temp = T0 * (1.0 - (double)t / (double)iters) + 0.05;
        if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / temp)) {
            cur = c2;
            if (cur < bestc) {
                bestc = cur;
                memcpy(runS, S, sizeof(int) * DEG);
            }
        } else {
            S[j] = old;
            Sinv[j] = oldi;
        }
    }
    memcpy(S, runS, sizeof(int) * DEG);
    for (int j = 0; j < DEG; j++) Sinv[j] = ginv(S[j]);
    return bestc;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    long long found = atoll(argv[3]);
    CAP = atoi(argv[4]);
    unsigned long long seed = strtoull(argv[5], NULL, 10);
    TL = atof(argv[6]);
    tstart = (double)clock() / CLOCKS_PER_SEC;

    rs = ((uint64_t)seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (DEG < 3 || DEG > MAXDEG || DIAM < 2 || CAP < 8) {
        printf("0 0\n");
        return 0;
    }

    AA = malloc(sizeof(int) * (size_t)(CAP + 2));
    BB = malloc(sizeof(int) * (size_t)(CAP + 2));
    dist = malloc(sizeof(int) * (size_t)(CAP + 2));
    qu = malloc(sizeof(int) * (size_t)(CAP + 2));
    if (!AA || !BB || !dist || !qu) {
        printf("0 0\n");
        return 0;
    }

    int have_best = 0, have_near = 0;
    int64_t near_cost = 0;
    int nM = 0, nK2 = 0, nR = 0, nG = 0;
    int near_S[MAXDEG];
    int bM = 0, bK2 = 0, bR = 0, bG = 0;

    while (elapsed() < TL && found < CAP) {
        int64_t cc;
        if (have_near && rnd01() < 0.5) {
            /* Iterated local search: kick the saved near miss, then re-anneal gently. */
            M = nM;
            K2 = nK2;
            R = nR;
            G = nG;
            setup_group();
            memcpy(S, near_S, sizeof(int) * DEG);
            for (int j = 0; j < DEG; j++) Sinv[j] = ginv(S[j]);
            int kicks = 1 + rndint(3);
            for (int q = 0; q < kicks; q++) {
                int j = rndint(DEG);
                int x;
                do {
                    x = rndint(G);
                } while (in_S(x));
                S[j] = x;
                Sinv[j] = ginv(x);
            }
            cc = run_sa(ILS_ITERS, 0, 0.15);
        } else {
            int64_t base = found / 2;
            int64_t span = base / 10 + 2;
            int64_t target = base + 1 + rndint((int)span);
            if (!sample_group(target)) continue;
            if (G < 2 * DEG + 2) continue;
            long long N = 2LL * G;
            if (N <= found || N > CAP) continue;
            setup_group();
            cc = run_sa(FRESH_ITERS, 1, 0.5);
        }

        if (cc == 0) {
            found = 2LL * G;
            have_best = 1;
            have_near = 0;
            memcpy(winS, S, sizeof(int) * DEG);
            bM = M;
            bK2 = K2;
            bR = R;
            bG = G;
        } else if (!timed_out) {
            if (!have_near || cc < near_cost) {
                have_near = 1;
                near_cost = cc;
                nM = M;
                nK2 = K2;
                nR = R;
                nG = G;
                memcpy(near_S, S, sizeof(int) * DEG);
            }
        }
        if (timed_out) break;
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    M = bM;
    K2 = bK2;
    R = bR;
    G = bG;
    setup_group();
    printf("%d %d\n", 2 * G, G * DEG);
    for (int g = 0; g < G; g++)
        for (int j = 0; j < DEG; j++)
            printf("%d %d\n", g, G + gmul(g, winS[j]));
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact construction for D = 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, time_limit - 5.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best

    if d >= 3 and D >= 3:
        remaining = deadline - time.monotonic()
        cap = lib.moore_bound(d, D)
        if remaining > 2.0 and best_n < cap:
            try:
                text = lib.run_c(
                    C_SOURCE,
                    [d, D, best_n, cap, int(seed) & 0x7FFFFFFF, round(remaining, 2)],
                    timeout=max(5.0, time_limit - (time.monotonic() - start) - 2.0),
                )
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
