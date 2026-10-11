"""Voltage-lift search over semidirect products Z_m x| Z_k2 with warm-start growth.

New in this version:
  * Warm-start growth. A valid lift with K base rows per side is extended to K+1
    rows by inserting one new A-row and one new B-row into every layer. Each layer
    stays a bijection, so every base vertex keeps degree DEG. Existing voltages are
    kept and the annealer then repairs the new rows. The search walks up through
    K = 1, 2, 3, ... for a fixed group, instead of restarting from random lifts.
  * Soft duplicate penalty. Parallel darts (same row, column and voltage) cost
    DUPPEN instead of being forbidden, so the annealer can pass through them.
    Cost 0 still implies a simple graph.
  * Table-based duplicate detection with a generation stamp, so no memset per eval.
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

#define BIGC 1000000000LL
#define DUPPEN 40LL
#define LIMK 1400
#define GMAX 160
#define ITERS_FRESH 5000
#define ITERS_GROW 6000

static uint64_t rs[2];

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int DEG, DIAM;
static int K, K2, M, G, R, KCAP;
static int *Rpow;
static int *dI, *dJ, *dS, *bestJ, *bestS, *prevJ, *prevS, *pbuf;
static int *perm, *adj, *cnt, *stamp, *fr, *nx, *dupmark;
static int curstamp, dupstamp;
static double DEADLINE;
static int best_n, best_m;
static int *best_e = NULL;

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod(long long b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static inline int tix(int l, int i) { return l * KCAP + i; }

/* (a,b)*(c,e) = (a + r^b c, b + e), element index a*K2 + b. */
static inline int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
    int rb = (b + e) % K2;
    return ra * K2 + rb;
}

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

static void rebuild_active(void) {
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++)
            build_perm(tix(l, i));
}

/* Cost = (ordered unreached pairs from the 2K representatives) + DUPPEN * (parallel darts). */
static long long eval_cost(void) {
    int N = 2 * K * G;
    long long dup = 0;
    if (dupstamp >= 2000000000) {
        memset(dupmark, 0, sizeof(int) * (size_t)KCAP * KCAP * G);
        dupstamp = 0;
    }
    dupstamp++;
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++) {
            int t = tix(l, i);
            size_t key = ((size_t)dI[t] * KCAP + (size_t)dJ[t]) * G + (size_t)dS[t];
            if (dupmark[key] == dupstamp) dup++;
            else dupmark[key] = dupstamp;
        }

    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++) {
            int t = tix(l, i);
            int ai = i * G, bj = (K + dJ[t]) * G;
            const int *pm = perm + (size_t)t * G;
            for (int g = 0; g < G; g++) {
                int a = ai + g, b = bj + pm[g];
                adj[(size_t)a * DEG + cnt[a]++] = b;
                adj[(size_t)b * DEG + cnt[b]++] = a;
            }
        }

    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;  /* identity element of base vertex r */
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        f[0] = src;
        stamp[src] = curstamp;
        for (int lvl = 0; lvl < DIAM && fsz > 0 && count < N; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                const int *au = adj + (size_t)f[q] * DEG;
                for (int e = 0; e < DEG; e++) {
                    int v = au[e];
                    if (stamp[v] != curstamp) {
                        stamp[v] = curstamp;
                        h[nsz++] = v;
                    }
                }
            }
            count += nsz;
            int *tmp = f; f = h; h = tmp;
            fsz = nsz;
        }
        total += N - count;
    }
    return total + DUPPEN * dup;
}

static void alloc_config(void) {
    int TT = DEG * KCAP;
    size_t NN = (size_t)2 * KCAP * G;
    dI = calloc((size_t)TT, sizeof(int));
    dJ = calloc((size_t)TT, sizeof(int));
    dS = calloc((size_t)TT, sizeof(int));
    bestJ = calloc((size_t)TT, sizeof(int));
    bestS = calloc((size_t)TT, sizeof(int));
    prevJ = calloc((size_t)TT, sizeof(int));
    prevS = calloc((size_t)TT, sizeof(int));
    pbuf = malloc(sizeof(int) * (size_t)KCAP);
    perm = malloc(sizeof(int) * (size_t)TT * G);
    adj = malloc(sizeof(int) * NN * DEG);
    cnt = malloc(sizeof(int) * NN);
    stamp = calloc(NN, sizeof(int));
    fr = malloc(sizeof(int) * NN);
    nx = malloc(sizeof(int) * NN);
    dupmark = calloc((size_t)KCAP * KCAP * G, sizeof(int));
    Rpow = malloc(sizeof(int) * (size_t)K2);
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
    dupstamp = 0;
}

static void free_config(void) {
    free(dI); free(dJ); free(dS); free(bestJ); free(bestS);
    free(prevJ); free(prevS); free(pbuf);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx);
    free(dupmark); free(Rpow);
    dI = dJ = dS = bestJ = bestS = prevJ = prevS = NULL;
    pbuf = perm = adj = NULL;
    cnt = stamp = fr = nx = dupmark = NULL;
    Rpow = NULL;
}

/* Random start: each layer is a random bijection between the K A-rows and K B-rows. */
static void init_fresh(void) {
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) pbuf[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int tmp = pbuf[i]; pbuf[i] = pbuf[j]; pbuf[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            int t = tix(l, i);
            dI[t] = i;
            dJ[t] = pbuf[i];
            dS[t] = rnd_int(G);
        }
    }
    rebuild_active();
}

/* Warm-start growth: insert new A-row nr and B-row nr into every layer.
 * In each layer a random old row r gives its B-target to the new row, and the new
 * B-row is taken by r with its old voltage. The layer stays a bijection. The new
 * row's voltage is random. */
static void grow_init(void) {
    int nr = K;
    for (int l = 0; l < DEG; l++) {
        int r = rnd_int(nr);
        int tr = tix(l, r), tn = tix(l, nr);
        dI[tn] = nr;
        dJ[tn] = dJ[tr];
        dS[tn] = rnd_int(G);
        dJ[tr] = nr;
    }
    K++;
    rebuild_active();
}

static void save_prev(void) {
    memcpy(prevJ, dJ, sizeof(int) * (size_t)DEG * KCAP);
    memcpy(prevS, dS, sizeof(int) * (size_t)DEG * KCAP);
}

static void restore_prev(int k) {
    memcpy(dJ, prevJ, sizeof(int) * (size_t)DEG * KCAP);
    memcpy(dS, prevS, sizeof(int) * (size_t)DEG * KCAP);
    K = k;
    rebuild_active();
}

/* Simulated annealing on the active darts. Returns the best cost and leaves the
 * best state in place. Moves: swap two B-targets in one layer, or change one voltage. */
static long long anneal(int iters) {
    long long cost = eval_cost();
    long long bestc = cost;
    memcpy(bestJ, dJ, sizeof(int) * (size_t)DEG * KCAP);
    memcpy(bestS, dS, sizeof(int) * (size_t)DEG * KCAP);

    for (int it = 0; it < iters && bestc > 0; it++) {
        if (elapsed() > DEADLINE) break;
        double temp = 3.0 * (1.0 - (double)it / iters) + 0.05;
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = tix(l, i1), t2 = tix(l, i2);
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long long c2 = eval_cost();
            if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            }
        } else {
            int t = tix(rnd_int(DEG), rnd_int(K));
            int olds = dS[t];
            int news = rnd_int(G);
            if (news == olds) continue;
            dS[t] = news;
            build_perm(t);
            long long c2 = eval_cost();
            if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                dS[t] = olds;
                build_perm(t);
            }
        }
        if (cost < bestc) {
            bestc = cost;
            memcpy(bestJ, dJ, sizeof(int) * (size_t)DEG * KCAP);
            memcpy(bestS, dS, sizeof(int) * (size_t)DEG * KCAP);
        }
    }
    memcpy(dJ, bestJ, sizeof(int) * (size_t)DEG * KCAP);
    memcpy(dS, bestS, sizeof(int) * (size_t)DEG * KCAP);
    rebuild_active();
    return bestc;
}

/* Output the current (valid) lift if it beats the best order so far. */
static void emit(void) {
    int N = 2 * K * G;
    if (N <= best_n) return;
    int m = DEG * K * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++) {
            int t = tix(l, i);
            for (int g = 0; g < G; g++) {
                best_e[idx++] = i * G + g;
                best_e[idx++] = (K + dJ[t]) * G + perm[(size_t)t * G + g];
            }
        }
    best_m = m;
    best_n = N;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n]\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int start_n = argc > 5 ? atoi(argv[5]) : 0;
    best_n = start_n;
    best_m = 0;
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int c2opts[8] = {1, 1, 1, 2, 2, 3, 4, 6};
    while (elapsed() < DEADLINE - 1.0) {
        /* Choose a group Z_m x| Z_c2 with order G = m*c2 <= GMAX. */
        int c2 = c2opts[rnd_int(8)];
        int mhi = GMAX / c2;
        if (mhi < 4) { c2 = 1; mhi = GMAX; }
        int m = 4 + rnd_int(mhi - 3);
        int r = 1;
        if (c2 > 1) {
            int found = 0;
            for (int tr = 0; tr < 200 && !found; tr++) {
                int cand = 1 + rnd_int(m - 1);
                if (gcd_i(cand, m) == 1 && powmod(cand, c2, m) == 1 % m) {
                    r = cand;
                    found = 1;
                }
            }
            if (!found) { c2 = 1; r = 1; }
        }
        M = m;
        K2 = c2;
        R = r;
        G = m * c2;
        KCAP = LIMK / G + 2;
        alloc_config();

        K = 1;
        init_fresh();
        long long c = anneal(ITERS_FRESH);
        if (c == 0) {
            emit();
            int fails = 0;
            while (K < KCAP && fails < 2 && elapsed() < DEADLINE - 0.5) {
                save_prev();
                int kp = K;
                grow_init();
                c = anneal(ITERS_GROW);
                if (c == 0) {
                    emit();
                    fails = 0;
                } else {
                    restore_prev(kp);
                    fails++;
                }
            }
        }
        free_config();
    }

    if (best_m > 0) {
        printf("%d %d\n", best_n, best_m);
        for (int i = 0; i < best_m; i++)
            printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
    } else {
        printf("0 0\n");
    }
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
    start = time.monotonic()
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if best_n >= lib.moore_bound(d, D):
        return best

    remaining = 0.85 * time_limit - (time.monotonic() - start) - 2.0
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 5.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
