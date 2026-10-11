import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Two engines.
#
# 1. C_SOURCE (annealing over voltage lifts of semidirect products) finds a
#    good regular start graph. This is the parent engine, unchanged.
#
# 2. C_REPAIR (new): grows a valid d-regular bipartite graph by vertex-pair
#    insertion followed by repair. Take d edges (a_i, y_i) with distinct a_i
#    and distinct y_i. Replace them with a* ~ y_i and b* ~ a_i, where a* and
#    b* are new vertices on opposite sides. Every degree stays d. The
#    result is then repaired by degree-preserving edge switches (2-switches
#    that keep the graph simple and bipartite), annealing on the number of
#    vertex pairs at distance > D. Reachability is computed with bitsets, so
#    one full evaluation costs roughly a fraction of a millisecond at this
#    size. A successful repair is saved and growth continues from it. A failed
#    attempt restarts from the last saved graph with a new random insertion.
#
# The Python driver spends about 40% of the budget on the annealing start,
# then the rest on repair growth from the best graph. Every returned graph is
# checked with lib.is_valid, and a Haar fallback is kept.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define ITERS 6000
#define ILS_ITERS 3000
#define POOLMAX 48
#define POOLP 0.6
#define BRK 150

static uint64_t rs[2];
static struct timespec T0;

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

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int DEG, DIAM, K, K2, M, G, T, MAXT;
static int R;
static int *Rpow;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int *bestJ, *bestS;
static int curstamp;
static double DEADLINE;
static int best_n, best_m;
static int *best_e = NULL;

static long long *wt = NULL;
static long long *unc = NULL;
static long long wsum_w = 0;
static long long last_w = 0;

typedef struct {
    int K, K2, M, R;
    long long cost;
    int *J, *S;
} Cfg;

static Cfg pool[POOLMAX];
static int npool = 0;

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

static long long eval_cost(void) {
    int N = 2 * K * G;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) {
                for (int r = 0; r < 2 * K; r++) unc[r] = 0;
                last_w = BIGC;
                return BIGC;
            }
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * G, bj = (K + dJ[t]) * G;
        const int *pm = perm + (size_t)t * G;
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        f[0] = src;
        stamp[src] = curstamp;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
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
        unc[r] = N - count;
        total += N - count;
    }
    long long w = 0;
    for (int r = 0; r < 2 * K; r++) w += wt[r] * unc[r];
    last_w = w;
    return total;
}

static void alloc_config(void) {
    int N = 2 * K * G;
    T = DEG * K;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bestJ = malloc(sizeof(int) * (size_t)T);
    bestS = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    Rpow = malloc(sizeof(int) * (size_t)K2);
    wt = malloc(sizeof(long long) * (size_t)(2 * K));
    unc = malloc(sizeof(long long) * (size_t)(2 * K));
    curstamp = 0;
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
}

static void free_config(void) {
    free(dI); free(dJ); free(dS); free(bestJ); free(bestS);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx); free(Rpow);
    free(wt); free(unc);
    dI = dJ = dS = bestJ = bestS = perm = adj = cnt = stamp = fr = nx = Rpow = NULL;
    wt = unc = NULL;
}

static void setup_group(int k, int c2, int m, int r) {
    K = k; K2 = c2; M = m; R = r; G = m * c2;
    alloc_config();
    for (int t = 0; t < T; t++) dI[t] = t % K;
    for (int b = 0; b < 2 * K; b++) wt[b] = 1;
    wsum_w = 2 * K;
}

static void emit(void) {
    int m = T * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++) {
        for (int g = 0; g < G; g++) {
            best_e[idx++] = dI[t] * G + g;
            best_e[idx++] = (K + dJ[t]) * G + perm[(size_t)t * G + g];
        }
    }
    best_m = m;
    best_n = 2 * K * G;
}

static void random_init(void) {
    int p[8];
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            int t = l * K + i;
            dI[t] = i;
            dJ[t] = p[i];
            dS[t] = rnd_int(G);
        }
    }
    for (int t = 0; t < T; t++) build_perm(t);
}

static void perturb(int nmoves) {
    for (int s = 0; s < nmoves; s++) {
        if (K > 1 && rnd_unit() < 0.3) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
        } else {
            int t = rnd_int(T);
            dS[t] = rnd_int(G);
            build_perm(t);
        }
    }
}

static long long run_sa(int iters, double tscale, long long cost) {
    long long bestc = cost;
    long long wcur = last_w;
    long long prevc = cost;
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        if (it > 0 && it % BRK == 0) {
            if (cost < BIGC && cost >= prevc) {
                eval_cost();
                for (int r = 0; r < 2 * K; r++)
                    if (unc[r] > 0) { wt[r]++; wsum_w++; }
                wcur = 0;
                for (int r = 0; r < 2 * K; r++) wcur += wt[r] * unc[r];
            }
            prevc = cost;
        }
        double sc = (double)wsum_w / (2.0 * K);
        double temp = tscale * (3.0 * (1.0 - (double)it / iters) + 0.05) * sc;
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2;
                wcur = w2;
            } else {
                tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            }
        } else {
            int t = rnd_int(T);
            int olds = dS[t];
            int news = rnd_int(G);
            if (news == olds) continue;
            dS[t] = news;
            build_perm(t);
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2;
                wcur = w2;
            } else {
                dS[t] = olds;
                build_perm(t);
            }
        }
        if (cost < bestc) {
            bestc = cost;
            memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
            memcpy(bestS, dS, sizeof(int) * (size_t)T);
        }
    }
    return bestc;
}

static void finish_run(long long bc) {
    if (bc == 0) {
        memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
        memcpy(dS, bestS, sizeof(int) * (size_t)T);
        for (int t = 0; t < T; t++) build_perm(t);
        if (2 * K * G > best_n) emit();
    }
}

static void pool_add(long long cost, const int *J, const int *S) {
    if (cost <= 0 || cost >= BIGC) return;
    int slot;
    if (npool < POOLMAX) {
        slot = npool++;
    } else {
        slot = 0;
        for (int i = 1; i < POOLMAX; i++)
            if (pool[i].cost > pool[slot].cost) slot = i;
        if (pool[slot].cost <= cost) return;
    }
    Cfg *c = &pool[slot];
    c->K = K; c->K2 = K2; c->M = M; c->R = R; c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)T);
    memcpy(c->S, S, sizeof(int) * (size_t)T);
}

static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++) {
        long long nn = 2LL * pool[i].K * pool[i].K2 * pool[i].M;
        if (nn > best_n) cand[nc++] = i;
    }
    if (nc == 0) return -1;
    int bi = cand[rnd_int(nc)];
    for (int s = 0; s < 2; s++) {
        int c = cand[rnd_int(nc)];
        if (pool[c].cost < pool[bi].cost) bi = c;
    }
    return bi;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
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
    MAXT = 3 * DEG;
    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].S = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].cost = BIGC;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kc[5] = {1, 1, 2, 2, 3};
    while (elapsed() < DEADLINE) {
        int pi = -1;
        if (rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            Cfg c = pool[pi];
            setup_group(c.K, c.K2, c.M, c.R);
            memcpy(dJ, c.J, sizeof(int) * (size_t)T);
            memcpy(dS, c.S, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            for (int t = 0; t < T; t++) build_perm(t);
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            finish_run(bc);
            pool_add(bc, bestJ, bestS);
            free_config();
            continue;
        }

        int k = kc[rnd_int(5)];
        int gmin = best_n / (2 * k) + 1;
        int spread = gmin / 6 + 2;
        int g = gmin + rnd_int(spread);
        if (g < 2) g = 2;
        int opts[12], no = 0;
        for (int c = 1; c <= 12; c++)
            if (g % c == 0 && g / c >= 2) opts[no++] = c;
        int c2 = opts[rnd_int(no)];
        int m = g / c2, r = 1;
        if (c2 > 1) {
            int found = 0;
            for (int tr = 0; tr < 200 && !found; tr++) {
                int cand = 1 + rnd_int(m - 1);
                if (gcd_i(cand, m) == 1 && powmod(cand, c2, m) == 1 % m) {
                    r = cand;
                    found = 1;
                }
            }
            if (!found) {
                c2 = 1;
                m = g;
                r = 1;
            }
        }
        setup_group(k, c2, m, r);
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cost);
        finish_run(bc);
        pool_add(bc, bestJ, bestS);
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


C_REPAIR = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define ATTEMPT_SEC 5.0

static int d, D, n;
static int *nb;        /* n*d neighbour lists (grown up to MAXN*d) */
static int *side;      /* 0 = A side, 1 = B side */
static int *sv_nb;     /* saved valid graph */
static int sv_n;
static uint64_t *R0, *R1;
static struct timespec T0;
static double DEADLINE;
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

static int rnd_int(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > D (bitset ball propagation). */
static long long eval_cost(void) {
    int Wc = (n + 63) / 64;
    uint64_t *A = R0, *B = R1;
    memset(A, 0, sizeof(uint64_t) * (size_t)n * Wc);
    for (int v = 0; v < n; v++) A[(size_t)v * Wc + v / 64] |= 1ULL << (v % 64);
    for (int lvl = 0; lvl < D; lvl++) {
        for (int v = 0; v < n; v++) {
            uint64_t *bv = B + (size_t)v * Wc;
            memcpy(bv, A + (size_t)v * Wc, sizeof(uint64_t) * (size_t)Wc);
            const int *p = nb + (size_t)v * d;
            for (int k = 0; k < d; k++) {
                const uint64_t *au = A + (size_t)p[k] * Wc;
                for (int w = 0; w < Wc; w++) bv[w] |= au[w];
            }
        }
        uint64_t *t = A; A = B; B = t;
    }
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *av = A + (size_t)v * Wc;
        for (int w = 0; w < Wc; w++) c += pc64(av[w]);
        tot += n - c;
    }
    return tot / 2;
}

static void repl(int u, int oldv, int newv) {
    int *p = nb + (size_t)u * d;
    for (int k = 0; k < d; k++)
        if (p[k] == oldv) { p[k] = newv; return; }
}

/* Edges (x1,y1),(x2,y2) become (x1,y2),(x2,y1). Degrees are unchanged. */
static void sw(int x1, int y1, int x2, int y2) {
    repl(x1, y1, y2);
    repl(y1, x1, x2);
    repl(x2, y2, y1);
    repl(y2, x2, x1);
}

static int has_edge(int a, int b) {
    const int *p = nb + (size_t)a * d;
    for (int k = 0; k < d; k++)
        if (p[k] == b) return 1;
    return 0;
}

static int propose(int *x1, int *y1, int *x2, int *y2) {
    int a1, a2;
    do { a1 = rnd_int(n); } while (side[a1] != 0);
    do { a2 = rnd_int(n); } while (side[a2] != 0);
    int b1 = nb[(size_t)a1 * d + rnd_int(d)];
    int b2 = nb[(size_t)a2 * d + rnd_int(d)];
    if (a1 == a2 || b1 == b2) return 0;
    if (has_edge(a1, b2) || has_edge(a2, b1)) return 0;
    *x1 = a1; *y1 = b1; *x2 = a2; *y2 = b2;
    return 1;
}

/* Insert two new vertices (A-side NA and B-side NB) by removing d edges
   (a_i, y_i) with distinct a_i and distinct y_i. Keeps d-regularity. */
static int grow(void) {
    if (n + 2 > MAXN) return 0;
    static int *Al = NULL;
    if (!Al) Al = malloc(sizeof(int) * MAXN);
    int na = 0;
    for (int v = 0; v < n; v++)
        if (side[v] == 0) Al[na++] = v;
    if (na < d) return 0;
    int as[64], ys[64];
    int found = 0;
    for (int tries = 0; tries < 10000 && !found; tries++) {
        for (int i = 0; i < d; i++) {
            int j = i + rnd_int(na - i);
            int tmp = Al[i]; Al[i] = Al[j]; Al[j] = tmp;
            as[i] = Al[i];
            ys[i] = nb[(size_t)as[i] * d + rnd_int(d)];
        }
        int ok = 1;
        for (int i = 0; i < d && ok; i++)
            for (int j = 0; j < i; j++)
                if (ys[i] == ys[j]) { ok = 0; break; }
        if (ok) found = 1;
    }
    if (!found) return 0;
    int NA = n, NB = n + 1;
    side[NA] = 0;
    side[NB] = 1;
    for (int i = 0; i < d; i++) {
        int a = as[i], y = ys[i];
        repl(a, y, NB);
        repl(y, a, NA);
        nb[(size_t)NA * d + i] = y;
        nb[(size_t)NB * d + i] = a;
    }
    n += 2;
    return 1;
}

static void save_state(void) {
    sv_n = n;
    memcpy(sv_nb, nb, sizeof(int) * (size_t)n * d);
}

static void restore_state(void) {
    n = sv_n;
    memcpy(nb, sv_nb, sizeof(int) * (size_t)n * d);
}

/* Simulated annealing on bad-pair count with 2-switch moves. */
static int anneal(double alen) {
    double t0 = elapsed();
    long long cur = eval_cost();
    double temp = 1.0;
    long long it = 0;
    while (cur > 0) {
        if ((it & 127) == 0) {
            double now = elapsed();
            if (now > DEADLINE || now - t0 > alen) break;
            double frac = (now - t0) / alen;
            temp = 1.2 * (1.0 - frac) + 0.03;
        }
        it++;
        int x1, y1, x2, y2;
        if (!propose(&x1, &y1, &x2, &y2)) continue;
        sw(x1, y1, x2, y2);
        long long c2 = eval_cost();
        if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / temp)) {
            cur = c2;
        } else {
            sw(x1, y2, x2, y1);
        }
    }
    return cur == 0;
}

static int color_sides(void) {
    int *q = malloc(sizeof(int) * MAXN);
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            for (int k = 0; k < d; k++) {
                int w = nb[(size_t)u * d + k];
                if (side[w] < 0) {
                    side[w] = 1 - side[u];
                    q[tail++] = w;
                } else if (side[w] == side[u]) {
                    free(q);
                    return 0;
                }
            }
        }
    }
    free(q);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit < graph\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    uint64_t sm = sd * 2654435761ULL + 999ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    if (d < 2 || d > 64 || D < 1) { printf("0 0\n"); return 0; }
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 2 || n0 > MAXN - 2 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *deg = calloc((size_t)n0, sizeof(int));
    int ok = 1;
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { ok = 0; break; }
        if (eu[i] < 0 || eu[i] >= n0 || ev[i] < 0 || ev[i] >= n0 || eu[i] == ev[i]) { ok = 0; break; }
        deg[eu[i]]++;
        deg[ev[i]]++;
    }
    if (ok)
        for (int v = 0; v < n0; v++)
            if (deg[v] != d) { ok = 0; break; }
    if (!ok) { printf("0 0\n"); return 0; }

    nb = malloc(sizeof(int) * (size_t)MAXN * d);
    side = malloc(sizeof(int) * (size_t)MAXN);
    sv_nb = malloc(sizeof(int) * (size_t)MAXN * d);
    R0 = malloc(sizeof(uint64_t) * (size_t)MAXN * (MAXN / 64));
    R1 = malloc(sizeof(uint64_t) * (size_t)MAXN * (MAXN / 64));
    int *fill = calloc((size_t)n0, sizeof(int));
    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = ev[i];
        nb[(size_t)u * d + fill[u]++] = v;
        nb[(size_t)v * d + fill[v]++] = u;
    }
    n = n0;
    if (!color_sides()) { printf("0 0\n"); return 0; }
    if (eval_cost() != 0) { printf("0 0\n"); return 0; }
    save_state();

    while (elapsed() < DEADLINE) {
        restore_state();
        if (!grow()) break;
        double rem = DEADLINE - elapsed();
        if (rem <= 0) break;
        double alen = ATTEMPT_SEC < rem ? ATTEMPT_SEC : rem;
        if (anneal(alen)) save_state();
    }

    int m = sv_n * d / 2;
    printf("%d %d\n", sv_n, m);
    for (int v = 0; v < sv_n; v++)
        for (int k = 0; k < d; k++) {
            int u = sv_nb[(size_t)v * d + k];
            if (v < u) printf("%d %d\n", v, u);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _is_regular(n, edges, d):
    """True if every vertex 0..n-1 has degree exactly d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


# ----------------------------------------------------------------------------
# Driver: baselines, then annealing start, then repair growth.
# ----------------------------------------------------------------------------

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

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best_n >= lib.moore_bound(d, D):
        return best

    def left():
        return 0.92 * time_limit - (time.monotonic() - start)

    # Phase 1: annealing over voltage lifts gives a regular start graph.
    p1 = 0.4 * (left() - 4.0)
    if p1 >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{p1:.2f}", best_n],
                            timeout=p1 + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Phase 2: grow the best regular graph by vertex-pair insertion and repair.
    if _is_regular(best[0], best[1], d) and left() > 4.0:
        p2 = left() - 2.5
        if p2 >= 1.0:
            try:
                out = lib.run_c(C_REPAIR, [d, D, seed + 1, f"{p2:.2f}"],
                                stdin_graph=best, timeout=p2 + 8.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
