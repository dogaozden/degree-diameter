import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 C engine (unchanged from the parent): voltage lifts of semidirect
# products Z_m x| Z_k2 over a base of K A-vertices and K B-vertices, searched
# by simulated annealing with breakout weights and an elite-pool ILS.
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


# ----------------------------------------------------------------------------
# Stage 2 C engine (new): grow a valid d-regular bipartite graph by two vertices
# at a time. Each growth step splices in one new A-vertex x and one new
# B-vertex y (degree-preserving surgery), then repairs the diameter with
# degree-preserving edge switches (simulated annealing on the number of
# unreachable ordered pairs, computed by bitset BFS). Only zero-cost states
# are kept, so every output is valid.
# ----------------------------------------------------------------------------

GROW_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 2048
#define WS 33
#define DMAX 16
#define EMAX (NMAX * DMAX / 2 + 64)
#define GROW_ITERS 40000

static int D_DEG, DIAM, N, NE, BN, BNE;
static int Ea[EMAX], Eb[EMAX], BEa[EMAX], BEb[EMAX];
static int TEa[EMAX], TEb[EMAX];
static int nbr[NMAX][DMAX];
static int ndeg_tmp[NMAX];
static unsigned char adj[NMAX][NMAX];   /* adj[a][b] = 1 for an edge, a on side 0, b on side 1 */
static int side[NMAX];
static uint64_t R1[NMAX * WS], R2[NMAX * WS];
static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

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

static inline int pop64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of ordered vertex pairs (v, u) with dist(v, u) > DIAM. */
static long long eval_cost(void) {
    int W = (N + 63) >> 6;
    uint64_t *cur = R1, *nxt = R2;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) cur[v * WS + w] = 0;
        cur[v * WS + (v >> 6)] = 1ULL << (v & 63);
    }
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + v * WS;
            const uint64_t *c = cur + v * WS;
            for (int w = 0; w < W; w++) o[w] = c[w];
            for (int k = 0; k < D_DEG; k++) {
                const uint64_t *u = cur + (size_t)nbr[v][k] * WS;
                for (int w = 0; w < W; w++) o[w] |= u[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long cost = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pop64(cur[v * WS + w]);
        cost += N - c;
    }
    return cost;
}

static void replace_nb(int v, int old, int nw) {
    for (int k = 0; k < D_DEG; k++)
        if (nbr[v][k] == old) { nbr[v][k] = nw; return; }
}

/* Edges e1 = (a1,b1), e2 = (a2,b2) become (a1,b2), (a2,b1). Applying it twice undoes it. */
static void do_switch(int e1, int e2) {
    int a1 = Ea[e1], b1 = Eb[e1], a2 = Ea[e2], b2 = Eb[e2];
    replace_nb(a1, b1, b2);
    replace_nb(a2, b2, b1);
    replace_nb(b1, a1, a2);
    replace_nb(b2, a2, a1);
    adj[a1][b1] = 0;
    adj[a2][b2] = 0;
    adj[a1][b2] = 1;
    adj[a2][b1] = 1;
    Eb[e1] = b2;
    Eb[e2] = b1;
}

/* Load an oriented edge list (ea[e] on side 0, eb[e] on side 1) with N vertices. */
static int rebuild(const int *ea, const int *eb, int m) {
    if (N > NMAX || m > EMAX) return 0;
    for (int v = 0; v < N; v++) {
        memset(adj[v], 0, (size_t)N);
        ndeg_tmp[v] = 0;
    }
    for (int e = 0; e < m; e++) {
        int a = ea[e], b = eb[e];
        if (a < 0 || a >= N || b < 0 || b >= N || a == b) return 0;
        if (side[a] != 0 || side[b] != 1) return 0;
        if (ndeg_tmp[a] >= D_DEG || ndeg_tmp[b] >= D_DEG || adj[a][b]) return 0;
        adj[a][b] = 1;
        nbr[a][ndeg_tmp[a]++] = b;
        nbr[b][ndeg_tmp[b]++] = a;
    }
    for (int v = 0; v < N; v++)
        if (ndeg_tmp[v] != D_DEG) return 0;
    for (int e = 0; e < m; e++) { Ea[e] = ea[e]; Eb[e] = eb[e]; }
    NE = m;
    return 1;
}

/* Add vertices x (side 0) and y (side 1). Pick D_DEG distinct B-vertices b_i, remove one
   edge (a_i, b_i) each with distinct a_i, then add (x, b_i) and (a_i, y). Degrees stay D_DEG. */
static int surgery(void) {
    int n0 = N;
    if (n0 + 2 > NMAX) return 0;
    static int Bl[NMAX];
    static int ra[DMAX], rb[DMAX];
    static unsigned char used[NMAX];
    int nb = 0;
    for (int v = 0; v < n0; v++)
        if (side[v] == 1) Bl[nb++] = v;
    if (nb < D_DEG) return 0;
    for (int i = 0; i < D_DEG; i++) {
        int j = i + rnd_int(nb - i);
        int t = Bl[i]; Bl[i] = Bl[j]; Bl[j] = t;
    }
    memset(used, 0, (size_t)n0);
    for (int i = 0; i < D_DEG; i++) {
        int b = Bl[i], ok = 0;
        for (int tr = 0; tr < 4 * D_DEG && !ok; tr++) {
            int a = nbr[b][rnd_int(D_DEG)];
            if (!used[a]) { used[a] = 1; ra[i] = a; rb[i] = b; ok = 1; }
        }
        for (int k = 0; k < D_DEG && !ok; k++) {
            int a = nbr[b][k];
            if (!used[a]) { used[a] = 1; ra[i] = a; rb[i] = b; ok = 1; }
        }
        if (!ok) return 0;
    }
    int x = n0, y = n0 + 1, m = 0;
    for (int e = 0; e < NE; e++) {
        int skip = 0;
        for (int i = 0; i < D_DEG; i++)
            if (Ea[e] == ra[i] && Eb[e] == rb[i]) { skip = 1; break; }
        if (!skip) { TEa[m] = Ea[e]; TEb[m] = Eb[e]; m++; }
    }
    for (int i = 0; i < D_DEG; i++) {
        TEa[m] = x; TEb[m] = rb[i]; m++;
        TEa[m] = ra[i]; TEb[m] = y; m++;
    }
    side[x] = 0;
    side[y] = 1;
    N = n0 + 2;
    return rebuild(TEa, TEb, m);
}

static void output_best(void) {
    printf("%d %d\n", BN, BNE);
    for (int e = 0; e < BNE; e++) printf("%d %d\n", BEa[e], BEb[e]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    D_DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    uint64_t sm = sd * 0x9E3779B97F4A7C15ULL + 777ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int n_in = 0, m_in = 0;
    if (scanf("%d %d", &n_in, &m_in) != 2 || n_in <= 0 || m_in < 0) {
        printf("0 0\n");
        return 0;
    }
    if (D_DEG < 2 || D_DEG > DMAX || DIAM < 2 || n_in + 2 > NMAX || m_in > EMAX - 2 * D_DEG) {
        printf("0 0\n");
        return 0;
    }
    static int IU[EMAX], IV[EMAX], col[NMAX];
    for (int e = 0; e < m_in; e++) {
        if (scanf("%d %d", &IU[e], &IV[e]) != 2) { printf("0 0\n"); return 0; }
        if (IU[e] < 0 || IU[e] >= n_in || IV[e] < 0 || IV[e] >= n_in) { printf("0 0\n"); return 0; }
    }

    /* Bipartition by label propagation. */
    for (int v = 0; v < n_in; v++) col[v] = -1;
    col[0] = 0;
    int changed = 1, bad = 0;
    while (changed) {
        changed = 0;
        for (int e = 0; e < m_in; e++) {
            int u = IU[e], v = IV[e];
            if (col[u] >= 0 && col[v] < 0) { col[v] = 1 - col[u]; changed = 1; }
            else if (col[v] >= 0 && col[u] < 0) { col[u] = 1 - col[v]; changed = 1; }
            else if (col[u] >= 0 && col[u] == col[v]) bad = 1;
        }
    }
    for (int v = 0; v < n_in; v++)
        if (col[v] < 0) bad = 1;
    if (bad) {
        printf("0 0\n");
        return 0;
    }
    N = n_in;
    for (int v = 0; v < N; v++) side[v] = col[v];
    static int Ia[EMAX], Ib[EMAX];
    for (int e = 0; e < m_in; e++) {
        if (side[IU[e]] == 0) { Ia[e] = IU[e]; Ib[e] = IV[e]; }
        else { Ia[e] = IV[e]; Ib[e] = IU[e]; }
    }
    if (!rebuild(Ia, Ib, m_in)) {
        printf("0 0\n");
        return 0;
    }
    if (eval_cost() != 0) {
        printf("0 0\n");
        return 0;
    }
    BN = N;
    BNE = NE;
    memcpy(BEa, Ea, sizeof(int) * (size_t)NE);
    memcpy(BEb, Eb, sizeof(int) * (size_t)NE);

    while (elapsed() < DEADLINE) {
        N = BN;
        if (!rebuild(BEa, BEb, BNE)) break;
        if (!surgery()) continue;
        long long cur = eval_cost();
        for (int it = 0; it < GROW_ITERS && cur > 0; it++) {
            if ((it & 15) == 0 && elapsed() > DEADLINE) break;
            int e1 = rnd_int(NE), e2 = rnd_int(NE);
            if (e1 == e2) continue;
            int a1 = Ea[e1], b1 = Eb[e1], a2 = Ea[e2], b2 = Eb[e2];
            if (a1 == a2 || b1 == b2) continue;
            if (adj[a1][b2] || adj[a2][b1]) continue;
            do_switch(e1, e2);
            long long nc = eval_cost();
            double T = 1.2 * (1.0 - (double)it / GROW_ITERS) + 0.02;
            if (nc <= cur || rnd_unit() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                do_switch(e1, e2);
            }
        }
        if (cur == 0) {
            BN = N;
            BNE = NE;
            memcpy(BEa, Ea, sizeof(int) * (size_t)NE);
            memcpy(BEb, Eb, sizeof(int) * (size_t)NE);
        }
    }
    output_best();
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
# Driver: baselines, then the structured lift search (stage 1), then the
# growth-by-surgery search from its best graph (stage 2). Every candidate is
# checked with lib.is_valid before it can replace the current best.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    def left():
        return time.monotonic() - start

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

    if D >= 4 and left() < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Stage 1: structured voltage-lift search over semidirect products.
    remaining = 0.72 * time_limit - left() - 1.5
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 6.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Stage 2: grow the best regular graph by surgery plus switch annealing.
    remaining = 0.92 * time_limit - left() - 2.0
    if remaining >= 2.0 and D >= 2 and d >= 2 and _is_regular(best[0], best[1], d):
        try:
            out = lib.run_c(GROW_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                            stdin_graph=best, timeout=remaining + 6.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
