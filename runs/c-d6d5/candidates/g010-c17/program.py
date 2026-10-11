import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Engine 1 (C_LIFT): voltage lifts of semidirect products Z_m x| Z_k2 over a
# base of K A-vertices and K B-vertices, found by simulated annealing with
# breakout weights and an elite pool (ILS). Unchanged from the parent engine.
#
# Engine 2 (C_REPAIR): unstructured search. It takes a valid bipartite graph
# with equal sides, adds one A and one B vertex, and repairs the graph with
# degree-preserving 2-switches, transfers that move a degree deficit, and
# additions between deficient vertices. The cost is bad pairs plus total
# degree deficit. Bad pairs are counted by bit-parallel ball expansion, each
# A or B vertex keeping bitsets of the vertices of each side it reaches. Each
# success is saved and the graph grows again. Output is always a valid graph
# or the input itself.
# ----------------------------------------------------------------------------

C_LIFT = r"""
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

#define MAXH 2048
#define MAXW 32
#define MAXDEG 32
#define TEMP 0.6

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;
static int DEG, DIAM;
static int NA = 0, NB = 0;
static int dgA[MAXH], dgB[MAXH];
static int nbA[MAXH][MAXDEG], nbB[MAXH][MAXDEG];
static unsigned char adjm[MAXH * MAXH];
static uint64_t bufs[8][MAXH][MAXW];
static uint64_t (*SA)[MAXW], (*SB)[MAXW], (*TA)[MAXW], (*TB)[MAXW];
static uint64_t (*nSA)[MAXW], (*nSB)[MAXW], (*nTA)[MAXW], (*nTB)[MAXW];
static int *bp;
static int best_NA = 0, best_m = 0;
static int la[MAXH], lb[MAXH];

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

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int popc_arr(const uint64_t *x, int W) {
    int s = 0;
    for (int w = 0; w < W; w++) s += popc64(x[w]);
    return s;
}

/* Number of unordered pairs at distance > DIAM (unreachable counts too). */
static long long eval_bad(void) {
    int WA = (NA + 63) >> 6, WB = (NB + 63) >> 6;
    for (int a = 0; a < NA; a++) {
        memset(SA[a], 0, sizeof(uint64_t) * (size_t)WA);
        memset(SB[a], 0, sizeof(uint64_t) * (size_t)WB);
        SA[a][a >> 6] |= 1ULL << (a & 63);
    }
    for (int b = 0; b < NB; b++) {
        memset(TA[b], 0, sizeof(uint64_t) * (size_t)WA);
        memset(TB[b], 0, sizeof(uint64_t) * (size_t)WB);
        TB[b][b >> 6] |= 1ULL << (b & 63);
    }
    for (int r = 0; r < DIAM; r++) {
        for (int a = 0; a < NA; a++) {
            uint64_t *xa = nSA[a], *xb = nSB[a];
            memset(xa, 0, sizeof(uint64_t) * (size_t)WA);
            memset(xb, 0, sizeof(uint64_t) * (size_t)WB);
            xa[a >> 6] |= 1ULL << (a & 63);
            for (int k = 0; k < dgA[a]; k++) {
                int b = nbA[a][k];
                const uint64_t *ta = TA[b], *tb = TB[b];
                for (int w = 0; w < WA; w++) xa[w] |= ta[w];
                for (int w = 0; w < WB; w++) xb[w] |= tb[w];
            }
        }
        for (int b = 0; b < NB; b++) {
            uint64_t *xa = nTA[b], *xb = nTB[b];
            memset(xa, 0, sizeof(uint64_t) * (size_t)WA);
            memset(xb, 0, sizeof(uint64_t) * (size_t)WB);
            xb[b >> 6] |= 1ULL << (b & 63);
            for (int k = 0; k < dgB[b]; k++) {
                int a = nbB[b][k];
                const uint64_t *sa = SA[a], *sb = SB[a];
                for (int w = 0; w < WA; w++) xa[w] |= sa[w];
                for (int w = 0; w < WB; w++) xb[w] |= sb[w];
            }
        }
        uint64_t (*t)[MAXW];
        t = SA; SA = nSA; nSA = t;
        t = SB; SB = nSB; nSB = t;
        t = TA; TA = nTA; nTA = t;
        t = TB; TB = nTB; nTB = t;
    }
    long long unr = 0;
    for (int a = 0; a < NA; a++)
        unr += (NA - popc_arr(SA[a], WA)) + (NB - popc_arr(SB[a], WB));
    for (int b = 0; b < NB; b++)
        unr += (NA - popc_arr(TA[b], WA)) + (NB - popc_arr(TB[b], WB));
    return unr / 2;
}

static void del_nb(int *arr, int *deg, int x) {
    for (int k = 0; k < *deg; k++) {
        if (arr[k] == x) {
            arr[k] = arr[*deg - 1];
            (*deg)--;
            return;
        }
    }
}

static void add_edge(int a, int b) {
    nbA[a][dgA[a]++] = b;
    nbB[b][dgB[b]++] = a;
    adjm[a * MAXH + b] = 1;
}

static void remove_edge(int a, int b) {
    del_nb(nbA[a], &dgA[a], b);
    del_nb(nbB[b], &dgB[b], a);
    adjm[a * MAXH + b] = 0;
}

static int rand_edge(int *ra, int *rb) {
    for (int t = 0; t < 200; t++) {
        int a = rnd_int(NA);
        if (dgA[a] > 0) {
            *ra = a;
            *rb = nbA[a][rnd_int(dgA[a])];
            return 1;
        }
    }
    return 0;
}

static long long def_side(void) {
    long long s = 0;
    for (int a = 0; a < NA; a++) s += DEG - dgA[a];
    return s;
}

static void save_best(void) {
    best_NA = NA;
    best_m = 0;
    for (int a = 0; a < NA; a++)
        for (int k = 0; k < dgA[a]; k++) {
            bp[2 * best_m] = a;
            bp[2 * best_m + 1] = nbA[a][k];
            best_m++;
        }
}

static int accept(long long newc, long long oldc) {
    if (newc <= oldc) return 1;
    return rnd_unit() < exp(-(double)(newc - oldc) / TEMP);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 999ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);
    SA = bufs[0]; SB = bufs[1]; TA = bufs[2]; TB = bufs[3];
    nSA = bufs[4]; nSB = bufs[5]; nTA = bufs[6]; nTB = bufs[7];
    bp = malloc(sizeof(int) * 2 * MAXH * MAXDEG);

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || m < 0 || n > 2 * MAXH) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    int *ev = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (eu[i] < 0 || eu[i] >= n || ev[i] < 0 || ev[i] >= n) {
            printf("0 0\n");
            return 0;
        }
    }

    /* CSR adjacency and 2-colouring. */
    int *st = calloc((size_t)n + 1, sizeof(int));
    for (int i = 0; i < m; i++) { st[eu[i] + 1]++; st[ev[i] + 1]++; }
    for (int v = 0; v < n; v++) st[v + 1] += st[v];
    int *pos = malloc(sizeof(int) * (size_t)n);
    memcpy(pos, st, sizeof(int) * (size_t)n);
    int *al = malloc(sizeof(int) * (size_t)(2 * m + 1));
    for (int i = 0; i < m; i++) {
        al[pos[eu[i]]++] = ev[i];
        al[pos[ev[i]]++] = eu[i];
    }
    int *col = malloc(sizeof(int) * (size_t)n);
    int *q = malloc(sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            for (int k = st[u]; k < st[u + 1]; k++) {
                int v = al[k];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    q[tail++] = v;
                } else if (col[v] == col[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    int *idx = malloc(sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) {
        if (col[v] == 0) idx[v] = NA++;
        else idx[v] = NB++;
    }
    if (NA != NB || NA == 0 || NA + 2 >= MAXH) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        if (col[u] == 1) { int t = u; u = v; v = t; }
        int a = idx[u], b = idx[v];
        if (dgA[a] >= DEG || dgB[b] >= DEG || adjm[a * MAXH + b]) {
            printf("0 0\n");
            return 0;
        }
        add_edge(a, b);
    }
    if (eval_bad() != 0) {
        printf("0 0\n");
        return 0;
    }

    /* The input is valid: keep it as the fallback, then grow one A and one B vertex. */
    save_best();
    NA++; NB++;
    long long bad = eval_bad();
    long long defA = def_side();
    long long cost = bad + defA;
    const double TMAX = 1e18;
    (void)TMAX;

    while (elapsed() < DEADLINE) {
        if (bad == 0 && defA == 0) {
            save_best();
            if (NA + 2 >= MAXH) break;
            NA++; NB++;
            bad = eval_bad();
            defA = def_side();
            cost = bad + defA;
            continue;
        }

        int na = 0, nb = 0;
        for (int a = 0; a < NA; a++) if (dgA[a] < DEG) la[na++] = a;
        for (int b = 0; b < NB; b++) if (dgB[b] < DEG) lb[nb++] = b;
        double u = rnd_unit();

        /* Additions never raise the bad-pair count, so accept them directly. */
        if (na > 0 && nb > 0 && u < 0.35) {
            int done = 0;
            for (int t = 0; t < 40 && !done; t++) {
                int a = la[rnd_int(na)], b = lb[rnd_int(nb)];
                if (!adjm[a * MAXH + b]) {
                    add_edge(a, b);
                    done = 1;
                }
            }
            if (done) {
                bad = eval_bad();
                defA = def_side();
                cost = bad + defA;
                continue;
            }
        }

        if (na > 0 && u < 0.6) {
            /* A-side transfer: deficient a0 takes edge (a1,b1) from a1. */
            int a0 = la[rnd_int(na)], a1, b1;
            if (!rand_edge(&a1, &b1) || a1 == a0 || adjm[a0 * MAXH + b1]) continue;
            remove_edge(a1, b1);
            add_edge(a0, b1);
            long long nbad = eval_bad();
            long long nd = def_side();
            long long nc = nbad + nd;
            if (accept(nc, cost)) {
                bad = nbad; defA = nd; cost = nc;
            } else {
                remove_edge(a0, b1);
                add_edge(a1, b1);
            }
        } else if (nb > 0 && u < 0.8) {
            /* B-side transfer: deficient b0 takes edge (a1,b1) from b1. */
            int b0 = lb[rnd_int(nb)], a1, b1;
            if (!rand_edge(&a1, &b1) || b1 == b0 || adjm[a1 * MAXH + b0]) continue;
            remove_edge(a1, b1);
            add_edge(a1, b0);
            long long nbad = eval_bad();
            long long nd = def_side();
            long long nc = nbad + nd;
            if (accept(nc, cost)) {
                bad = nbad; defA = nd; cost = nc;
            } else {
                remove_edge(a1, b0);
                add_edge(a1, b1);
            }
        } else {
            /* Degree-preserving 2-switch. */
            int a1, b1, a2, b2;
            if (!rand_edge(&a1, &b1) || !rand_edge(&a2, &b2)) continue;
            if (a1 == a2 || b1 == b2 || adjm[a1 * MAXH + b2] || adjm[a2 * MAXH + b1]) continue;
            remove_edge(a1, b1);
            remove_edge(a2, b2);
            add_edge(a1, b2);
            add_edge(a2, b1);
            long long nbad = eval_bad();
            long long nc = nbad + defA;
            if (accept(nc, cost)) {
                bad = nbad; cost = nc;
            } else {
                remove_edge(a1, b2);
                remove_edge(a2, b1);
                add_edge(a1, b1);
                add_edge(a2, b2);
            }
        }
    }

    /* Output the largest valid graph found. */
    printf("%d %d\n", best_NA + best_NA, best_m);
    for (int i = 0; i < best_m; i++)
        printf("%d %d\n", bp[2 * i], best_NA + bp[2 * i + 1]);
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


# ----------------------------------------------------------------------------
# Driver: baselines, then lift annealing (C_LIFT), then unstructured repair
# (C_REPAIR) started from the best graph found so far.
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

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    def left():
        # Keep a margin for compilation, process start, parsing and validation.
        return 0.9 * time_limit - (time.monotonic() - start) - 1.0

    # Phase 1: voltage-lift annealing, only for graphs larger than the current best.
    rem = left()
    if rem >= 4.0:
        p1 = 0.45 * rem
        try:
            out = lib.run_c(C_LIFT, [d, D, seed, f"{p1:.2f}", best_n],
                            timeout=p1 + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Phase 2: unstructured repair search that grows the best graph found so far.
    rem = left()
    if rem >= 2.0:
        try:
            out = lib.run_c(C_REPAIR, [d, D, seed, f"{rem:.2f}"],
                            stdin_graph=best, timeout=rem + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
