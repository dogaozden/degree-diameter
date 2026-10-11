import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 engine (unchanged family): voltage lifts of semidirect products
# Z_m x| Z_k over a small K+K base, simulated annealing with breakout weights
# and an elite pool for iterated local search.
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


# ----------------------------------------------------------------------------
# Stage 2 engine (new construction): unstructured repair-and-grow search.
#
# Input: a valid bipartite graph with max degree d (the best graph so far).
# Each attempt inserts two new vertices (one per side) by removing d-1
# pairwise-disjoint edges and reconnecting their endpoints to the new pair.
# Degrees stay at most d. Simulated annealing then rewires the graph
# (degree-preserving 2-switches, plus rare add/remove edge moves) to minimise
# the number of vertex pairs at distance > D. Zero cost means a valid graph
# with two more vertices, which is saved and grown again. Failed attempts
# restart from the last saved valid graph.
# ----------------------------------------------------------------------------

C_REPAIR = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1400
#define MAXW 22
#define MAXE (MAXN * 16)
#define ITER 15000

static int DEG, DIAM, N, M;
static int side[MAXN];
static int dg[MAXN];
static int nbr[MAXN][16];
static unsigned char adjm[MAXN][MAXN];
static int EA[MAXE], EB[MAXE];
static int snapEA[MAXE], snapEB[MAXE], snapN, snapM;
static uint64_t bufA[MAXN * MAXW], bufB[MAXN * MAXW];
static uint64_t rs[2];
static struct timespec TS0;
static double DEADLINE;
static int markA[MAXN], markB[MAXN], mstamp = 0;
static int dlA[MAXN], dlB[MAXN];

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t next64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int k) { return (int)(next64() % (uint64_t)k); }
static double rnd_unit(void) { return (double)(next64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - TS0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - TS0.tv_nsec);
}

static void remove_from(int x, int y) {
    for (int k = 0; k < dg[x]; k++)
        if (nbr[x][k] == y) { nbr[x][k] = nbr[x][--dg[x]]; return; }
}

static void link_e(int x, int y) {
    nbr[x][dg[x]++] = y;
    nbr[y][dg[y]++] = x;
    adjm[x][y] = 1;
    adjm[y][x] = 1;
}

static void unlink_e(int x, int y) {
    remove_from(x, y);
    remove_from(y, x);
    adjm[x][y] = 0;
    adjm[y][x] = 0;
}

static void rebuild(void) {
    memset(adjm, 0, sizeof adjm);
    for (int v = 0; v < N; v++) dg[v] = 0;
    for (int i = 0; i < M; i++) link_e(EA[i], EB[i]);
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered vertex pairs at distance > DIAM. */
static long long eval_bad(void) {
    const int w = (N + 63) >> 6;
    for (int v = 0; v < N; v++) {
        uint64_t *row = bufA + (size_t)v * w;
        for (int k = 0; k < w; k++) row[k] = 0;
        row[v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t *cur = bufA, *nxt = bufB;
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * w;
            const uint64_t *c = cur + (size_t)v * w;
            for (int k = 0; k < w; k++) o[k] = c[k];
            for (int e = 0; e < dg[v]; e++) {
                const uint64_t *u = cur + (size_t)nbr[v][e] * w;
                for (int k = 0; k < w; k++) o[k] |= u[k];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *row = cur + (size_t)v * w;
        int cnt = 0;
        for (int k = 0; k < w; k++) cnt += pc64(row[k]);
        bad += N - cnt;
    }
    return bad / 2;
}

static void snap_save(void) {
    snapN = N;
    snapM = M;
    memcpy(snapEA, EA, sizeof(int) * (size_t)M);
    memcpy(snapEB, EB, sizeof(int) * (size_t)M);
}

static void snap_restore(void) {
    N = snapN;
    M = snapM;
    memcpy(EA, snapEA, sizeof(int) * (size_t)M);
    memcpy(EB, snapEB, sizeof(int) * (size_t)M);
    rebuild();
}

/* Add two vertices A2 (side 0) and B2 (side 1): remove DEG-1 disjoint edges
   (a_k, b_k), join A2 to every b_k and B2 to every a_k, and join A2-B2.
   All degrees stay <= DEG and the graph stays bipartite. */
static int grow_one(void) {
    int K = DEG - 1;
    if (K < 1 || M < K + 2 || N + 2 > MAXN - 4 || M + K + 2 >= MAXE - 4) return 0;
    int ea[16], eb[16], idx[16];
    mstamp++;
    int cnt = 0, tries = 0;
    while (cnt < K && tries < 2000) {
        tries++;
        int i = rnd_int(M);
        int a = EA[i], b = EB[i];
        if (markA[a] == mstamp || markB[b] == mstamp) continue;
        markA[a] = mstamp;
        markB[b] = mstamp;
        idx[cnt] = i; ea[cnt] = a; eb[cnt] = b;
        cnt++;
    }
    if (cnt < K) return 0;
    int A2 = N, B2 = N + 1;
    side[A2] = 0; side[B2] = 1;
    dg[A2] = 0; dg[B2] = 0;
    N += 2;
    for (int k = 0; k < K; k++) unlink_e(ea[k], eb[k]);
    for (int k = 0; k < K; k++) {
        link_e(A2, eb[k]);
        link_e(ea[k], B2);
        EA[idx[k]] = A2;
        EB[idx[k]] = eb[k];
        EA[M] = ea[k]; EB[M] = B2; M++;
    }
    link_e(A2, B2);
    EA[M] = A2; EB[M] = B2; M++;
    return 1;
}

/* Simulated annealing on the bad-pair count. Returns the final cost. */
static long long sa_run(int iters) {
    long long cost = eval_bad();
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 127) == 0 && elapsed() > DEADLINE) break;
        double temp = (0.08 * (double)cost + 1.0) * (1.0 - (double)it / iters) + 0.1;
        double r = rnd_unit();
        long long nc;
        if (r < 0.70) {
            if (M < 2) continue;
            int i = rnd_int(M), j = rnd_int(M);
            if (i == j) continue;
            int a = EA[i], b = EB[i], c = EA[j], e = EB[j];
            if (a == c || b == e || adjm[a][e] || adjm[c][b]) continue;
            unlink_e(a, b);
            unlink_e(c, e);
            link_e(a, e);
            link_e(c, b);
            EB[i] = e; EB[j] = b;
            nc = eval_bad();
            if (nc <= cost || rnd_unit() < exp(-(double)(nc - cost) / temp)) {
                cost = nc;
            } else {
                unlink_e(a, e);
                unlink_e(c, b);
                link_e(a, b);
                link_e(c, e);
                EB[i] = b; EB[j] = e;
            }
        } else if (r < 0.85) {
            int na = 0, nbk = 0;
            for (int v = 0; v < N; v++) {
                if (dg[v] < DEG) {
                    if (side[v] == 0) dlA[na++] = v;
                    else dlB[nbk++] = v;
                }
            }
            if (na == 0 || nbk == 0 || M + 2 >= MAXE) continue;
            int x = -1, y = -1;
            for (int tries = 0; tries < 20; tries++) {
                int p = dlA[rnd_int(na)], q = dlB[rnd_int(nbk)];
                if (!adjm[p][q]) { x = p; y = q; break; }
            }
            if (x < 0) continue;
            link_e(x, y);
            EA[M] = x; EB[M] = y; M++;
            nc = eval_bad();
            if (nc <= cost || rnd_unit() < exp(-(double)(nc - cost) / temp)) {
                cost = nc;
            } else {
                M--;
                unlink_e(x, y);
            }
        } else {
            if (M <= 1) continue;
            int i = rnd_int(M);
            int a = EA[i], b = EB[i];
            int L = M - 1;
            unlink_e(a, b);
            EA[i] = EA[L]; EB[i] = EB[L];
            M = L;
            nc = eval_bad();
            if (nc <= cost || rnd_unit() < exp(-(double)(nc - cost) / temp)) {
                cost = nc;
            } else {
                EA[L] = EA[i]; EB[L] = EB[i];
                EA[i] = a; EB[i] = b;
                M = L + 1;
                link_e(a, b);
            }
        }
    }
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit < graph\n");
        return 1;
    }
    timespec_get(&TS0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    uint64_t sm = sd * 0x9E3779B97F4A7C15ULL + 777ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || n0 > MAXN - 4 ||
        DEG < 2 || DEG > 15 || DIAM < 1 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    N = n0;
    M = 0;
    memset(adjm, 0, sizeof adjm);
    for (int v = 0; v < N; v++) dg[v] = 0;
    int ok = 1;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v || adjm[u][v] ||
            dg[u] >= DEG || dg[v] >= DEG) { ok = 0; break; }
        link_e(u, v);
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    static int queue[MAXN];
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N && ok; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt && ok) {
            int x = queue[qh++];
            for (int k = 0; k < dg[x]; k++) {
                int y = nbr[x][k];
                if (side[y] == -1) {
                    side[y] = 1 - side[x];
                    queue[qt++] = y;
                } else if (side[y] == side[x]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    M = 0;
    for (int v = 0; v < N; v++) {
        if (side[v] != 0) continue;
        for (int k = 0; k < dg[v]; k++) {
            EA[M] = v;
            EB[M] = nbr[v][k];
            M++;
        }
    }
    snap_save();

    while (elapsed() < DEADLINE) {
        snap_restore();
        while (1) {
            if (!grow_one()) break;
            if (elapsed() > DEADLINE) break;
            long long c = sa_run(ITER);
            if (c == 0) {
                snap_save();
                continue;
            }
            break;
        }
    }

    printf("%d %d\n", snapN, snapM);
    for (int i = 0; i < snapM; i++) printf("%d %d\n", snapEA[i], snapEB[i]);
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


def _araujo(d):
    """Araujo-Pardo & Lopez graph for degree d = q + 2 with q a prime power >= 3; diameter 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
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
# Driver: baselines, then stage 1 (lift annealer), then stage 2 (repair/grow).
# ----------------------------------------------------------------------------

def _attempt(source, d, D, seed, budget, time_limit, used, graph, tail):
    """Run one C engine for about `budget` seconds while staying inside the case's limit."""
    hard = min(budget + 3.0, time_limit - used() - 2.0)
    budget = min(budget, hard - 2.0)
    if budget < 1.0:
        return None
    try:
        out = lib.run_c(source, [d, D, seed, f"{budget:.2f}", *tail],
                        stdin_graph=graph, timeout=hard)
        return lib.parse_graph_text(out)
    except Exception:
        return None


def build(d, D, seed, time_limit):
    start = time.monotonic()

    def used():
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
        for builder in (_best_pg, _araujo):
            try:
                g = builder(d)
                if g is not None:
                    consider(g[0], g[1])
            except Exception:
                pass

    if D >= 4 and used() < 0.3 * time_limit:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Stage 1: voltage-lift annealer on about 45% of the remaining budget.
    budget1 = 0.45 * (0.9 * time_limit - used() - 1.5)
    out = _attempt(C_LIFT, d, D, seed, budget1, time_limit, used, None, [best_n])
    if out is not None:
        consider(out[0], out[1])

    # Stage 2: repair-and-grow search started from the best graph so far.
    if 2 <= d <= 15 and best_n <= 1300:
        budget2 = 0.9 * time_limit - used() - 1.5
        out = _attempt(C_REPAIR, d, D, seed, budget2, time_limit, used, best, [])
        if out is not None:
            consider(out[0], out[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
