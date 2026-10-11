import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Engine 1 (voltage search): annealing over voltage lifts of semidirect
# products Z_m x| Z_k2 with breakout weights and an elite pool (ILS).
# Used first to produce a large base graph.
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
# Engine 2 (new, bold): vertex-augmented repair search.
# Starts from a valid bipartite graph, adds one A and one B vertex at a time,
# and anneals over 2-switches, endpoint moves and edge additions. The cost is
# the number of unordered vertex pairs at distance > D, computed exactly with
# bitset ball expansion. Every zero-cost state is valid by construction
# (bipartite, degree <= d, no duplicate edges, diameter <= D) and is recorded.
# ----------------------------------------------------------------------------

REPAIR_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2600
#define MAXDEG 64
#define MAXM (MAXN * MAXDEG / 2)
#define WMAX ((MAXN + 63) / 64)
#define ITERS 20000
#define T_HI 3.0
#define T_LO 0.2

static int DIAMX, DEG, N, NE;
static int col[MAXN], deg[MAXN], qu[MAXN];
static int adj[MAXN * MAXDEG];
static int EA[MAXM], EB[MAXM];
static int RU[MAXM], RV[MAXM];
static int defA[MAXN], defB[MAXN], nA, nB;
static uint64_t RA[MAXN * WMAX], RB[MAXN * WMAX];
static long long cur_cost;
static int BEA[MAXM], BEB[MAXM], BN = 0, BNE = 0;
static int RUNA[MAXM], RUNB[MAXM];
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

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    const int *p = adj + (size_t)a * MAXDEG;
    for (int k = 0; k < deg[a]; k++)
        if (p[k] == b) return 1;
    return 0;
}

static void adj_add(int v, int u) {
    adj[(size_t)v * MAXDEG + deg[v]] = u;
    deg[v]++;
}

static void adj_del(int v, int u) {
    int *p = adj + (size_t)v * MAXDEG;
    for (int k = 0; k < deg[v]; k++)
        if (p[k] == u) {
            p[k] = p[deg[v] - 1];
            deg[v]--;
            return;
        }
}

/* Set edge slot idx to (a, b). Slot may be fresh (EA = -1) or hold an old pair. */
static void set_edge(int idx, int a, int b) {
    if (EA[idx] >= 0) {
        adj_del(EA[idx], EB[idx]);
        adj_del(EB[idx], EA[idx]);
    }
    EA[idx] = a;
    EB[idx] = b;
    adj_add(a, b);
    adj_add(b, a);
}

/* Unordered pairs at distance > DIAMX, via bitset ball expansion. */
static long long eval_cost(void) {
    int W = (N + 63) / 64;
    uint64_t *cu = RA, *nxb = RB;
    memset(cu, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++) cu[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int lvl = 0; lvl < DIAMX; lvl++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxb + (size_t)v * W;
            const uint64_t *s = cu + (size_t)v * W;
            for (int w = 0; w < W; w++) o[w] = s[w];
            const int *av = adj + (size_t)v * MAXDEG;
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *t = cu + (size_t)av[k] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        uint64_t *tmp = cu; cu = nxb; nxb = tmp;
    }
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *s = cu + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(s[w]);
        tot += N - c;
    }
    return tot / 2;
}

static void build_def(void) {
    nA = nB = 0;
    for (int v = 0; v < N; v++)
        if (deg[v] < DEG) {
            if (col[v] == 0) defA[nA++] = v;
            else defB[nB++] = v;
        }
}

/* Add one non-adjacent pair of deficient vertices (A-B). Adding an edge never raises cost. */
static int add_once(void) {
    if (NE >= MAXM) return 0;
    build_def();
    if (nA == 0 || nB == 0) return 0;
    int st = rnd_int(nA);
    for (int ii = 0; ii < nA; ii++) {
        int a = defA[(st + ii) % nA];
        int sb = rnd_int(nB);
        for (int jj = 0; jj < nB; jj++) {
            int b = defB[(sb + jj) % nB];
            if (!has_edge(a, b)) {
                set_edge(NE, a, b);
                NE++;
                cur_cost = eval_cost();
                return 1;
            }
        }
    }
    return 0;
}

/* One annealing move: 2-switch or endpoint move. Reverted on rejection. */
static void step(double T) {
    int idx[2], oa[2], ob[2], nch = 0;
    if (NE < 1) return;
    if (rnd_int(100) < 60) {
        if (NE < 2) return;
        int i = rnd_int(NE), j = rnd_int(NE);
        if (i == j) return;
        int a1 = EA[i], b1 = EB[i], a2 = EA[j], b2 = EB[j];
        if (a1 == a2 || b1 == b2) return;
        if (has_edge(a1, b2) || has_edge(a2, b1)) return;
        idx[0] = i; oa[0] = a1; ob[0] = b1;
        idx[1] = j; oa[1] = a2; ob[1] = b2;
        nch = 2;
        set_edge(i, a1, b2);
        set_edge(j, a2, b1);
    } else {
        build_def();
        int i = rnd_int(NE);
        int a = EA[i], b = EB[i];
        if (rnd_int(2) == 0) {
            if (nA == 0) return;
            int u = defA[rnd_int(nA)];
            if (u == a || has_edge(u, b)) return;
            set_edge(i, u, b);
        } else {
            if (nB == 0) return;
            int v = defB[rnd_int(nB)];
            if (v == b || has_edge(a, v)) return;
            set_edge(i, a, v);
        }
        idx[0] = i; oa[0] = a; ob[0] = b;
        nch = 1;
    }
    long long c = eval_cost();
    double delta = (double)(c - cur_cost);
    if (delta <= 0 || rnd_unit() < exp(-delta / T)) {
        cur_cost = c;
        return;
    }
    for (int k = nch - 1; k >= 0; k--) set_edge(idx[k], oa[k], ob[k]);
}

/* Replace the current state by edges xa/xb[0..nE) and recompute the cost. */
static void load_from(const int *xa, const int *xb, int nE) {
    for (int i = nE; i < NE; i++) { EA[i] = -1; EB[i] = -1; }
    NE = nE;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < NE; i++) {
        EA[i] = xa[i];
        EB[i] = xb[i];
        adj_add(EA[i], EB[i]);
        adj_add(EB[i], EA[i]);
    }
    cur_cost = eval_cost();
}

static void sa_run(void) {
    long long bestc = cur_cost;
    int bestNE = NE;
    memcpy(RUNA, EA, sizeof(int) * (size_t)NE);
    memcpy(RUNB, EB, sizeof(int) * (size_t)NE);
    for (int it = 0; it < ITERS; it++) {
        if ((it & 127) == 0 && elapsed() > DEADLINE) break;
        double T = T_HI * pow(T_LO / T_HI, (double)it / ITERS);
        add_once();
        if (cur_cost > 0) step(T);
        if (cur_cost < bestc) {
            bestc = cur_cost;
            bestNE = NE;
            memcpy(RUNA, EA, sizeof(int) * (size_t)NE);
            memcpy(RUNB, EB, sizeof(int) * (size_t)NE);
        }
        if (cur_cost == 0) break;
    }
    if (cur_cost > bestc) load_from(RUNA, RUNB, bestNE);
}

static void snapshot(void) {
    BN = N;
    BNE = NE;
    memcpy(BEA, EA, sizeof(int) * (size_t)NE);
    memcpy(BEB, EB, sizeof(int) * (size_t)NE);
}

static void add_pair(void) {
    col[N] = 0; deg[N] = 0;
    col[N + 1] = 1; deg[N + 1] = 0;
    N += 2;
    cur_cost = eval_cost();
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAMX = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    if (DEG < 1 || DEG > MAXDEG - 1 || DIAMX < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 987654ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 0 || n > MAXN - 4 || m < 0 || m > MAXM) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < MAXM; i++) { EA[i] = -1; EB[i] = -1; }
    for (int i = 0; i < MAXN; i++) { deg[i] = 0; col[i] = -1; }
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &RU[i], &RV[i]) != 2) { m = i; break; }
        adj_add(RU[i], RV[i]);
        adj_add(RV[i], RU[i]);
    }

    if (n == 0) {
        N = 2;
        col[0] = 0;
        col[1] = 1;
        NE = 0;
    } else {
        N = n;
        for (int s = 0; s < N; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int qh = 0, qt = 0;
            qu[qt++] = s;
            while (qh < qt) {
                int v = qu[qh++];
                for (int k = 0; k < deg[v]; k++) {
                    int u = adj[(size_t)v * MAXDEG + k];
                    if (col[u] < 0) {
                        col[u] = 1 - col[v];
                        qu[qt++] = u;
                    }
                }
            }
        }
        NE = 0;
        for (int i = 0; i < m; i++) {
            int u = RU[i], v = RV[i];
            if (col[u] == col[v]) continue;
            if (col[u] == 0) { EA[NE] = u; EB[NE] = v; }
            else { EA[NE] = v; EB[NE] = u; }
            NE++;
        }
    }

    /* Rebuild adjacency from the oriented edge list so the state is consistent. */
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < NE; i++) {
        adj_add(EA[i], EB[i]);
        adj_add(EB[i], EA[i]);
    }
    cur_cost = eval_cost();

    while (elapsed() < DEADLINE) {
        while (add_once()) {
        }
        if (cur_cost == 0) {
            snapshot();
            if (N + 2 > MAXN - 4) break;
            add_pair();
            continue;
        }
        sa_run();
    }

    if (BN > 0) {
        printf("%d %d\n", BN, BNE);
        for (int i = 0; i < BNE; i++)
            printf("%d %d\n", BEA[i], BEB[i]);
    } else {
        printf("0 0\n");
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


# ----------------------------------------------------------------------------
# Driver: baselines, then voltage search (engine 1) for half of the remaining
# time, then vertex-augmented repair (engine 2) from the best graph found.
# Every result is validated, and the best valid graph is kept.
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
        return 0.94 * time_limit - (time.monotonic() - start) - 2.0

    # Phase 1: voltage-lift search for a large base graph (half of the budget).
    if left() >= 2.0:
        t1 = 0.5 * left()
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{t1:.2f}", best_n],
                            timeout=t1 + 3.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Phase 2: grow the best graph by vertex pairs and repair it by annealing.
    rem = left()
    if rem >= 1.0:
        try:
            out = lib.run_c(REPAIR_SOURCE, [d, D, seed, f"{rem:.2f}"],
                            stdin_graph=best, timeout=rem + 3.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
