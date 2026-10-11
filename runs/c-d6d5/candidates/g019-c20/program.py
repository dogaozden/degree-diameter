import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Stage A engine (unchanged from the parent): voltage lifts of semidirect
# products Z_m x| Z_k2 over a small base, found by annealing with breakout
# weights and an elite pool (ILS).
# ----------------------------------------------------------------------------

GROUP_C = r"""
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
# Stage B engine (new): unstructured growth of a d-regular bipartite graph.
# State: N+N vertices, every vertex of degree exactly d. Moves are double edge
# swaps, scored by the number of ordered vertex pairs at distance > D (bitset
# BFS). When the cost hits 0, the graph is snapshotted and grown by one
# vertex per side: remove d edges (a_i, b_i) and attach a new A vertex to all
# b_i and a new B vertex to all a_i. Annealing then repairs the diameter.
# ----------------------------------------------------------------------------

GROW_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXV 4096
#define MAXW 64
#define MAXD 16

static int d_, D_, N;
static int adjA[MAXN][MAXD];
static int adjB[MAXN][MAXD];
static unsigned char ex[MAXN][MAXN];
static int snapN = 0;
static int snapAdj[MAXN][MAXD];
static uint64_t RA[MAXV][MAXW], RB[MAXV][MAXW];
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

static int pop64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of ordered pairs (u,v) with dist(u,v) > D_ (0 means valid). */
static long long eval_cost(void) {
    int V = 2 * N, W = (V + 63) >> 6;
    uint64_t (*cur)[MAXW] = RA;
    uint64_t (*nxt)[MAXW] = RB;
    uint64_t (*tmp)[MAXW];
    for (int v = 0; v < V; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * (size_t)W);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int lvl = 0; lvl < D_; lvl++) {
        for (int v = 0; v < V; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * (size_t)W);
            if (v < N) {
                for (int k = 0; k < d_; k++) {
                    const uint64_t *src = cur[N + adjA[v][k]];
                    for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
                }
            } else {
                for (int k = 0; k < d_; k++) {
                    const uint64_t *src = cur[adjB[v - N][k]];
                    for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
                }
            }
        }
        tmp = cur; cur = nxt; nxt = tmp;
    }
    long long total = 0;
    for (int v = 0; v < V; v++)
        for (int w = 0; w < W; w++)
            total += pop64(cur[v][w]);
    return (long long)V * V - total;
}

/* Swap partners: A-vertex a1 loses b1 and a2 loses b2; gains b2 and b1.
   Calling it again with the same slots undoes it. */
static void do_swap(int a1, int k1, int a2, int k2) {
    int b1 = adjA[a1][k1], b2 = adjA[a2][k2];
    int j1 = -1, j2 = -1;
    for (int k = 0; k < d_; k++) if (adjB[b1][k] == a1) { j1 = k; break; }
    for (int k = 0; k < d_; k++) if (adjB[b2][k] == a2) { j2 = k; break; }
    adjA[a1][k1] = b2;
    adjA[a2][k2] = b1;
    adjB[b1][j1] = a2;
    adjB[b2][j2] = a1;
    ex[a1][b1] = 0; ex[a2][b2] = 0;
    ex[a1][b2] = 1; ex[a2][b1] = 1;
}

static int propose(int *a1, int *k1, int *a2, int *k2) {
    int x = rnd_int(N), y = rnd_int(N);
    if (x == y) return 0;
    int kx = rnd_int(d_), ky = rnd_int(d_);
    int b1 = adjA[x][kx], b2 = adjA[y][ky];
    if (b1 == b2) return 0;
    if (ex[x][b2] || ex[y][b1]) return 0;
    *a1 = x; *k1 = kx; *a2 = y; *k2 = ky;
    return 1;
}

/* Add one A vertex (index N) and one B vertex (index N). Needs d distinct
   A vertices with distinct B neighbours. Returns 0 on failure. */
static int grow(void) {
    int x = N, y = N;
    if (x + 1 >= MAXN) return 0;
    int as[MAXD], ks[MAXD], bs[MAXD], cnt = 0;
    long tries = 0;
    while (cnt < d_ && tries < 200000) {
        tries++;
        int a = rnd_int(N), k = rnd_int(d_), b = adjA[a][k];
        int bad = 0;
        for (int i = 0; i < cnt; i++)
            if (as[i] == a || bs[i] == b) { bad = 1; break; }
        if (bad) continue;
        as[cnt] = a; ks[cnt] = k; bs[cnt] = b; cnt++;
    }
    if (cnt < d_) return 0;
    for (int i = 0; i < d_; i++) {
        int a = as[i], k = ks[i], b = bs[i];
        ex[a][b] = 0;
        adjA[a][k] = y;
        for (int j = 0; j < d_; j++)
            if (adjB[b][j] == a) { adjB[b][j] = x; break; }
        adjA[x][i] = b; ex[x][b] = 1;
        adjB[y][i] = a; ex[a][y] = 1;
    }
    N++;
    return 1;
}

static void snapshot(void) {
    snapN = N;
    memcpy(snapAdj, adjA, sizeof(adjA));
}

static void print_snapshot(void) {
    int n = 2 * snapN, m = snapN * d_;
    printf("%d %d\n", n, m);
    for (int a = 0; a < snapN; a++)
        for (int k = 0; k < d_; k++)
            printf("%d %d\n", a, snapN + snapAdj[a][k]);
}

static void fallback(void) {
    memset(ex, 0, sizeof(ex));
    N = d_;
    for (int a = 0; a < N; a++)
        for (int k = 0; k < d_; k++) {
            adjA[a][k] = k;
            adjB[a][k] = k;
            ex[a][k] = 1;
        }
}

/* Loads a d-regular bipartite graph from stdin. Returns 0 if it is not one. */
static int load_input(int n, int m) {
    if (n <= 0 || n > 2 * MAXN || m <= 0) return 0;
    int *eu = malloc(sizeof(int) * (size_t)m);
    int *ev = malloc(sizeof(int) * (size_t)m);
    int *deg = calloc((size_t)n, sizeof(int));
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) return 0;
        if (eu[i] < 0 || eu[i] >= n || ev[i] < 0 || ev[i] >= n || eu[i] == ev[i]) return 0;
        deg[eu[i]]++;
        deg[ev[i]]++;
    }
    for (int v = 0; v < n; v++) if (deg[v] != d_) return 0;
    int *off = malloc(sizeof(int) * (size_t)(n + 1));
    int *pos = malloc(sizeof(int) * (size_t)n);
    int *to = malloc(sizeof(int) * (size_t)(2 * m));
    off[0] = 0;
    for (int v = 0; v < n; v++) { off[v + 1] = off[v] + deg[v]; pos[v] = off[v]; }
    for (int i = 0; i < m; i++) {
        to[pos[eu[i]]++] = ev[i];
        to[pos[ev[i]]++] = eu[i];
    }
    int *col = malloc(sizeof(int) * (size_t)n);
    int *q = malloc(sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int u = q[qh++];
            for (int e = off[u]; e < off[u + 1]; e++) {
                int w = to[e];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    q[qt++] = w;
                } else if (col[w] == col[u]) {
                    return 0;
                }
            }
        }
    }
    int *idx = malloc(sizeof(int) * (size_t)n);
    int na = 0, nb = 0;
    for (int v = 0; v < n; v++) {
        if (col[v] == 0) idx[v] = na++;
        else idx[v] = nb++;
    }
    if (na != nb || na < 1 || na > MAXN) return 0;
    memset(ex, 0, sizeof(ex));
    N = na;
    int *fa = calloc((size_t)N, sizeof(int));
    int *fb = calloc((size_t)N, sizeof(int));
    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        int a = (col[u] == 0) ? u : v;
        int b = (col[u] == 0) ? v : u;
        int ai = idx[a], bi = idx[b];
        if (ex[ai][bi]) return 0;
        ex[ai][bi] = 1;
        if (fa[ai] >= d_ || fb[bi] >= d_) return 0;
        adjA[ai][fa[ai]++] = bi;
        adjB[bi][fb[bi]++] = ai;
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    if (d_ < 1 || d_ > MAXD || D_ < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 777ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int nin = 0, min_ = 0;
    int ok = 0;
    if (scanf("%d %d", &nin, &min_) == 2 && nin > 0 && min_ > 0)
        ok = load_input(nin, min_);
    if (!ok) fallback();

    long long cost = eval_cost();
    long long iter = 0;
    static const double TS[3] = {0.5, 1.0, 2.0};
    double tmpT = 1.0;

    while (1) {
        if ((iter & 15) == 0 && elapsed() > DEADLINE) break;
        iter++;
        if (cost == 0) {
            snapshot();
            if (!grow()) break;
            cost = eval_cost();
            continue;
        }
        if (iter % 20000 == 0) tmpT = TS[rnd_int(3)];
        int a1, k1, a2, k2;
        if (!propose(&a1, &k1, &a2, &k2)) continue;
        do_swap(a1, k1, a2, k2);
        long long nc = eval_cost();
        long long dl = nc - cost;
        if (dl <= 0 || rnd_unit() < exp(-(double)dl / tmpT)) {
            cost = nc;
        } else {
            do_swap(a1, k1, a2, k2);
        }
    }

    if (cost == 0 && N > snapN) snapshot();
    if (snapN > 0) print_snapshot();
    else printf("0 0\n");
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
# Driver: baselines, then Stage A (group lifts), then Stage B (unstructured
# growth from the best graph so far). Every stage is optional; the best valid
# graph seen so far is always returned.
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

    if best_n >= lib.moore_bound(d, D):
        return best

    # Stage A: group-lift annealer, a bounded share of the budget.
    remaining = 0.92 * time_limit - left() - 2.0
    if remaining >= 2.0:
        budget_a = 0.4 * remaining
        try:
            out = lib.run_c(GROUP_C, [d, D, seed, f"{budget_a:.2f}", best_n],
                            timeout=budget_a + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Stage B: unstructured growth from the best valid graph so far.
    remB = 0.92 * time_limit - left() - 2.0
    if remB >= 2.0:
        try:
            out = lib.run_c(GROW_C, [d, D, seed, f"{remB:.2f}"],
                            stdin_graph=best, timeout=remB + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
