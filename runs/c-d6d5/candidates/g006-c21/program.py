import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1 (unchanged from the parent): voltage lifts of semidirect products
# Z_m x| Z_k2 over a base of K A-vertices and K B-vertices, searched by
# simulated annealing with an elite pool and iterated local search.
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

static int DEG, DIAM, K, K2, M, G, T, MAXT;
static int R;
static int *Rpow;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int *bestJ, *bestS;
static int curstamp;
static double DEADLINE;
static int best_n, best_m;
static int *best_e = NULL;

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

static long long eval_cost(void) {
    int N = 2 * K * G;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2])
                return BIGC;
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
        total += N - count;
    }
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
    curstamp = 0;
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
}

static void free_config(void) {
    free(dI); free(dJ); free(dS); free(bestJ); free(bestS);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx); free(Rpow);
    dI = dJ = dS = bestJ = bestS = perm = adj = cnt = stamp = fr = nx = Rpow = NULL;
}

static void setup_group(int k, int c2, int m, int r) {
    K = k; K2 = c2; M = m; R = r; G = m * c2;
    alloc_config();
    for (int t = 0; t < T; t++) dI[t] = t % K;
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
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        double temp = tscale * (3.0 * (1.0 - (double)it / iters) + 0.05);
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long long c2 = eval_cost();
            if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
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
            if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
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
# C engine 2 (new, bold): direct annealing on general bipartite graphs.
# Start from a valid graph, add vertex pairs, then anneal over degree-preserving
# edge swaps and "fill" moves (subdivide an edge to attach a deficient pair).
# Cost = number of ordered vertex pairs at distance > D, computed with bitsets.
# Each time cost reaches 0 the graph is saved and two vertices are added.
# ----------------------------------------------------------------------------

C2_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXW 64
#define MAXDEG 16
#define MAXE (MAXN * MAXDEG)
#define LCYC 30000

static int DEG, DIAM, N, M;
static int side[MAXN];
static int dg[MAXN];
static int adj[MAXN * MAXDEG];
static int ea[MAXE], eb[MAXE];
static int sideCnt[2];
static int sideList[2][MAXN];
static int dA[MAXN], dB[MAXN];
static int qbuf[MAXN];
static int bestN, bestM;
static int bestA[MAXE], bestB[MAXE];
static uint64_t bufA[MAXN * MAXW], bufB[MAXN * MAXW];
static uint64_t rs0, rs1;

static uint64_t rnext(void) {
    uint64_t s1 = rs0;
    const uint64_t s0 = rs1;
    rs0 = s0;
    s1 ^= s1 << 23;
    rs1 = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs1 + s0;
}
static int rint_(int n) { return (int)(rnext() % (uint64_t)n); }
static double runit(void) { return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu_now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static void adj_add(int v, int u) { adj[v * DEG + dg[v]] = u; dg[v]++; }

static void adj_del(int v, int u) {
    int *p = adj + v * DEG;
    for (int k = 0; k < dg[v]; k++) {
        if (p[k] == u) { p[k] = p[dg[v] - 1]; dg[v]--; return; }
    }
}

static int is_adj(int v, int u) {
    const int *p = adj + v * DEG;
    for (int k = 0; k < dg[v]; k++) if (p[k] == u) return 1;
    return 0;
}

static void edge_push(int a, int b) {
    ea[M] = a; eb[M] = b; M++;
    adj_add(a, b); adj_add(b, a);
}

static void edge_pop(void) {
    M--;
    int a = ea[M], b = eb[M];
    adj_del(a, b); adj_del(b, a);
}

/* Edges i=(a1,b1), j=(a2,b2) become (a1,b2), (a2,b1). Returns 0 if not allowed. */
static int do_swap(int i, int j) {
    int a1 = ea[i], b1 = eb[i], a2 = ea[j], b2 = eb[j];
    if (a1 == a2 || b1 == b2) return 0;
    if (is_adj(a1, b2) || is_adj(a2, b1)) return 0;
    adj_del(a1, b1); adj_del(b1, a1);
    adj_del(a2, b2); adj_del(b2, a2);
    ea[i] = a1; eb[i] = b2;
    ea[j] = a2; eb[j] = b1;
    adj_add(a1, b2); adj_add(b2, a1);
    adj_add(a2, b1); adj_add(b1, a2);
    return 1;
}

static void undo_swap(int i, int j) {
    int a1 = ea[i], b2 = eb[i], a2 = ea[j], b1 = eb[j];
    adj_del(a1, b2); adj_del(b2, a1);
    adj_del(a2, b1); adj_del(b1, a2);
    ea[i] = a1; eb[i] = b1;
    ea[j] = a2; eb[j] = b2;
    adj_add(a1, b1); adj_add(b1, a1);
    adj_add(a2, b2); adj_add(b2, a2);
}

/* Edge i=(a1,b1) becomes (a,b1), and (a1,b) is appended. Degrees of a, b rise by 1. */
static void do_fill(int i, int a, int b) {
    int a1 = ea[i], b1 = eb[i];
    adj_del(a1, b1); adj_del(b1, a1);
    adj_add(a, b1); adj_add(b1, a);
    adj_add(a1, b); adj_add(b, a1);
    ea[i] = a; eb[i] = b1;
    ea[M] = a1; eb[M] = b; M++;
}

static void undo_fill(int i, int a, int b, int a1, int b1) {
    M--;
    adj_del(a1, b); adj_del(b, a1);
    adj_del(a, b1); adj_del(b1, a);
    adj_add(a1, b1); adj_add(b1, a1);
    ea[i] = a1; eb[i] = b1;
}

static int popc(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

/* Number of ordered pairs (v,u) with dist(v,u) > DIAM. */
static long long eval_cost(void) {
    int W = (N + 63) >> 6;
    uint64_t *cur = bufA, *nxt = bufB;
    for (int v = 0; v < N; v++) {
        uint64_t *r = cur + v * MAXW;
        for (int w = 0; w < W; w++) r[w] = 0;
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int lv = 0; lv < DIAM; lv++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + v * MAXW;
            const uint64_t *rv = cur + v * MAXW;
            for (int w = 0; w < W; w++) o[w] = rv[w];
            const int *p = adj + v * DEG;
            for (int k = 0; k < dg[v]; k++) {
                const uint64_t *ru = cur + p[k] * MAXW;
                for (int w = 0; w < W; w++) o[w] |= ru[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long c = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *r = cur + v * MAXW;
        int cn = 0;
        for (int w = 0; w < W; w++) cn += popc(r[w]);
        c += N - cn;
    }
    return c;
}

static int bfs_sides(void) {
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        qbuf[t++] = s;
        while (h < t) {
            int u = qbuf[h++];
            for (int k = 0; k < dg[u]; k++) {
                int w = adj[u * DEG + k];
                if (side[w] < 0) {
                    side[w] = 1 - side[u];
                    qbuf[t++] = w;
                } else if (side[w] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void grow(void) {
    int a = N, b = N + 1;
    dg[a] = 0; dg[b] = 0;
    side[a] = 0; side[b] = 1;
    sideList[0][sideCnt[0]++] = a;
    sideList[1][sideCnt[1]++] = b;
    N += 2;
}

static void save_best(void) {
    bestN = N;
    bestM = M;
    memcpy(bestA, ea, sizeof(int) * (size_t)M);
    memcpy(bestB, eb, sizeof(int) * (size_t)M);
}

static int accept(long long delta, double temp) {
    if (delta <= 0) return 1;
    return runit() < exp(-(double)delta / temp);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    double deadline = atof(argv[4]);
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    rs0 = 0x9E3779B97F4A7C15ULL ^ (sd * 0xD1B54A32D192ED03ULL + 7ULL);
    rs1 = 0xBF58476D1CE4E5B9ULL + sd * 0x94D049BB133111EBULL + 1ULL;
    for (int i = 0; i < 20; i++) rnext();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    N = 0; M = 0;
    if (n0 > 0) {
        if (n0 > MAXN - 64 || m0 < 0 || m0 > MAXE) {
            printf("0 0\n");
            return 0;
        }
        N = n0;
        for (int i = 0; i < m0; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) break;
            if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
            if (dg[u] >= DEG || dg[v] >= DEG) continue;
            ea[M] = u; eb[M] = v; M++;
            adj_add(u, v); adj_add(v, u);
        }
        if (!bfs_sides()) {
            printf("0 0\n");
            return 0;
        }
        for (int i = 0; i < M; i++)
            if (side[ea[i]] == 1) { int t = ea[i]; ea[i] = eb[i]; eb[i] = t; }
    } else {
        /* No start graph: complete bipartite K_{DEG,DEG}. */
        N = 2 * DEG;
        for (int v = 0; v < N; v++) side[v] = (v < DEG) ? 0 : 1;
        for (int a = 0; a < DEG; a++)
            for (int b = 0; b < DEG; b++)
                edge_push(a, DEG + b);
    }

    sideCnt[0] = sideCnt[1] = 0;
    for (int v = 0; v < N; v++) sideList[side[v]][sideCnt[side[v]]++] = v;

    bestN = 0; bestM = 0;
    if (sideCnt[0] == 0 || sideCnt[1] == 0) {
        printf("0 0\n");
        return 0;
    }

    long long cost = eval_cost();
    if (cost == 0) save_best();

    const double T0 = 3.0, T1 = 0.25;
    long long it = 0;
    while (1) {
        if ((it & 127) == 0 && cpu_now() > deadline) break;
        it++;
        if (cost == 0) {
            save_best();
            if (N + 2 > MAXN) break;
            grow();
            cost = eval_cost();
            continue;
        }

        double temp = T0 * pow(T1 / T0, (double)(it % LCYC) / (double)LCYC);

        int nA = 0, nB = 0;
        for (int k = 0; k < sideCnt[0]; k++) {
            int v = sideList[0][k];
            if (dg[v] < DEG) dA[nA++] = v;
        }
        for (int k = 0; k < sideCnt[1]; k++) {
            int v = sideList[1][k];
            if (dg[v] < DEG) dB[nB++] = v;
        }

        int done = 0;
        if (nA > 0 && nB > 0 && rint_(2) == 0) {
            int a = dA[rint_(nA)], b = dB[rint_(nB)];
            if (!is_adj(a, b) && M < MAXE) {
                edge_push(a, b);
                long long c2 = eval_cost();
                if (accept(c2 - cost, temp)) cost = c2;
                else edge_pop();
                done = 1;
            } else if (M > 0) {
                int i = rint_(M);
                int a1 = ea[i], b1 = eb[i];
                if (M < MAXE && a != a1 && b != b1 && !is_adj(a, b1) && !is_adj(a1, b)) {
                    do_fill(i, a, b);
                    long long c2 = eval_cost();
                    if (accept(c2 - cost, temp)) cost = c2;
                    else undo_fill(i, a, b, a1, b1);
                    done = 1;
                }
            }
        }
        if (!done && M >= 2) {
            int i = rint_(M), j = rint_(M);
            if (i != j && do_swap(i, j)) {
                long long c2 = eval_cost();
                if (accept(c2 - cost, temp)) cost = c2;
                else undo_swap(i, j);
            }
        }
    }

    if (bestM == 0 && bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++)
        printf("%d %d\n", bestA[i], bestB[i]);
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
# Driver: baselines, then group-lift search (engine 1), then direct graph
# annealing from the best valid graph found so far (engine 2).
# ----------------------------------------------------------------------------

def _run_engine2(d, D, seed, budget, start):
    """Run the direct annealer from a valid start graph; return (n, edges)."""
    n, e = start
    out = lib.run_c(C2_SOURCE, [d, D, seed, f"{budget:.2f}"],
                    stdin_graph=(n, e), timeout=budget + 8.0)
    return lib.parse_graph_text(out)


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

    usable = 0.85 * time_limit - (time.monotonic() - start) - 1.0
    if usable < 1.0:
        return best

    use_direct = d <= 16 and D >= 2
    b1 = usable * 0.45 if use_direct else usable
    if b1 >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{b1:.2f}", best_n],
                            timeout=b1 + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    remaining = 0.85 * time_limit - (time.monotonic() - start) - 1.0
    if use_direct and remaining >= 2.0 and best_n >= 2:
        try:
            n, e = _run_engine2(d, D, seed + 1, remaining, best)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
