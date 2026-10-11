import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 (C_LIFT): voltage lifts of semidirect products Z_m x| Z_k2 over a base
# of K A-vertices and K B-vertices, searched by simulated annealing with breakout
# weights and an elite pool (iterated local search). Unchanged from the parent.
#
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart t = (i, j, s) joins
# A_i,g to B_j,g*s for all g. Each layer is a permutation, so every vertex has
# degree DEG. Diameter <= D iff BFS of depth D from each block representative
# covers all vertices.
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
# Stage 2 (C_GRAPH): graph-level search, a different construction from the lifts.
#
# Input: a d-regular bipartite graph (the best lift found so far) on stdin.
# Growth step: pick d "slots" (edges) with pairwise distinct endpoints, reroute
# them through two NEW vertices (new A vertex joined to the d freed B endpoints,
# new B vertex joined to the d freed A endpoints). This keeps the graph exactly
# d-regular and bipartite on n+2 vertices, but the diameter is generally broken.
# Simulated annealing on double-edge swaps (which preserve degrees and the
# bipartition) then minimises the number of vertex pairs at distance > D.
# On success the graph is saved and grown again while time remains.
#
# Slot model: each edge slot e has a fixed A endpoint eA[e] and a B endpoint
# eB[e]. A double-edge swap of slots e1, e2 exchanges their B endpoints.
# Output: the last zero-cost graph found (valid by construction), else "0 0".
# ----------------------------------------------------------------------------

C_GRAPH = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

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

static int DEG, DIAM;
static int N, NE, W;
static int *eA, *eB;          /* slot e joins A-vertex eA[e] and B-vertex eB[e] */
static int *pB;               /* best B endpoints in the current anneal */
static int *bA, *bB;          /* best valid graph saved so far */
static int bestN = 0, bestNE = 0;
static unsigned char *adjm;   /* N*N adjacency matrix */
static int *nb;               /* N*DEG neighbour lists */
static uint64_t *R1, *R2;     /* N*W bitsets */

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void alloc_struct(void) {
    W = (N + 63) / 64;
    adjm = calloc((size_t)N * N, 1);
    nb = malloc(sizeof(int) * (size_t)N * DEG);
    R1 = malloc(sizeof(uint64_t) * (size_t)N * W);
    R2 = malloc(sizeof(uint64_t) * (size_t)N * W);
}

static void free_struct(void) {
    free(adjm); free(nb); free(R1); free(R2);
    adjm = NULL; nb = NULL; R1 = NULL; R2 = NULL;
}

/* Fill adjm and nb from an undirected edge list. Returns 1 iff every vertex has exactly DEG neighbours. */
static int build_struct(const int *ea, const int *eb, int m) {
    int *cntv = calloc((size_t)N, sizeof(int));
    memset(adjm, 0, (size_t)N * N);
    int ok = 1;
    for (int e = 0; e < m; e++) {
        int a = ea[e], b = eb[e];
        if (cntv[a] >= DEG || cntv[b] >= DEG) { ok = 0; break; }
        nb[(size_t)a * DEG + cntv[a]++] = b;
        nb[(size_t)b * DEG + cntv[b]++] = a;
        adjm[(size_t)a * N + b] = 1;
        adjm[(size_t)b * N + a] = 1;
    }
    if (ok)
        for (int v = 0; v < N; v++)
            if (cntv[v] != DEG) { ok = 0; break; }
    free(cntv);
    return ok;
}

/* Number of unordered vertex pairs at distance > DIAM. */
static long long eval_cost(void) {
    size_t tot = (size_t)N * W;
    memset(R1, 0, sizeof(uint64_t) * tot);
    for (int v = 0; v < N; v++) R1[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = R2 + (size_t)v * W;
            memcpy(dst, R1 + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            const int *p = nb + (size_t)v * DEG;
            for (int k = 0; k < DEG; k++) {
                const uint64_t *src = R1 + (size_t)p[k] * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t *t = R1; R1 = R2; R2 = t;
    }
    long long miss = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *src = R1 + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(src[w]);
        miss += N - c;
    }
    return miss / 2;
}

static void nb_replace(int v, int old, int nw) {
    int *p = nb + (size_t)v * DEG;
    for (int k = 0; k < DEG; k++)
        if (p[k] == old) { p[k] = nw; return; }
}

static void set_adj(int a, int b, int val) {
    adjm[(size_t)a * N + b] = (unsigned char)val;
    adjm[(size_t)b * N + a] = (unsigned char)val;
}

/* Exchange the B endpoints of slots e1 and e2. Applying it twice restores the state. */
static void apply_swap(int e1, int e2) {
    int x1 = eA[e1], y1 = eB[e1], x2 = eA[e2], y2 = eB[e2];
    set_adj(x1, y1, 0);
    set_adj(x2, y2, 0);
    set_adj(x1, y2, 1);
    set_adj(x2, y1, 1);
    nb_replace(x1, y1, y2);
    nb_replace(y1, x1, x2);
    nb_replace(x2, y2, y1);
    nb_replace(y2, x2, x1);
    eB[e1] = y2;
    eB[e2] = y1;
}

static int swap_ok(int e1, int e2) {
    int x1 = eA[e1], y1 = eB[e1], x2 = eA[e2], y2 = eB[e2];
    if (x1 == x2 || y1 == y2) return 0;
    if (adjm[(size_t)x1 * N + y2] || adjm[(size_t)x2 * N + y1]) return 0;
    return 1;
}

/* Simulated annealing on the slot swaps until cost 0 (returns 1) or the deadline (returns 0). */
static int anneal_zero(void) {
    const long long PH = 3000;
    const double Thi = 4.0, Tlo = 0.2;
    long long cur = eval_cost();
    long long pbest = cur;
    memcpy(pB, eB, sizeof(int) * (size_t)NE);
    if (cur == 0) return 1;
    long long it = 0;
    while (1) {
        if ((it & 15) == 0 && elapsed() > DEADLINE) return 0;
        if (it > 0 && it % PH == 0) {
            /* Restart the phase from the best state found so far. */
            memcpy(eB, pB, sizeof(int) * (size_t)NE);
            build_struct(eA, eB, NE);
            cur = pbest;
        }
        double frac = (double)(it % PH) / (double)PH;
        double temp = Thi * pow(Tlo / Thi, frac);
        it++;
        int e1 = rnd_int(NE), e2 = rnd_int(NE);
        if (e1 == e2 || !swap_ok(e1, e2)) continue;
        apply_swap(e1, e2);
        long long c2 = eval_cost();
        if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / temp)) {
            cur = c2;
            if (cur < pbest) {
                pbest = cur;
                memcpy(pB, eB, sizeof(int) * (size_t)NE);
                if (pbest == 0) return 1;
            }
        } else {
            apply_swap(e1, e2);
        }
    }
}

/* Add two vertices (new A = N, new B = N+1), keeping the graph DEG-regular and bipartite. */
static int grow(void) {
    int E = NE, d = DEG;
    int *sel = malloc(sizeof(int) * (size_t)d);
    unsigned char *ua = calloc((size_t)N, 1), *ub = calloc((size_t)N, 1);
    int cnt = 0;
    for (long tries = 0; cnt < d && tries < 2000000; tries++) {
        int s = rnd_int(E);
        int a = eA[s], b = eB[s];
        if (ua[a] || ub[b]) continue;
        ua[a] = 1;
        ub[b] = 1;
        sel[cnt++] = s;
    }
    free(ua);
    free(ub);
    if (cnt < d) { free(sel); return 0; }
    int newE = E + d;
    eA = realloc(eA, sizeof(int) * (size_t)newE);
    eB = realloc(eB, sizeof(int) * (size_t)newE);
    pB = realloc(pB, sizeof(int) * (size_t)newE);
    for (int i = 0; i < d; i++) {
        int s = sel[i];
        int fb = eB[s];          /* freed B endpoint; the freed A endpoint eA[s] is kept */
        eB[s] = N + 1;           /* slot s: (freed A, new B) */
        eA[E + i] = N;           /* new slot: (new A, freed B) */
        eB[E + i] = fb;
    }
    free(sel);
    free_struct();
    N += 2;
    NE = newE;
    alloc_struct();
    return build_struct(eA, eB, NE);
}

static void save_best(void) {
    free(bA);
    free(bB);
    bA = malloc(sizeof(int) * (size_t)NE);
    bB = malloc(sizeof(int) * (size_t)NE);
    memcpy(bA, eA, sizeof(int) * (size_t)NE);
    memcpy(bB, eB, sizeof(int) * (size_t)NE);
    bestN = N;
    bestNE = NE;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit   (graph on stdin)\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int n = 0, m = 0;
    if (DEG < 1 || DIAM < 1 || scanf("%d %d", &n, &m) != 2 || n < 2 || m < 1) {
        printf("0 0\n");
        return 0;
    }
    int *su = malloc(sizeof(int) * (size_t)m);
    int *sv = malloc(sizeof(int) * (size_t)m);
    for (int e = 0; e < m; e++) {
        if (scanf("%d %d", &su[e], &sv[e]) != 2 || su[e] < 0 || su[e] >= n ||
            sv[e] < 0 || sv[e] >= n || su[e] == sv[e]) {
            printf("0 0\n");
            return 0;
        }
    }
    N = n;
    NE = m;
    alloc_struct();
    int ok = build_struct(su, sv, m);

    /* 2-colour by BFS: colour 0 = A side, colour 1 = B side. */
    int *col = malloc(sizeof(int) * (size_t)N);
    int *q = malloc(sizeof(int) * (size_t)N);
    for (int v = 0; v < N; v++) col[v] = -1;
    if (ok) {
        int qh = 0, qt = 0;
        col[0] = 0;
        q[qt++] = 0;
        while (qh < qt) {
            int v = q[qh++];
            for (int k = 0; k < DEG; k++) {
                int u = nb[(size_t)v * DEG + k];
                if (col[u] < 0) {
                    col[u] = 1 - col[v];
                    q[qt++] = u;
                }
            }
        }
    }
    for (int v = 0; v < N; v++) if (col[v] < 0) ok = 0;
    for (int e = 0; e < m && ok; e++) if (col[su[e]] == col[sv[e]]) ok = 0;
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    eA = malloc(sizeof(int) * (size_t)(m + DEG));
    eB = malloc(sizeof(int) * (size_t)(m + DEG));
    pB = malloc(sizeof(int) * (size_t)(m + DEG));
    for (int e = 0; e < m; e++) {
        if (col[su[e]] == 0) { eA[e] = su[e]; eB[e] = sv[e]; }
        else                 { eA[e] = sv[e]; eB[e] = su[e]; }
    }
    if (!build_struct(eA, eB, NE)) {
        printf("0 0\n");
        return 0;
    }

    while (elapsed() < DEADLINE) {
        if (!anneal_zero()) break;
        save_best();
        if (elapsed() >= DEADLINE) break;
        if (!grow()) break;
    }

    if (bestN > 0 && bA != NULL) {
        printf("%d %d\n", bestN, bestNE);
        for (int e = 0; e < bestNE; e++) printf("%d %d\n", bA[e], bB[e]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue and constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _is_regular(n, edges, d):
    """True if every vertex has degree exactly d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Already at the Moore bound: nothing larger is possible.
    if best[0] >= lib.moore_bound(d, D):
        return best

    def left():
        return 0.92 * time_limit - 1.5 - (time.monotonic() - start)

    # Stage 1: voltage-lift search (parent engine), about 55% of the remaining budget.
    r = left()
    if r >= 2.0:
        b1 = 0.55 * r
        try:
            out = lib.run_c(C_LIFT, [d, D, seed, f"{b1:.2f}", best[0]], timeout=b1 + 5.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    # Stage 2: graph-level growth from the best regular graph, using the rest of the budget.
    r = left()
    if r >= 2.0 and _is_regular(best[0], best[1], d):
        try:
            out = lib.run_c(C_GRAPH, [d, D, seed + 1, f"{r:.2f}"], stdin_graph=best,
                            timeout=r + 5.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
