import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Engine 1 (lift search): voltage lifts of semidirect products Z_m x| Z_k2 over a
# base of K A-vertices and K B-vertices, searched by simulated annealing with
# breakout weights and an elite pool (iterated local search).
#
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart t = (i, j, s) joins
# A_i,g to B_j,g*s for all g. Each layer is a permutation, so every vertex
# has degree DEG. Left multiplication is an automorphism, so diameter <= D
# iff BFS of depth D from each of the 2K block representatives covers all.
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
# Engine 2 (bold, different family): unstructured bipartite repair-and-grow.
#
# The graph is an arbitrary bipartite graph with max degree DEG, not a lift.
# Cost = number of unordered vertex pairs at distance > DIAM (bit-parallel BFS).
# Moves: double-edge swap, relocating one edge endpoint to a deficient vertex
# on the same side, adding an edge between deficient vertices, and removing an
# edge. Annealing accepts by the usual Metropolis rule with reheating cycles
# and restarts from the best state. Whenever cost reaches 0 the graph is
# recorded and two isolated vertices (one per side) are added, so the engine
# keeps searching for a valid graph with more vertices. The last recorded valid
# graph is printed.
# ----------------------------------------------------------------------------

REPAIR_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXW 32
#define MAXDEG 32
#define CYC 3000

static int N, DEG, DIAM, MAXNV;
static unsigned char side[MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXDEG];
static unsigned char adj[MAXN][MAXN];

static int best_deg[MAXN];
static int best_nb[MAXN][MAXDEG];
static long long best_cost;

static int have_out, out_N, out_m;
static int out_eu[MAXN * MAXDEG], out_ev[MAXN * MAXDEG];

static uint64_t bufA[MAXN * MAXW], bufB[MAXN * MAXW];
static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

static uint64_t rnext(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rint_(int n) { return (int)(rnext() % (uint64_t)n); }
static double runit(void) { return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static void raw_add(int a, int b) {
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
    adj[a][b] = 1;
    adj[b][a] = 1;
}

static void raw_rem(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (nb[a][k] == b) { nb[a][k] = nb[a][--deg[a]]; break; }
    for (int k = 0; k < deg[b]; k++)
        if (nb[b][k] == a) { nb[b][k] = nb[b][--deg[b]]; break; }
    adj[a][b] = 0;
    adj[b][a] = 0;
}

static int nlog;
static int lt[8], la[8], lb[8];

static void do_add(int a, int b) {
    raw_add(a, b);
    lt[nlog] = 1; la[nlog] = a; lb[nlog] = b; nlog++;
}

static void do_rem(int a, int b) {
    raw_rem(a, b);
    lt[nlog] = 0; la[nlog] = a; lb[nlog] = b; nlog++;
}

static void undo(void) {
    while (nlog > 0) {
        nlog--;
        if (lt[nlog]) raw_rem(la[nlog], lb[nlog]);
        else raw_add(la[nlog], lb[nlog]);
    }
}

/* Number of unordered pairs at distance > DIAM. */
static long long eval_bad(void) {
    int W = (N + 63) / 64;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < DIAM; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(uint64_t) * W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *s = cur + (size_t)nb[v][k] * W;
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
            for (int w = 0; w < W; w++)
                if (o[w] != c[w]) { changed = 1; break; }
        }
        if (!changed) break;
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long cov = 0;
    for (size_t i = 0; i < (size_t)N * W; i++) cov += __builtin_popcountll(cur[i]);
    return ((long long)N * N - cov) / 2;
}

static void snapshot(void) {
    for (int v = 0; v < N; v++) {
        best_deg[v] = deg[v];
        memcpy(best_nb[v], nb[v], sizeof(nb[v]));
    }
}

static void restore_best(void) {
    for (int v = 0; v < N; v++) {
        deg[v] = best_deg[v];
        memcpy(nb[v], best_nb[v], sizeof(nb[v]));
        memset(adj[v], 0, (size_t)N);
    }
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++) adj[v][nb[v][k]] = 1;
}

static void record_out(void) {
    out_N = N;
    out_m = 0;
    for (int v = 0; v < N; v++) {
        if (side[v] != 0) continue;
        for (int k = 0; k < deg[v]; k++) {
            if (out_m < MAXN * MAXDEG) {
                out_eu[out_m] = v;
                out_ev[out_m] = nb[v][k];
                out_m++;
            }
        }
    }
    have_out = 1;
}

static void grow(void) {
    int a = N, b = N + 1;
    side[a] = 0;
    side[b] = 1;
    deg[a] = 0;
    deg[b] = 0;
    for (int v = 0; v < N + 2; v++) {
        adj[a][v] = 0; adj[v][a] = 0;
        adj[b][v] = 0; adj[v][b] = 0;
    }
    N += 2;
}

/* Random edge (a on side 0, b on side 1). */
static int pick_edge(int *pa, int *pb) {
    int a = -1;
    for (int t = 0; t < 64 && a < 0; t++) {
        int v = rint_(N);
        if (side[v] == 0 && deg[v] > 0) a = v;
    }
    if (a < 0) {
        int cnt = 0;
        for (int v = 0; v < N; v++)
            if (side[v] == 0 && deg[v] > 0) {
                cnt++;
                if (rint_(cnt) == 0) a = v;
            }
    }
    if (a < 0) return 0;
    *pa = a;
    *pb = nb[a][rint_(deg[a])];
    return 1;
}

/* Uniformly random vertex on side s with spare degree, or -1. */
static int pick_def(int s) {
    int cnt = 0, ch = -1;
    for (int v = 0; v < N; v++)
        if (side[v] == s && deg[v] < DEG) {
            cnt++;
            if (rint_(cnt) == 0) ch = v;
        }
    return ch;
}

/* Apply one random move (logged). Returns 0 if nothing was applied. */
static int random_move(void) {
    nlog = 0;
    double r = runit();
    int a, b, a2, b2;
    if (r < 0.35) {
        if (!pick_edge(&a, &b)) return 0;
        if (!pick_edge(&a2, &b2)) return 0;
        if (a == a2 || b == b2) return 0;
        if (adj[a][b2] || adj[a2][b]) return 0;
        do_rem(a, b);
        do_rem(a2, b2);
        do_add(a, b2);
        do_add(a2, b);
        return 1;
    } else if (r < 0.6) {
        if (!pick_edge(&a, &b)) return 0;
        int x = pick_def(0);
        if (x < 0 || x == a || adj[x][b]) return 0;
        do_rem(a, b);
        do_add(x, b);
        return 1;
    } else if (r < 0.85) {
        if (!pick_edge(&a, &b)) return 0;
        int y = pick_def(1);
        if (y < 0 || y == b || adj[a][y]) return 0;
        do_rem(a, b);
        do_add(a, y);
        return 1;
    } else if (r < 0.97) {
        int x = pick_def(0), y = pick_def(1);
        if (x < 0 || y < 0 || adj[x][y]) return 0;
        do_add(x, y);
        return 1;
    } else {
        if (!pick_edge(&a, &b)) return 0;
        do_rem(a, b);
        return 1;
    }
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed time_limit max_n\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    MAXNV = atoi(argv[5]);
    if (MAXNV > MAXN) MAXNV = MAXN;
    rs[0] = sd * 2654435761ULL + 12345ULL;
    rs[1] = (sd + 7) * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n <= 0 || n > MAXN) {
        N = 2;
        side[0] = 0;
        side[1] = 1;
        raw_add(0, 1);
    } else {
        N = n;
        for (int i = 0; i < m; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) break;
            if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
            if (adj[u][v]) continue;
            if (deg[u] >= DEG || deg[v] >= DEG) continue;
            raw_add(u, v);
        }
        static int col[MAXN], queue[MAXN];
        for (int v = 0; v < N; v++) col[v] = -1;
        for (int s = 0; s < N; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int qh = 0, qt = 0;
            queue[qt++] = s;
            while (qh < qt) {
                int u = queue[qh++];
                for (int k = 0; k < deg[u]; k++) {
                    int w = nb[u][k];
                    if (col[w] < 0) {
                        col[w] = 1 - col[u];
                        queue[qt++] = w;
                    }
                }
            }
        }
        for (int v = 0; v < N; v++) {
            side[v] = (unsigned char)col[v];
            for (int k = 0; k < deg[v]; k++)
                if (side[nb[v][k]] == side[v]) { printf("0 0\n"); return 0; }
        }
    }
    if (N + 2 > MAXNV && N > MAXNV) { printf("0 0\n"); return 0; }

    long long cost = eval_bad();
    best_cost = cost;
    snapshot();
    if (cost == 0) record_out();

    long long it = 0;
    for (;;) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        it++;
        if (cost == 0) {
            if (N + 2 > MAXNV) break;
            grow();
            cost = eval_bad();
            best_cost = cost;
            snapshot();
            continue;
        }
        int phase = (int)(it % CYC);
        if (phase == 0 && cost > best_cost && runit() < 0.5) {
            restore_best();
            cost = best_cost;
        }
        double f = 1.0 - (double)phase / CYC;
        double temp = 0.05 + 2.0 * f * f;
        if (!random_move()) continue;
        long long nc = eval_bad();
        long long delta = nc - cost;
        if (delta <= 0 || runit() < exp(-(double)delta / temp)) {
            cost = nc;
            if (cost < best_cost) {
                best_cost = cost;
                snapshot();
            }
            if (cost == 0) record_out();
        } else {
            undo();
        }
    }

    if (have_out) {
        printf("%d %d\n", out_N, out_m);
        for (int i = 0; i < out_m; i++)
            printf("%d %d\n", out_eu[i], out_ev[i]);
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
# Driver: baselines, then lift search (engine 1), then repair-and-grow (engine 2)
# seeded from the best valid graph so far. Every return path is validated.
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

    # Stage 1: lift search gets a share of the budget.
    usable = 0.93 * time_limit - (time.monotonic() - start) - 2.5
    if usable >= 2.0:
        t1 = 0.45 * usable
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{t1:.2f}", best_n],
                            timeout=t1 + 5.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Stage 2: unstructured repair-and-grow from the best graph found so far.
    remaining = 0.93 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0 and d <= 32:
        cap = min(lib.moore_bound(d, D), 2000)
        if best_n < cap:
            try:
                out = lib.run_c(REPAIR_C, [d, D, seed, f"{remaining:.2f}", cap],
                                stdin_graph=best, timeout=remaining + 5.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
