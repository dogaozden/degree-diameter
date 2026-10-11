import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Pipeline (per case):
#   1. Safe Python baselines: K_{d,d}, PG(2,q), W(q).
#   2. C_LIFT (the previous lift annealer): voltage lifts over semidirect
#      products, about 45% of the search budget. Its output is the strong
#      baseline (684 for d=6, D=5 in the parent).
#   3. C_ANNEAL (new, bold): unstructured annealing over degree-preserving
#      double-edge swaps of a bipartite d-regular graph. The cost is the number
#      of ordered vertex pairs farther apart than D, computed with bitset
#      ball expansion. Whenever the cost reaches 0, the graph is valid, so the
#      engine GROWS it by one vertex per side (d edges are rerouted through the
#      two new vertices) and keeps annealing. It starts from the lift output
#      when that is regular, otherwise from a circulant Haar-type graph.
# Each stage only replaces the current best when its output is valid and
# larger, and the final graph is re-checked with lib.is_valid.
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


C_ANNEAL = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MS 1200
#define MAXV (2 * MS)
#define MAXW ((MAXV + 63) / 64)
#define MAXDEG 16
#define EPOCH 15000
#define PERTURB_DIV 20

/* Bipartite d-regular graph on sides A (0..N-1) and B (0..N-1); vertex ids A: i, B: N + j.
   Edge e joins A index ea[e] to B index eb[e]. Mx[a*MS+b] = 1 iff the edge exists. */
static int DEG, DIAM, N, E, NV, W;
static int ea[MS * MAXDEG], eb[MS * MAXDEG];
static int epa[MS * MAXDEG], epb[MS * MAXDEG];
static int bea[MS * MAXDEG], beb[MS * MAXDEG];
static int bestN = 0, bestE = 0;
static unsigned char Mx[MS * MS];
static int adjv[MAXV * MAXDEG];
static int cnt[MAXV];
static uint64_t R1[MAXV * MAXW], R2[MAXV * MAXW];
static int sA[MS], sB[MS];
static int gstamp = 0;
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

static void rebuild_mx(void) {
    for (int a = 0; a < N; a++) memset(Mx + a * MS, 0, (size_t)N);
    for (int e = 0; e < E; e++) Mx[ea[e] * MS + eb[e]] = 1;
}

/* Bad ordered pairs: pairs (v,u) with distance > DIAM. Zero iff the graph is valid. */
static long long eval_cost(void) {
    NV = 2 * N;
    W = (NV + 63) / 64;
    for (int v = 0; v < NV; v++) cnt[v] = 0;
    for (int e = 0; e < E; e++) {
        int a = ea[e], b = N + eb[e];
        adjv[a * DEG + cnt[a]++] = b;
        adjv[b * DEG + cnt[b]++] = a;
    }
    memset(R1, 0, sizeof(uint64_t) * (size_t)NV * W);
    for (int v = 0; v < NV; v++) R1[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    uint64_t *cur = R1, *nxt = R2;
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < NV; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(uint64_t) * W);
            for (int k = 0; k < DEG; k++) {
                const uint64_t *u = cur + (size_t)adjv[v * DEG + k] * W;
                for (int w = 0; w < W; w++) o[w] |= u[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < NV; v++) {
        const uint64_t *c = cur + (size_t)v * W;
        int reached = 0;
        for (int w = 0; w < W; w++) reached += popc(c[w]);
        bad += NV - reached;
    }
    return bad;
}

static void init_circulant(int n0) {
    N = n0;
    E = N * DEG;
    int idx = 0;
    for (int s = 0; s < DEG; s++)
        for (int i = 0; i < N; i++) {
            ea[idx] = i;
            eb[idx] = (i + s) % N;
            idx++;
        }
    rebuild_mx();
}

/* Read "n m" and m edges. Accept only a bipartite d-regular simple graph with equal sides. */
static int read_input(void) {
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || m <= 0 || n > MAXV || m > MS * MAXDEG) return 0;
    int *du = malloc(sizeof(int) * (size_t)m);
    int *dv = malloc(sizeof(int) * (size_t)m);
    int *deg = calloc((size_t)n, sizeof(int));
    int *col = malloc(sizeof(int) * (size_t)n);
    int *off = malloc(sizeof(int) * (size_t)(n + 1));
    int *nb = malloc(sizeof(int) * (size_t)(2 * m));
    int *pos = malloc(sizeof(int) * (size_t)n);
    int *idx = malloc(sizeof(int) * (size_t)n);
    int *queue = malloc(sizeof(int) * (size_t)n);
    int ok = 1;
    for (int i = 0; i < m && ok; i++) {
        if (scanf("%d %d", &du[i], &dv[i]) != 2) ok = 0;
        else if (du[i] < 0 || du[i] >= n || dv[i] < 0 || dv[i] >= n || du[i] == dv[i]) ok = 0;
        else { deg[du[i]]++; deg[dv[i]]++; }
    }
    for (int v = 0; ok && v < n; v++)
        if (deg[v] != DEG) ok = 0;
    if (ok) {
        off[0] = 0;
        for (int v = 0; v < n; v++) {
            off[v + 1] = off[v] + deg[v];
            pos[v] = off[v];
        }
        for (int i = 0; i < m; i++) {
            nb[pos[du[i]]++] = dv[i];
            nb[pos[dv[i]]++] = du[i];
        }
        for (int v = 0; v < n; v++) col[v] = -1;
        for (int s = 0; ok && s < n; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int qh = 0, qt = 0;
            queue[qt++] = s;
            while (qh < qt && ok) {
                int u = queue[qh++];
                for (int k = off[u]; k < off[u + 1]; k++) {
                    int w = nb[k];
                    if (col[w] < 0) {
                        col[w] = 1 - col[u];
                        queue[qt++] = w;
                    } else if (col[w] == col[u]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
    }
    if (ok) {
        int c0 = 0, c1 = 0;
        for (int v = 0; v < n; v++) idx[v] = (col[v] == 0) ? c0++ : c1++;
        if (c0 != c1 || c0 > MS) ok = 0;
        if (ok) {
            N = c0;
            E = m;
            for (int a = 0; a < N; a++) memset(Mx + a * MS, 0, (size_t)N);
            for (int i = 0; i < m && ok; i++) {
                int a, b;
                if (col[du[i]] == 0) { a = idx[du[i]]; b = idx[dv[i]]; }
                else { a = idx[dv[i]]; b = idx[du[i]]; }
                if (Mx[a * MS + b]) { ok = 0; break; }
                Mx[a * MS + b] = 1;
                ea[i] = a;
                eb[i] = b;
            }
        }
    }
    free(du); free(dv); free(deg); free(col); free(off);
    free(nb); free(pos); free(idx); free(queue);
    return ok;
}

static void record_valid(void) {
    if (N <= bestN) return;
    bestN = N;
    bestE = E;
    memcpy(bea, ea, sizeof(int) * (size_t)E);
    memcpy(beb, eb, sizeof(int) * (size_t)E);
}

static void save_epoch(void) {
    memcpy(epa, ea, sizeof(int) * (size_t)E);
    memcpy(epb, eb, sizeof(int) * (size_t)E);
}

static void restore_epoch(void) {
    memcpy(ea, epa, sizeof(int) * (size_t)E);
    memcpy(eb, epb, sizeof(int) * (size_t)E);
    rebuild_mx();
}

/* Add one A vertex and one B vertex: remove DEG edges (x_k, y_k) forming a matching,
   reconnect x_k to the new B vertex and the new A vertex to y_k. Degrees stay DEG. */
static int grow(void) {
    if (N + 1 > MS) return 0;
    int ch[MAXDEG], nc = 0;
    gstamp++;
    for (int tr = 0; tr < 4000 && nc < DEG; tr++) {
        int e = rnd_int(E);
        int a = ea[e], b = eb[e];
        if (sA[a] == gstamp || sB[b] == gstamp) continue;
        sA[a] = gstamp;
        sB[b] = gstamp;
        ch[nc++] = e;
    }
    if (nc < DEG) return 0;
    int newN = N + 1;
    for (int k = 0; k < DEG; k++) {
        int e = ch[k];
        int x = ea[e], y = eb[e];
        Mx[x * MS + y] = 0;
        ea[e] = x;
        eb[e] = N;
        Mx[x * MS + N] = 1;
        ea[E + k] = N;
        eb[E + k] = y;
        Mx[N * MS + y] = 1;
    }
    E += DEG;
    N = newN;
    return 1;
}

static void blind_swap(void) {
    for (int tr = 0; tr < 50; tr++) {
        int e1 = rnd_int(E), e2 = rnd_int(E);
        if (e1 == e2) continue;
        int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
        if (a1 == a2 || b1 == b2) continue;
        if (Mx[a1 * MS + b2] || Mx[a2 * MS + b1]) continue;
        Mx[a1 * MS + b1] = 0;
        Mx[a2 * MS + b2] = 0;
        Mx[a1 * MS + b2] = 1;
        Mx[a2 * MS + b1] = 1;
        ea[e1] = a1; eb[e1] = b2;
        ea[e2] = a2; eb[e2] = b1;
        return;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_side]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int start_side = argc > 5 ? atoi(argv[5]) : 0;
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 777ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    if (!read_input()) {
        int n0 = start_side;
        if (n0 < DEG) n0 = DEG;
        if (n0 > MS - 1) n0 = MS - 1;
        init_circulant(n0);
    }

    long long cur = eval_cost();
    long long epbest = cur;
    save_epoch();
    int epit = 0;
    for (;;) {
        if (elapsed() > DEADLINE) break;
        if (cur == 0) {
            record_valid();
            if (!grow()) break;
            cur = eval_cost();
            epbest = cur;
            epit = 0;
            save_epoch();
            continue;
        }
        if (epit >= EPOCH) {
            restore_epoch();
            int P = E / PERTURB_DIV + 1;
            for (int s = 0; s < P; s++) blind_swap();
            cur = eval_cost();
            epbest = cur;
            epit = 0;
            save_epoch();
            continue;
        }
        double frac = (double)epit / EPOCH;
        double temp = 1.5 * (1.0 - frac) + 0.05;
        int e1 = rnd_int(E), e2 = rnd_int(E);
        epit++;
        if (e1 == e2) continue;
        int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
        if (a1 == a2 || b1 == b2) continue;
        if (Mx[a1 * MS + b2] || Mx[a2 * MS + b1]) continue;
        Mx[a1 * MS + b1] = 0;
        Mx[a2 * MS + b2] = 0;
        Mx[a1 * MS + b2] = 1;
        Mx[a2 * MS + b1] = 1;
        ea[e1] = a1; eb[e1] = b2;
        ea[e2] = a2; eb[e2] = b1;
        long long c2 = eval_cost();
        if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / temp)) {
            cur = c2;
            if (cur < epbest) {
                epbest = cur;
                save_epoch();
            }
        } else {
            Mx[a1 * MS + b2] = 0;
            Mx[a2 * MS + b1] = 0;
            Mx[a1 * MS + b1] = 1;
            Mx[a2 * MS + b2] = 1;
            ea[e1] = a1; eb[e1] = b1;
            ea[e2] = a2; eb[e2] = b2;
        }
    }

    if (bestN > 0) {
        printf("%d %d\n", 2 * bestN, bestE);
        for (int e = 0; e < bestE; e++)
            printf("%d %d\n", bea[e], bestN + beb[e]);
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
# Driver.
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

    # Two C runs plus two compiles. Reserve about 4 s for compiles, parsing and validation.
    avail = 0.9 * time_limit - (time.monotonic() - start) - 4.0
    if avail >= 2.0:
        dl1 = 0.45 * avail
        try:
            out = lib.run_c(C_LIFT, [d, D, seed, f"{dl1:.2f}", best_n],
                            timeout=dl1 + 10.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

        dl2 = 0.9 * time_limit - (time.monotonic() - start) - 2.0
        if dl2 >= 1.0:
            try:
                out = lib.run_c(C_ANNEAL, [d, D, seed + 1, f"{dl2:.2f}", max(d, best_n // 2)],
                                stdin_graph=(best_n, best[1]), timeout=dl2 + 10.0)
                consider(*lib.parse_graph_text(out))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
