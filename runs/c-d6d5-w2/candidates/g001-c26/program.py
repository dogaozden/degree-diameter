import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine. Two phases share one run.
#
# Phase 1 (first PHASE1 fraction of the budget): voltage lifts of semidirect
# products Z_m x| Z_k2 over a base of K A-vertices and K B-vertices, searched by
# simulated annealing with breakout weights, plus an elite pool (ILS). This is
# the search from the parent program.
#
# Phase 2 (NEW): validity-preserving growth by edge switches. The best valid
# base (lift, optional stdin start graph, or K_{d,d}) is loaded into a
# mutable adjacency structure. Two moves are tried:
#   * augmentation: pick d disjoint edges (a_i, b_i) with a_i on side A and
#     b_i on side B. Delete them and add two new vertices x (side A) and y
#     (side B) with x ~ b_i and y ~ a_i for all i. Degrees are unchanged for
#     old vertices and both new vertices get degree d. The graph grows by 2.
#   * plateau switch: a double-edge swap (a1,b1),(a2,b2) -> (a1,b2),(a2,b1),
#     which keeps every degree and changes the graph's shape.
# A move is kept only if the result still has diameter <= D (BFS from every
# vertex, starting from the newest vertices so failures are found quickly).
# The graph is valid at all times and its order never decreases.
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
#define GCAPMAX 16384
#define PHASE1 0.55

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

/* Breakout state. */
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

/* ------------------------------------------------------------------------
 * Phase 2: mutable graph with validity-preserving growth.
 * Vertices 0..GN-1; gside[v] is 0 (A) or 1 (B); adjacency rows of width DEG.
 * ------------------------------------------------------------------------ */
static int *gadj, *gdeg, *gside, *gstamp, *gq0, *gq1, *gmark;
static int GN = 0, gcur = 0, mcur = 0;

static int g_has(int u, int v) {
    const int *row = gadj + (size_t)u * DEG;
    for (int i = 0; i < gdeg[u]; i++)
        if (row[i] == v) return 1;
    return 0;
}

static void g_del_one(int u, int v) {
    int *row = gadj + (size_t)u * DEG;
    for (int i = 0; i < gdeg[u]; i++)
        if (row[i] == v) {
            row[i] = row[gdeg[u] - 1];
            gdeg[u]--;
            return;
        }
}

static void g_remove(int u, int v) { g_del_one(u, v); g_del_one(v, u); }

static void g_add(int u, int v) {
    gadj[(size_t)u * DEG + gdeg[u]++] = v;
    gadj[(size_t)v * DEG + gdeg[v]++] = u;
}

/* BFS of depth DIAM from every vertex; newest vertices first so that failures
   are found early. Returns 1 iff every vertex reaches all vertices. */
static int g_diam_ok(void) {
    int N = GN;
    for (int k = 0; k < N; k++) {
        int s = (k == 0) ? N - 1 : (k == 1 ? N - 2 : k - 2);
        if (gcur >= 2000000000) {
            memset(gstamp, 0, sizeof(int) * (size_t)GCAPMAX);
            gcur = 0;
        }
        gcur++;
        int head = 0, tail = 0;
        gq0[tail++] = s;
        gstamp[s] = gcur;
        for (int lvl = 0; lvl < DIAM && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int u = gq0[head++];
                const int *row = gadj + (size_t)u * DEG;
                for (int i = 0; i < gdeg[u]; i++) {
                    int v = row[i];
                    if (gstamp[v] != gcur) {
                        gstamp[v] = gcur;
                        gq0[tail++] = v;
                    }
                }
            }
        }
        if (tail != N) return 0;
    }
    return 1;
}

/* Load a graph (n vertices, m edges as pairs) and keep it if it is a simple
   bipartite graph with max degree DEG and diameter <= DIAM. */
static int try_load(int n, int m, const int *pr) {
    if (n < 1 || n > GCAPMAX - 2 || m < 0) return 0;
    GN = n;
    for (int v = 0; v < n; v++) { gdeg[v] = 0; gside[v] = -1; }
    for (int i = 0; i < m; i++) {
        int u = pr[2 * i], v = pr[2 * i + 1];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (gdeg[u] >= DEG || gdeg[v] >= DEG) return 0;
        if (g_has(u, v)) return 0;
        g_add(u, v);
    }
    for (int s = 0; s < n; s++) {
        if (gside[s] >= 0) continue;
        gside[s] = 0;
        int h = 0, t = 0;
        gq1[t++] = s;
        while (h < t) {
            int u = gq1[h++];
            for (int i = 0; i < gdeg[u]; i++) {
                int v = gadj[(size_t)u * DEG + i];
                if (gside[v] < 0) {
                    gside[v] = 1 - gside[u];
                    gq1[t++] = v;
                } else if (gside[v] == gside[u]) {
                    return 0;
                }
            }
        }
    }
    return g_diam_ok();
}

/* Random A-side vertex with an edge; returns its edge (a in A, b in B). */
static int pick_edge(int *a, int *b) {
    for (int t = 0; t < 100000; t++) {
        int v = rnd_int(GN);
        if (gside[v] == 0 && gdeg[v] > 0) {
            *a = v;
            *b = gadj[(size_t)v * DEG + rnd_int(gdeg[v])];
            return 1;
        }
    }
    return 0;
}

/* Augmentation: d disjoint edges (a_i,b_i) are replaced by x~b_i and y~a_i,
   with new x on side A and new y on side B. Grows the graph by 2. */
static int try_augment(void) {
    int N = GN;
    if (N + 2 > GCAPMAX) return 0;
    int A[64], B[64];
    int k = 0;
    if (mcur >= 2000000000) {
        memset(gmark, 0, sizeof(int) * (size_t)GCAPMAX);
        mcur = 0;
    }
    mcur++;
    for (int tr = 0; tr < 400 && k < DEG; tr++) {
        int a, b;
        if (!pick_edge(&a, &b)) break;
        if (gmark[a] == mcur || gmark[b] == mcur) continue;
        gmark[a] = mcur;
        gmark[b] = mcur;
        A[k] = a;
        B[k] = b;
        k++;
    }
    if (k < DEG) return 0;
    for (int i = 0; i < k; i++) g_remove(A[i], B[i]);
    int x = N, y = N + 1;
    gdeg[x] = 0;
    gdeg[y] = 0;
    gside[x] = 0;
    gside[y] = 1;
    GN = N + 2;
    for (int i = 0; i < k; i++) {
        g_add(x, B[i]);
        g_add(A[i], y);
    }
    if (g_diam_ok()) return 1;
    for (int i = 0; i < k; i++) {
        g_remove(x, B[i]);
        g_remove(A[i], y);
    }
    for (int i = 0; i < k; i++) g_add(A[i], B[i]);
    GN = N;
    return 0;
}

/* Plateau move: double-edge swap, kept only if the diameter is still <= DIAM. */
static int try_swap(void) {
    int a1, b1, a2, b2;
    if (!pick_edge(&a1, &b1)) return 0;
    if (!pick_edge(&a2, &b2)) return 0;
    if (a1 == a2 || b1 == b2) return 0;
    if (g_has(a1, b2) || g_has(a2, b1)) return 0;
    g_remove(a1, b1);
    g_remove(a2, b2);
    g_add(a1, b2);
    g_add(a2, b1);
    if (g_diam_ok()) return 1;
    g_remove(a1, b2);
    g_remove(a2, b1);
    g_add(a1, b1);
    g_add(a2, b2);
    return 0;
}

static void augment_phase(void) {
    if (GN < 2 || DEG > 64) return;
    while (elapsed() < DEADLINE) {
        if (rnd_unit() < 0.5) try_augment();
        else try_swap();
    }
}

/* Optional start graph on stdin: "n m" then m lines "u v". Returns NULL if none. */
static int *read_start(int *n_out, int *m_out) {
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) return NULL;
    if (n <= 0 || m <= 0 || n > GCAPMAX - 2) return NULL;
    int *p = malloc(sizeof(int) * 2 * (size_t)m);
    for (int i = 0; i < 2 * m; i++) {
        if (scanf("%d", &p[i]) != 1) {
            free(p);
            return NULL;
        }
    }
    *n_out = n;
    *m_out = m;
    return p;
}

static void print_graph(void) {
    long long m2 = 0;
    for (int v = 0; v < GN; v++) m2 += gdeg[v];
    printf("%d %lld\n", GN, m2 / 2);
    for (int u = 0; u < GN; u++)
        for (int i = 0; i < gdeg[u]; i++) {
            int v = gadj[(size_t)u * DEG + i];
            if (v > u) printf("%d %d\n", u, v);
        }
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
    double TOTAL = atof(argv[4]);
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

    /* Phase-2 storage and the optional stdin start graph. */
    gadj = malloc(sizeof(int) * (size_t)GCAPMAX * DEG);
    gdeg = calloc(GCAPMAX, sizeof(int));
    gside = calloc(GCAPMAX, sizeof(int));
    gstamp = calloc(GCAPMAX, sizeof(int));
    gmark = calloc(GCAPMAX, sizeof(int));
    gq0 = malloc(sizeof(int) * GCAPMAX);
    gq1 = malloc(sizeof(int) * GCAPMAX);
    int sn = 0, smc = 0;
    int *sp = read_start(&sn, &smc);
    int *kp = malloc(sizeof(int) * 2 * (size_t)DEG * DEG + 2);
    {
        int idx = 0;
        for (int a = 0; a < DEG; a++)
            for (int b = 0; b < DEG; b++) {
                kp[idx++] = a;
                kp[idx++] = DEG + b;
            }
    }

    /* Phase 1: lift search with annealing and ILS. */
    DEADLINE = PHASE1 * TOTAL;
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

    /* Phase 2: pick the largest valid base, then grow it by edge switches. */
    DEADLINE = TOTAL;
    int chosen = -1, cn = 0;
    if (best_m > 0 && try_load(best_n, best_m, best_e)) {
        chosen = 0;
        cn = best_n;
    }
    if (sp && sn > cn && try_load(sn, smc, sp)) {
        chosen = 1;
        cn = sn;
    }
    if (DIAM >= 2 && 2 * DEG > cn && try_load(2 * DEG, DEG * DEG, kp)) {
        chosen = 2;
        cn = 2 * DEG;
    }
    if (chosen == 0) try_load(best_n, best_m, best_e);
    else if (chosen == 1) try_load(sn, smc, sp);
    else if (chosen == 2) try_load(2 * DEG, DEG * DEG, kp);

    if (chosen >= 0) {
        augment_phase();
        print_graph();
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
# Driver: baselines in Python, then the C engine (lift search, then growth
# by edge switches from the best valid base).
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

    # Give the C search nearly all of the budget. The best Python construction
    # is passed as the start graph so C can grow it if the lift search fails.
    remaining = 0.90 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            stdin_graph=best, timeout=remaining + 6.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
