import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 engine (C_LIFT): voltage lifts of semidirect products Z_m x| Z_k2
# over a base of K A-vertices and K B-vertices, searched by simulated annealing
# with breakout weights and an elite pool (iterated local search).
#
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart t = (i, j, s) joins
# A_i,g to B_j,g*s for all g. Each layer is a permutation, so every vertex
# has degree DEG. Diameter <= D iff BFS of depth D from each of the 2K block
# representatives covers all vertices.
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
# Stage 2 engine (C_GROW): vertex insertion plus edge-switch annealing.
#
# Start from a valid bipartite graph with max degree DEG. Insert a pair of new
# vertices v (side A) and w (side B). Take DEG edges (a_i, b_i) with distinct
# endpoints, replace each by (a_i, w), and add (v, b_i). Every old vertex keeps
# its degree and v, w each get degree DEG. Then anneal with degree-preserving
# edge switches, minimising the number of vertex pairs at distance > DEG-free
# diameter D. On reaching zero the graph is valid and becomes the new best.
# Otherwise restore the best graph and try a different random insertion.
# Output is always a valid graph (or the input best, if no growth).
# ----------------------------------------------------------------------------

C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXW 32
#define MAXM 30000
#define MAXD 32
#define ITERS 9000
#define MAXTRY 400

static int DEG, DIAM;
static int n, m;
static int eu[MAXM], ev[MAXM];
static unsigned char adjm[MAXN * MAXN];
static int bn = 0, bm = 0;
static int beu[MAXM], bev[MAXM];
static int have_best = 0;
static int adjl[MAXN * MAXD];
static int degc[MAXN];
static uint64_t Ba[MAXN * MAXW], Bb[MAXN * MAXW];
static int markA[MAXN], markB[MAXN];
static int stampv = 0;
static int ru[MAXM], rv[MAXM];
static int col[MAXN], queue_[MAXN];
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

static int rnd_int(int k) { return (int)(rnd64() % (uint64_t)k); }
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

static void rebuild_adjm(void) {
    memset(adjm, 0, sizeof adjm);
    for (int i = 0; i < m; i++) {
        adjm[eu[i] * MAXN + ev[i]] = 1;
        adjm[ev[i] * MAXN + eu[i]] = 1;
    }
}

/* Replace edge i by (a, b), keeping the adjacency matrix in sync. */
static void set_edge(int i, int a, int b) {
    adjm[eu[i] * MAXN + ev[i]] = 0;
    adjm[ev[i] * MAXN + eu[i]] = 0;
    eu[i] = a;
    ev[i] = b;
    adjm[a * MAXN + b] = 1;
    adjm[b * MAXN + a] = 1;
}

/* Number of ordered-pair misses (unordered pairs at distance > DIAM). */
static long long eval_bad(void) {
    int wn = (n + 63) >> 6;
    for (int v = 0; v < n; v++) degc[v] = 0;
    for (int i = 0; i < m; i++) {
        int a = eu[i], b = ev[i];
        if (degc[a] >= DEG || degc[b] >= DEG) return 1000000000LL;
        adjl[a * DEG + degc[a]++] = b;
        adjl[b * DEG + degc[b]++] = a;
    }
    uint64_t *cur = Ba, *nxt = Bb;
    for (int v = 0; v < n; v++) {
        for (int k = 0; k < wn; k++) cur[v * MAXW + k] = 0;
        cur[v * MAXW + (v >> 6)] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIAM; r++) {
        int changed = 0;
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + v * MAXW;
            const uint64_t *c = cur + v * MAXW;
            for (int k = 0; k < wn; k++) o[k] = c[k];
            for (int e = 0; e < degc[v]; e++) {
                const uint64_t *c2 = cur + adjl[v * DEG + e] * MAXW;
                for (int k = 0; k < wn; k++) o[k] |= c2[k];
            }
            for (int k = 0; k < wn; k++)
                if (o[k] != c[k]) changed = 1;
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int k = 0; k < wn; k++) c += popc64(cur[v * MAXW + k]);
        bad += n - c;
    }
    return bad / 2;
}

/* Degree-preserving switch annealing. Returns 0 once the graph is valid. */
static long long anneal(long long cur, int iters) {
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        int i = rnd_int(m), j = rnd_int(m);
        if (i == j) continue;
        int a1 = eu[i], b1 = ev[i], a2 = eu[j], b2 = ev[j];
        if (a1 == a2 || b1 == b2) continue;
        if (adjm[a1 * MAXN + b2] || adjm[a2 * MAXN + b1]) continue;
        set_edge(i, a1, b2);
        set_edge(j, a2, b1);
        long long c2 = eval_bad();
        double frac = (double)it / (double)iters;
        double temp = 0.6 * (1.0 - frac) * sqrt((double)cur + 1.0) + 0.05;
        if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / temp)) {
            cur = c2;
        } else {
            set_edge(i, a1, b1);
            set_edge(j, a2, b2);
        }
    }
    return cur;
}

/* Insert two new vertices v (side A, id n) and w (side B, id n+1). */
static int insert_pair(void) {
    if (n + 2 > MAXN || m + DEG > MAXM || m < DEG) return 0;
    int chosen[MAXD];
    int got = 0;
    stampv++;
    for (int t = 0; t < MAXTRY * DEG && got < DEG; t++) {
        int idx = rnd_int(m);
        int a = eu[idx], b = ev[idx];
        if (markA[a] == stampv || markB[b] == stampv) continue;
        markA[a] = stampv;
        markB[b] = stampv;
        chosen[got++] = idx;
    }
    if (got < DEG) return 0;
    int v = n, w = n + 1;
    for (int c = 0; c < DEG; c++) {
        int idx = chosen[c];
        int a = eu[idx], b = ev[idx];
        set_edge(idx, a, w);
        eu[m] = v;
        ev[m] = b;
        adjm[v * MAXN + b] = 1;
        adjm[b * MAXN + v] = 1;
        m++;
    }
    n += 2;
    return 1;
}

static void save_best(void) {
    bn = n;
    bm = m;
    memcpy(beu, eu, sizeof(int) * (size_t)m);
    memcpy(bev, ev, sizeof(int) * (size_t)m);
    have_best = 1;
}

static void restore_best(void) {
    n = bn;
    m = bm;
    memcpy(eu, beu, sizeof(int) * (size_t)m);
    memcpy(ev, bev, sizeof(int) * (size_t)m);
    rebuild_adjm();
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit  (graph on stdin)\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    uint64_t sm = sd * 2654435761ULL + 99991ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = m0 = 0; }
    if (DEG < 1 || DEG > MAXD || DIAM < 1 || n0 < 1 || n0 > MAXN - 2 ||
        m0 < 1 || m0 > MAXM - DEG) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &ru[i], &rv[i]) != 2) { printf("0 0\n"); return 0; }
        if (ru[i] < 0 || ru[i] >= n0 || rv[i] < 0 || rv[i] >= n0 || ru[i] == rv[i]) {
            printf("0 0\n");
            return 0;
        }
    }

    /* Input checks: no duplicate edges, bipartite, degree <= DEG. */
    n = n0;
    memset(adjm, 0, sizeof adjm);
    for (int i = 0; i < m0; i++) {
        int a = ru[i], b = rv[i];
        if (adjm[a * MAXN + b]) { printf("0 0\n"); return 0; }
        adjm[a * MAXN + b] = 1;
        adjm[b * MAXN + a] = 1;
    }
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        int qh = 0, qt = 0;
        col[s] = 0;
        queue_[qt++] = s;
        while (qh < qt) {
            int u = queue_[qh++];
            for (int x = 0; x < n; x++) {
                if (!adjm[u * MAXN + x]) continue;
                if (col[x] == -1) {
                    col[x] = 1 - col[u];
                    queue_[qt++] = x;
                } else if (col[x] == col[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    m = m0;
    for (int i = 0; i < m; i++) {
        if (col[ru[i]] == 0) { eu[i] = ru[i]; ev[i] = rv[i]; }
        else { eu[i] = rv[i]; ev[i] = ru[i]; }
    }
    {
        static int dg[MAXN];
        for (int v = 0; v < n; v++) dg[v] = 0;
        for (int i = 0; i < m; i++) {
            if (++dg[eu[i]] > DEG || ++dg[ev[i]] > DEG) { printf("0 0\n"); return 0; }
        }
    }
    rebuild_adjm();

    long long cost = eval_bad();
    if (cost == 0) save_best();
    if (!have_best) {
        printf("0 0\n");
        return 0;
    }

    int fails = 0;
    while (elapsed() < DEADLINE) {
        restore_best();
        if (!insert_pair()) {
            fails++;
            if (fails > 200) break;
            continue;
        }
        long long c = eval_bad();
        c = anneal(c, ITERS);
        if (c == 0) {
            save_best();
            fails = 0;
        }
    }

    printf("%d %d\n", bn, bm);
    for (int i = 0; i < bm; i++)
        printf("%d %d\n", beu[i], bev[i]);
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
# Driver: baselines, then stage 1 (lift search), then stage 2 (vertex-insertion growth).
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

    # Stage 1: voltage-lift search for a large start graph.
    lift_budget = 0.5 * time_limit - (time.monotonic() - start) - 1.0
    if lift_budget >= 1.0:
        try:
            out = lib.run_c(C_LIFT, [d, D, seed, f"{lift_budget:.2f}", best_n],
                            timeout=lift_budget + 5.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Stage 2: grow the best graph by vertex insertion and switch annealing.
    grow_budget = 0.85 * time_limit - (time.monotonic() - start) - 1.0
    if grow_budget >= 1.0:
        try:
            out = lib.run_c(C_GROW, [d, D, seed, f"{grow_budget:.2f}"],
                            stdin_graph=best, timeout=grow_budget + 5.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
