import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Engine A (unchanged from the parent): voltage lifts of semidirect products
# Z_m x| Z_k2 over a base of K A-vertices and K B-vertices, searched by
# simulated annealing with breakout weights and an elite-pool ILS.
# ----------------------------------------------------------------------------

OLD_C_SOURCE = r"""
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
# Engine B (new): edge-switch growth search on an explicit d-regular bipartite
# graph. Each growth step adds one A-vertex and one B-vertex by subdividing a
# matching of d edges (edge x_k-y_k becomes a-y_k and x_k-b), which keeps every
# degree at d and the graph bipartite. Simulated annealing on the number of
# vertex pairs at distance > D then repairs the graph with random double-edge
# switches (which keep degrees and bipartiteness). The best valid graph found
# is printed. Starts from stdin if it is d-regular, bipartite and valid,
# otherwise from K_{d,d}.
# ----------------------------------------------------------------------------

NEW_C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXV 2048
#define MAXW ((MAXV + 63) / 64)
#define MAXDEG 16
#define MAXE (MAXV * MAXDEG / 2 + 64)
#define BASE_IT 6000
#define TSTART 2.0
#define TEND 0.1

static int DEG, DIAM;
static int N, E;
static int eu[MAXE], ev[MAXE];
static int adj[MAXV * MAXDEG];
static uint64_t bufA[MAXV * MAXW], bufB[MAXV * MAXW];
static int bestN, bestE;
static int beu[MAXE], bev[MAXE];
static double DEADLINE;
static struct timespec T0;
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

static int has_edge(int a, int b) {
    for (int k = 0; k < DEG; k++)
        if (adj[a * DEG + k] == b) return 1;
    return 0;
}

static void rebuild_adj(void) {
    int deg[MAXV];
    memset(deg, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < E; e++) {
        int a = eu[e], b = ev[e];
        adj[a * DEG + deg[a]++] = b;
        adj[b * DEG + deg[b]++] = a;
    }
}

/* Number of unordered vertex pairs at distance > DIAM (bitset BFS). */
static long long eval_cost(void) {
    int W = (N + 63) / 64;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++)
        cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *s = cur + (size_t)v * W;
            memcpy(o, s, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < DEG; k++) {
                const uint64_t *su = cur + (size_t)adj[v * DEG + k] * W;
                for (int w = 0; w < W; w++) o[w] |= su[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long reached = 0;
    size_t tot = (size_t)N * (size_t)W;
    for (size_t i = 0; i < tot; i++) reached += popc64(cur[i]);
    long long all = (long long)N * (long long)N;
    return (all - reached) / 2;
}

static void replace_nb(int v, int old, int nw) {
    for (int k = 0; k < DEG; k++)
        if (adj[v * DEG + k] == old) { adj[v * DEG + k] = nw; return; }
}

/* Edges e1=(x1,y1), e2=(x2,y2) become (x1,y2), (x2,y1). Applying it twice undoes it. */
static int swap_ok(int e1, int e2) {
    int x1 = eu[e1], y1 = ev[e1], x2 = eu[e2], y2 = ev[e2];
    if (e1 == e2 || x1 == x2 || y1 == y2) return 0;
    if (has_edge(x1, y2) || has_edge(x2, y1)) return 0;
    return 1;
}

static void do_swap(int e1, int e2) {
    int x1 = eu[e1], y1 = ev[e1], x2 = eu[e2], y2 = ev[e2];
    replace_nb(x1, y1, y2);
    replace_nb(y1, x1, x2);
    replace_nb(x2, y2, y1);
    replace_nb(y2, x2, x1);
    ev[e1] = y2;
    ev[e2] = y1;
}

static int anneal(long long iters, double tstart, double tend) {
    long long cur = eval_cost();
    for (long long it = 0; it < iters && cur > 0; it++) {
        if ((it & 15) == 0 && elapsed() > DEADLINE) break;
        int e1 = rnd_int(E), e2 = rnd_int(E);
        if (!swap_ok(e1, e2)) continue;
        double frac = (double)it / (double)iters;
        double temp = tstart * pow(tend / tstart, frac);
        do_swap(e1, e2);
        long long c2 = eval_cost();
        if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / temp)) {
            cur = c2;
        } else {
            do_swap(e1, e2);
        }
    }
    return cur == 0;
}

/* Add one A-vertex a=N and one B-vertex b=N+1 by taking a matching of DEG edges. */
static int grow_pair(void) {
    if (N + 2 > MAXV || E + DEG > MAXE) return -2;
    int chosen[MAXDEG];
    int nc = 0;
    for (int tries = 0; tries < 20000 && nc < DEG; tries++) {
        int e = rnd_int(E);
        int ok = 1;
        for (int j = 0; j < nc; j++)
            if (eu[chosen[j]] == eu[e] || ev[chosen[j]] == ev[e]) { ok = 0; break; }
        if (ok) chosen[nc++] = e;
    }
    if (nc < DEG) return -1;
    int a = N, b = N + 1;
    for (int k = 0; k < DEG; k++) {
        int e = chosen[k];
        int x = eu[e], y = ev[e];
        eu[e] = a; ev[e] = y;
        eu[E + k] = x; ev[E + k] = b;
    }
    E += DEG;
    N += 2;
    rebuild_adj();
    return 0;
}

static int read_start(void) {
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 1 || n > MAXV - 2 || m < 0 || m > MAXE) return 0;
    static int ru[MAXE], rv[MAXE];
    static int nb[MAXV * MAXDEG];
    static int dc[MAXV];
    static int colr[MAXV];
    static int queue[MAXV];
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &ru[i], &rv[i]) != 2) return 0;
        if (ru[i] < 0 || ru[i] >= n || rv[i] < 0 || rv[i] >= n || ru[i] == rv[i]) return 0;
    }
    memset(dc, 0, sizeof(int) * (size_t)n);
    for (int i = 0; i < m; i++) {
        int a = ru[i], b = rv[i];
        if (dc[a] >= DEG || dc[b] >= DEG) return 0;
        nb[a * DEG + dc[a]++] = b;
        nb[b * DEG + dc[b]++] = a;
    }
    for (int v = 0; v < n; v++)
        if (dc[v] != DEG) return 0;
    for (int v = 0; v < n; v++)
        for (int k = 0; k < DEG; k++)
            for (int l = k + 1; l < DEG; l++)
                if (nb[v * DEG + k] == nb[v * DEG + l]) return 0;
    for (int v = 0; v < n; v++) colr[v] = -1;
    for (int s = 0; s < n; s++) {
        if (colr[s] != -1) continue;
        colr[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int k = 0; k < DEG; k++) {
                int w = nb[u * DEG + k];
                if (colr[w] == -1) {
                    colr[w] = 1 - colr[u];
                    queue[qt++] = w;
                } else if (colr[w] == colr[u]) {
                    return 0;
                }
            }
        }
    }
    N = n;
    E = m;
    for (int i = 0; i < m; i++) {
        if (colr[ru[i]] == 0) { eu[i] = ru[i]; ev[i] = rv[i]; }
        else { eu[i] = rv[i]; ev[i] = ru[i]; }
    }
    rebuild_adj();
    return 1;
}

static void build_kdd(void) {
    N = 2 * DEG;
    E = 0;
    for (int i = 0; i < DEG; i++)
        for (int j = 0; j < DEG; j++) {
            eu[E] = i;
            ev[E] = DEG + j;
            E++;
        }
    rebuild_adj();
}

static void save_best(void) {
    bestN = N;
    bestE = E;
    memcpy(beu, eu, sizeof(int) * (size_t)E);
    memcpy(bev, ev, sizeof(int) * (size_t)E);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    if (DEG < 1 || DEG > MAXDEG || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    if (!read_start() || eval_cost() != 0) {
        build_kdd();
    }
    save_best();

    long long fails = 0;
    while (elapsed() < DEADLINE) {
        N = bestN;
        E = bestE;
        memcpy(eu, beu, sizeof(int) * (size_t)E);
        memcpy(ev, bev, sizeof(int) * (size_t)E);
        rebuild_adj();
        int g = grow_pair();
        if (g == -2) break;
        if (g == -1) {
            fails++;
            continue;
        }
        long long f = fails < 30 ? fails : 30;
        long long iters = (long long)(BASE_IT * pow(1.25, (double)f));
        int ok = anneal(iters, TSTART, TEND);
        if (ok) {
            save_best();
            fails = 0;
        } else {
            fails++;
        }
    }

    printf("%d %d\n", bestN, bestE);
    for (int e = 0; e < bestE; e++)
        printf("%d %d\n", beu[e], bev[e]);
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


def _is_regular(n, edges, d):
    """True if every vertex 0..n-1 has degree exactly d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


# ----------------------------------------------------------------------------
# Driver.
# Weak cases (d >= 5 and D >= 5): run the voltage-lift engine for part of the
# budget, then grow its best graph with the edge-switch engine (engine B).
# Other cases keep the parent pipeline.
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

    def elapsed():
        return time.monotonic() - start

    if D >= 3:
        for builder in (_best_pg, _araujo):
            try:
                g = builder(d)
                if g is not None:
                    consider(g[0], g[1])
            except Exception:
                pass

    weak = d >= 5 and D >= 5

    if D >= 4 and (weak or elapsed() < 0.3 * time_limit):
        try:
            gq = _gq_w(d - 1) if (weak and lib.is_prime_power(d - 1) and d - 1 <= 9) \
                else _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    def remaining():
        return 0.9 * time_limit - elapsed() - 3.0

    if not weak:
        rem = remaining()
        if rem >= 1.0:
            hard = min(rem + 3.0, time_limit - elapsed() - 1.5)
            try:
                out = lib.run_c(OLD_C_SOURCE, [d, D, seed, f"{rem:.2f}", best_n],
                                timeout=hard)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass
    else:
        # Phase 1: voltage-lift engine (the parent's record-reaching search).
        rem = remaining()
        if rem >= 2.0:
            budget = 0.45 * rem
            hard = min(budget + 4.0, time_limit - elapsed() - 1.5)
            try:
                out = lib.run_c(OLD_C_SOURCE, [d, D, seed, f"{budget:.2f}", best_n],
                                timeout=hard)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

        # Phase 2: edge-switch growth from the best d-regular graph we have.
        rem = remaining()
        if rem >= 2.0:
            if _is_regular(best[0], best[1], d):
                seed_graph = best
            else:
                seed_graph = lib.haar_graph(d, range(d))
            hard = min(rem + 4.0, time_limit - elapsed() - 1.5)
            try:
                out = lib.run_c(NEW_C_SOURCE, [d, D, seed, f"{rem:.2f}"],
                                stdin_graph=seed_graph, timeout=hard)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
