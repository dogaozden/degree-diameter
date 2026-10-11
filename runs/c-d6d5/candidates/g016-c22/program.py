import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Two-stage search for the target cases.
#
# Stage 1 (C_LIFT): the voltage-lift annealer from the parent. It is a fast
# source of a large, exactly regular valid graph.
#
# Stage 2 (C_GROW): a different construction. It works on the explicit graph,
# not on a group. Each step is a random 2-switch between A-B edges, which keeps
# every vertex at degree d and the graph bipartite. The cost is the number of
# ordered vertex pairs at distance greater than D. Distances are computed with
# bitset ball expansion, which costs about D*N*d*N/64 word operations per
# evaluation. When the cost reaches 0 the graph is valid. Then one new A-vertex
# and one new B-vertex are inserted: d edges (x_i, y_i) with distinct endpoints
# are rerouted through the two new vertices, which keeps regularity. The
# annealer then repairs the graph at the larger size. If repair fails within
# its budget, the engine restores the last valid graph and tries again with a
# bigger budget.
#
# Every stage keeps the best valid graph. Python checks it with lib.is_valid
# and falls back to a safe baseline if anything goes wrong.
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


C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXW 32
#define MAXDEG 16
#define MAXE (MAXN * MAXDEG / 2)

static int DEG, DIAM, N, E;
static int nb[MAXN * MAXDEG];
static int ea[MAXE + MAXDEG], eb[MAXE + MAXDEG];
static int bea[MAXE + MAXDEG], beb[MAXE + MAXDEG];
static int bestN = 0, bestE = 0;
static uint64_t bufA[MAXN * MAXW], bufB[MAXN * MAXW];
static struct timespec T0;
static double DEADLINE;
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

static inline int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of ordered pairs (v, w) with dist(v, w) > DIAM. */
static long long eval_cost(void) {
    int w = (N + 63) >> 6;
    uint64_t *P = bufA, *Q = bufB;
    for (int v = 0; v < N; v++) {
        uint64_t *c = P + (size_t)v * MAXW;
        for (int k = 0; k < w; k++) c[k] = 0;
        c[v >> 6] |= 1ULL << (v & 63);
    }
    for (int step = 0; step < DIAM; step++) {
        for (int v = 0; v < N; v++) {
            uint64_t *x = Q + (size_t)v * MAXW;
            const uint64_t *c = P + (size_t)v * MAXW;
            for (int k = 0; k < w; k++) x[k] = c[k];
            const int *nv = nb + (size_t)v * DEG;
            for (int j = 0; j < DEG; j++) {
                const uint64_t *cu = P + (size_t)nv[j] * MAXW;
                for (int k = 0; k < w; k++) x[k] |= cu[k];
            }
        }
        uint64_t *t = P; P = Q; Q = t;
    }
    long long miss = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *c = P + (size_t)v * MAXW;
        int cn = 0;
        for (int k = 0; k < w; k++) cn += pc64(c[k]);
        miss += N - cn;
    }
    return miss;
}

/* Replace neighbour `old` of v by `nw`. */
static void rep(int v, int old, int nw) {
    int *s = nb + (size_t)v * DEG;
    for (int j = 0; j < DEG; j++)
        if (s[j] == old) { s[j] = nw; return; }
    fprintf(stderr, "internal adjacency error\n");
    exit(2);
}

static int adjacent(int a, int b) {
    const int *s = nb + (size_t)a * DEG;
    for (int j = 0; j < DEG; j++)
        if (s[j] == b) return 1;
    return 0;
}

/* 2-switch: edges (a1,b1),(a2,b2) become (a1,b2),(a2,b1). Applying it twice restores the start. */
static void swap2(int e1, int e2) {
    int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
    rep(a1, b1, b2);
    rep(b1, a1, a2);
    rep(a2, b2, b1);
    rep(b2, a2, a1);
    eb[e1] = b2;
    eb[e2] = b1;
}

/* Insert one A-vertex N and one B-vertex N+1 keeping regularity. */
static int grow_one(void) {
    static int chosen[MAXDEG];
    if (N + 2 > MAXN || E + DEG > MAXE) return 0;
    int as = N, bs = N + 1;
    int nch = 0;
    long tries = 0;
    while (nch < DEG) {
        if (++tries > 200000) return 0;
        int e = rnd_int(E);
        int ok = 1;
        for (int i = 0; i < nch; i++)
            if (ea[chosen[i]] == ea[e] || eb[chosen[i]] == eb[e]) { ok = 0; break; }
        if (ok) chosen[nch++] = e;
    }
    for (int i = 0; i < DEG; i++) {
        int e = chosen[i];
        int x = ea[e], y = eb[e];
        rep(x, y, bs);
        rep(y, x, as);
        nb[(size_t)bs * DEG + i] = x;
        nb[(size_t)as * DEG + i] = y;
        eb[e] = bs;
        ea[E + i] = as;
        eb[E + i] = y;
    }
    E += DEG;
    N += 2;
    return 1;
}

/* Fill nb from edge arrays; fails unless every vertex 0..n-1 has degree DEG. */
static int build_nb(int n, int m, const int *A, const int *B) {
    static int cntv[MAXN];
    if (n < 1 || n > MAXN || m < 0 || m > MAXE) return 0;
    memset(cntv, 0, sizeof(int) * (size_t)n);
    for (int i = 0; i < m; i++) {
        int u = A[i], v = B[i];
        if (u < 0 || u >= n || v < 0 || v >= n || u == v) return 0;
        if (cntv[u] >= DEG || cntv[v] >= DEG) return 0;
        nb[(size_t)u * DEG + cntv[u]++] = v;
        nb[(size_t)v * DEG + cntv[v]++] = u;
    }
    for (int v = 0; v < n; v++)
        if (cntv[v] != DEG) return 0;
    return 1;
}

static int load_graph(int n, int m) {
    static int U[MAXE], V[MAXE];
    static int col[MAXN], stk[MAXN];
    if (n < 1 || n > MAXN || m < 0 || m > MAXE) return 0;
    for (int i = 0; i < m; i++)
        if (scanf("%d %d", &U[i], &V[i]) != 2) return 0;
    if (!build_nb(n, m, U, V)) return 0;
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp) {
            int u = stk[--sp];
            for (int j = 0; j < DEG; j++) {
                int v = nb[(size_t)u * DEG + j];
                if (col[v] == -1) { col[v] = 1 - col[u]; stk[sp++] = v; }
                else if (col[v] == col[u]) return 0;
            }
        }
    }
    for (int i = 0; i < m; i++) {
        if (col[U[i]] == 0) { ea[i] = U[i]; eb[i] = V[i]; }
        else { ea[i] = V[i]; eb[i] = U[i]; }
    }
    N = n;
    E = m;
    return 1;
}

/* Random DEG-regular bipartite graph on n0 vertices (halves of size n0/2). */
static int random_regular(int n0) {
    static int cntv[MAXN];
    static int p[MAXN];
    if (n0 < 2 * DEG || n0 > MAXN || (n0 & 1)) return 0;
    int h = n0 / 2;
    memset(cntv, 0, sizeof(int) * (size_t)n0);
    for (int l = 0; l < DEG; l++) {
        int ok = 0;
        for (int att = 0; att < 20000 && !ok; att++) {
            for (int i = 0; i < h; i++) p[i] = i;
            for (int i = h - 1; i > 0; i--) {
                int j = rnd_int(i + 1);
                int t = p[i]; p[i] = p[j]; p[j] = t;
            }
            ok = 1;
            for (int i = 0; i < h && ok; i++) {
                int b = h + p[i];
                for (int j = 0; j < cntv[i]; j++)
                    if (nb[(size_t)i * DEG + j] == b) { ok = 0; break; }
            }
        }
        if (!ok) return 0;
        for (int i = 0; i < h; i++) {
            int a = i, b = h + p[i];
            nb[(size_t)a * DEG + cntv[a]++] = b;
            nb[(size_t)b * DEG + cntv[b]++] = a;
        }
    }
    int e = 0;
    for (int i = 0; i < h; i++)
        for (int j = 0; j < DEG; j++) {
            ea[e] = i;
            eb[e] = nb[(size_t)i * DEG + j];
            e++;
        }
    N = n0;
    E = e;
    return 1;
}

static void save_best(void) {
    bestN = N;
    bestE = E;
    memcpy(bea, ea, sizeof(int) * (size_t)E);
    memcpy(beb, eb, sizeof(int) * (size_t)E);
}

static int restore_best(void) {
    if (!build_nb(bestN, bestE, bea, beb)) return 0;
    N = bestN;
    E = bestE;
    memcpy(ea, bea, sizeof(int) * (size_t)E);
    memcpy(eb, beb, sizeof(int) * (size_t)E);
    return 1;
}

/* Metropolis annealing over 2-switches. Returns 0 as soon as the cost hits 0. */
static long long anneal(long long budget, long long cost) {
    const double T_HOT = 3.0, T_COLD = 0.3;
    for (long long it = 0; it < budget; it++) {
        if ((it & 127) == 0 && elapsed() > DEADLINE) break;
        double frac = (double)it / (double)budget;
        double temp = T_HOT * (1.0 - frac) + T_COLD;
        int e1 = rnd_int(E), e2 = rnd_int(E);
        if (e1 == e2) continue;
        int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
        if (a1 == a2 || b1 == b2) continue;
        if (adjacent(a1, b2) || adjacent(a2, b1)) continue;
        swap2(e1, e2);
        long long c2 = eval_cost();
        long long dl = c2 - cost;
        if (dl <= 0 || rnd_unit() < exp(-(double)dl / temp)) {
            cost = c2;
            if (cost == 0) return 0;
        } else {
            swap2(e1, e2);
        }
    }
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [n0]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int N0 = argc > 5 ? atoi(argv[5]) : 0;
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    int ok;
    if (n > 0) ok = load_graph(n, m);
    else ok = random_regular(N0);
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    long long cost = eval_cost();
    if (cost == 0) save_best();

    int fails = 0;
    while (elapsed() < DEADLINE) {
        if (cost == 0) {
            save_best();
            if (!grow_one()) break;
            fails = 0;
            cost = eval_cost();
            continue;
        }
        long long budget = 20000LL * (1LL + fails);
        cost = anneal(budget, cost);
        if (cost == 0) continue;
        fails++;
        if (bestN > 0) {
            if (!restore_best()) break;
            if (!grow_one()) break;
            cost = eval_cost();
        }
    }

    if (bestN > 0) {
        printf("%d %d\n", bestN, bestE);
        for (int i = 0; i < bestE; i++)
            printf("%d %d\n", bea[i], beb[i]);
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


def _is_regular(n, edges, d):
    """True if every vertex 0..n-1 has degree exactly d."""
    if n < 1:
        return False
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


# ----------------------------------------------------------------------------
# Driver: baselines, then the lift annealer (stage 1), then the growth search
# (stage 2) starting from the best graph found so far.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    # Keep a margin for compile, process start, parsing and validation.
    end = start + 0.90 * time_limit - 1.0
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} is d-regular with diameter 2.
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

    # Stage 1: voltage-lift annealing from the parent (about 40% of the span).
    span = end - time.monotonic()
    if span >= 3.0:
        t1 = 0.40 * span
        try:
            out = lib.run_c(C_LIFT, [d, D, seed, f"{t1:.2f}", best_n],
                            timeout=t1 + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Stage 2: explicit 2-switch annealing with vertex-pair growth, from the
    # best regular graph. If the best graph is not regular, grow from a random
    # regular graph of the same order.
    span = end - time.monotonic() - 0.5
    if span >= 3.0:
        if _is_regular(best[0], best[1], d):
            stdin_graph = best
            n0 = 2 * d
        else:
            stdin_graph = None
            n0 = max(best_n - best_n % 2, 2 * d)
        try:
            out = lib.run_c(C_GROW, [d, D, seed + 1, f"{span:.2f}", n0],
                            stdin_graph=stdin_graph, timeout=span + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
