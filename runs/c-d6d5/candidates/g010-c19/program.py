import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 (C): voltage lifts of semidirect products Z_m x| Z_k2 over a base of
# K A-vertices and K B-vertices, searched by simulated annealing with breakout
# weights and an elite pool (ILS). It supplies a large start graph.
# ----------------------------------------------------------------------------

LIFT_SOURCE = r"""
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
# Stage 2 (C): a different construction. Starting from a valid bipartite graph,
# insert a pair of new vertices x (side A) and y (side B) by a degree-preserving
# splice: pick a matching of d edges (a_i, b_i), replace each by (a_i, y) and
# attach (x, b_i). Degrees of old vertices are unchanged, x and y get degree d.
# Then anneal over 2-switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1) to minimise the
# number of ordered vertex pairs at distance > D. Reachability is computed with
# bit-parallel BFS. On success the graph is saved and the next pair is inserted.
# ----------------------------------------------------------------------------

INS_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

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

static int DEG, DIAM, NMAX, W, N, NE;
static int *side, *deg, *adjv, *eu, *ev, *perm, *useA, *useB;
static uint64_t *R0, *R1;
static int *vs_eu, *vs_ev;
static int vs_N, vs_NE, vs_valid;
static int usegen = 0;

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    const int *au = adjv + (size_t)u * DEG;
    for (int i = 0; i < deg[u]; i++)
        if (au[i] == v) return 1;
    return 0;
}

static void replace_nb(int v, int old, int nw) {
    int *av = adjv + (size_t)v * DEG;
    for (int i = 0; i < deg[v]; i++)
        if (av[i] == old) { av[i] = nw; return; }
}

static void rebuild_adj(void) {
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int e = 0; e < NE; e++) {
        int a = eu[e], b = ev[e];
        adjv[(size_t)a * DEG + deg[a]++] = b;
        adjv[(size_t)b * DEG + deg[b]++] = a;
    }
}

/* Bit-parallel reachability within DIAM steps; returns number of ordered bad pairs. */
static long long eval_cost(void) {
    int Wa = (N + 63) / 64;
    uint64_t *cur = R0, *nxt = R1;
    for (int v = 0; v < N; v++) {
        uint64_t *r = cur + (size_t)v * W;
        memset(r, 0, sizeof(uint64_t) * (size_t)Wa);
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < N; v++) {
            uint64_t *out = nxt + (size_t)v * W;
            const uint64_t *in = cur + (size_t)v * W;
            memcpy(out, in, sizeof(uint64_t) * (size_t)Wa);
            const int *av = adjv + (size_t)v * DEG;
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *nb = cur + (size_t)av[i] * W;
                for (int w = 0; w < Wa; w++) out[w] |= nb[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *r = cur + (size_t)v * W;
        for (int w = 0; w < Wa; w++) cnt += popc64(r[w]);
    }
    return (long long)N * N - cnt;
}

/* 2-switch: edges e1=(a1,b1), e2=(a2,b2) become (a1,b2), (a2,b1). Calling it twice undoes it. */
static void do_switch(int e1, int e2) {
    int a1 = eu[e1], b1 = ev[e1], a2 = eu[e2], b2 = ev[e2];
    replace_nb(a1, b1, b2);
    replace_nb(b1, a1, a2);
    replace_nb(a2, b2, b1);
    replace_nb(b2, a2, a1);
    ev[e1] = b2;
    ev[e2] = b1;
}

static void save_vs(void) {
    memcpy(vs_eu, eu, sizeof(int) * (size_t)NE);
    memcpy(vs_ev, ev, sizeof(int) * (size_t)NE);
    vs_N = N;
    vs_NE = NE;
    vs_valid = 1;
}

static void restore_vs(void) {
    N = vs_N;
    NE = vs_NE;
    memcpy(eu, vs_eu, sizeof(int) * (size_t)NE);
    memcpy(ev, vs_ev, sizeof(int) * (size_t)NE);
    rebuild_adj();
}

/* Degree-preserving splice of a new pair (x in A, y in B). */
static int insert_pair(void) {
    if (N + 2 > NMAX) return 0;
    for (int i = 0; i < NE; i++) perm[i] = i;
    for (int i = NE - 1; i > 0; i--) {
        int j = rnd_int(i + 1);
        int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
    }
    usegen++;
    int ch[64];
    int nc = 0;
    for (int k = 0; k < NE && nc < DEG; k++) {
        int e = perm[k];
        int a = eu[e], b = ev[e];
        if (useA[a] == usegen || useB[b] == usegen) continue;
        useA[a] = usegen;
        useB[b] = usegen;
        ch[nc++] = e;
    }
    if (nc < DEG) return 0;
    int x = N, y = N + 1;
    side[x] = 0;
    side[y] = 1;
    deg[x] = 0;
    deg[y] = 0;
    for (int i = 0; i < nc; i++) {
        int e = ch[i];
        int a = eu[e], b = ev[e];
        replace_nb(a, b, y);
        replace_nb(b, a, x);
        ev[e] = y;
        eu[NE] = x;
        ev[NE] = b;
        NE++;
        adjv[(size_t)x * DEG + deg[x]++] = b;
        adjv[(size_t)y * DEG + deg[y]++] = a;
    }
    N += 2;
    return 1;
}

/* Simulated annealing over 2-switches. Stops early at cost 0 (valid graph). */
static long long anneal(double budget) {
    long long cost = eval_cost();
    if (cost == 0 || NE < 2) return cost;
    double t0 = elapsed();
    double tEnd = t0 + budget;
    if (tEnd > DEADLINE) tEnd = DEADLINE;
    double span = tEnd - t0;
    if (span <= 0) return cost;
    const double Tl = 0.2;
    double Th = 3.0 + 0.02 * (double)cost;
    double frac = 0.0, temp = Th;
    long long it = 0;
    for (;;) {
        if ((it & 15) == 0) {
            double now = elapsed();
            if (now >= tEnd) break;
            frac = (now - t0) / span;
            temp = Th * pow(Tl / Th, frac);
        }
        it++;
        int e1 = rnd_int(NE), e2 = rnd_int(NE);
        if (e1 == e2) continue;
        int a1 = eu[e1], b1 = ev[e1], a2 = eu[e2], b2 = ev[e2];
        (void)b1; (void)a2;
        if (has_edge(a1, b2) || has_edge(a2, b1)) continue;
        do_switch(e1, e2);
        long long c2 = eval_cost();
        if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost == 0) break;
        } else {
            do_switch(e1, e2);
        }
    }
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed time_limit nmax  (graph on stdin)\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    NMAX = atoi(argv[5]);
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 < 0 || DEG < 1 || DEG > 60 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    if (NMAX < n0 + 2) NMAX = n0 + 2;
    if (NMAX > 20000) NMAX = 20000;
    W = (NMAX + 63) / 64;
    size_t cap = (size_t)NMAX * DEG;
    if ((size_t)m0 > cap) {
        printf("0 0\n");
        return 0;
    }
    adjv = malloc(sizeof(int) * cap);
    eu = malloc(sizeof(int) * cap);
    ev = malloc(sizeof(int) * cap);
    perm = malloc(sizeof(int) * cap);
    vs_eu = malloc(sizeof(int) * cap);
    vs_ev = malloc(sizeof(int) * cap);
    side = malloc(sizeof(int) * (size_t)NMAX);
    deg = calloc((size_t)NMAX, sizeof(int));
    useA = calloc((size_t)NMAX, sizeof(int));
    useB = calloc((size_t)NMAX, sizeof(int));
    R0 = malloc(sizeof(uint64_t) * (size_t)NMAX * W);
    R1 = malloc(sizeof(uint64_t) * (size_t)NMAX * W);

    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { printf("0 0\n"); return 0; }
        eu[i] = u;
        ev[i] = v;
    }
    N = n0;
    NE = m0;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int e = 0; e < NE; e++) { deg[eu[e]]++; deg[ev[e]]++; }
    for (int v = 0; v < N; v++)
        if (deg[v] > DEG) { printf("0 0\n"); return 0; }
    rebuild_adj();

    /* 2-colour the input; a non-bipartite input cannot be used. */
    for (int v = 0; v < N; v++) side[v] = -1;
    int qh = 0, qt = 0;
    for (int s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        perm[qt++] = s;
        while (qh < qt) {
            int u = perm[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int w = adjv[(size_t)u * DEG + i];
                if (side[w] == -1) {
                    side[w] = 1 - side[u];
                    perm[qt++] = w;
                } else if (side[w] == side[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    for (int e = 0; e < NE; e++)
        if (side[eu[e]] == 1) { int t = eu[e]; eu[e] = ev[e]; ev[e] = t; }
    rebuild_adj();

    vs_valid = 0;
    if (eval_cost() == 0) {
        save_vs();
    } else {
        double bud = DEADLINE - elapsed() - 0.2;
        if (bud > 10.0) bud = 10.0;
        if (bud > 0.2 && anneal(bud) == 0) {
            save_vs();
        }
    }

    int fails = 0;
    while (elapsed() < DEADLINE - 0.1) {
        if (vs_valid) {
            restore_vs();
            if (vs_N + 2 > NMAX) break;
            if (!insert_pair()) { fails++; continue; }
        }
        double rem = DEADLINE - elapsed() - 0.1;
        double bud = (fails == 0) ? 6.0 : 12.0;
        if (bud > rem) bud = rem;
        if (bud < 0.2) break;
        long long c2 = anneal(bud);
        if (c2 == 0) {
            save_vs();
            fails = 0;
        } else {
            fails++;
        }
    }

    if (!vs_valid) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", vs_N, vs_NE);
    for (int e = 0; e < vs_NE; e++)
        printf("%d %d\n", vs_eu[e], vs_ev[e]);
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
# Driver: baselines, then lift annealing for a start graph, then the splice-and-
# anneal growth stage. Every returned graph is checked with lib.is_valid.
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

    def left():
        # Margin covers compilation (not counted by the C deadlines), parsing and validation.
        return 0.88 * time_limit - (time.monotonic() - start) - 1.5

    # Stage 1: lift annealing supplies a large start graph.
    stage1 = min(0.30 * time_limit, 0.45 * left())
    if stage1 >= 2.0:
        try:
            out = lib.run_c(LIFT_SOURCE, [d, D, seed, f"{stage1:.2f}", best_n],
                            timeout=stage1 + 5.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Stage 2: grow the best valid graph by degree-preserving splices plus annealing.
    rem = left()
    if rem >= 2.0:
        nmax = best_n + 300
        try:
            out = lib.run_c(INS_SOURCE, [d, D, seed, f"{rem:.2f}", nmax],
                            stdin_graph=best, timeout=rem + 5.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
