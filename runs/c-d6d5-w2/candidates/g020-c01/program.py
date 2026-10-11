import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 engine (C_LIFT): voltage lifts of semidirect products Z_m x| Z_k2
# over a base of K A-vertices and K B-vertices, searched by simulated annealing
# with breakout weights and an elite-pool iterated local search.
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart t = (i, j, s) joins
# A_i,g to B_j,g*s for all g.
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
# Stage 2 engine (C_GROW): unstructured growth and repair. It reads a valid
# bipartite graph, adds two vertices (one per side) by rewiring random edges
# so degrees stay at most d, then anneals over double-edge swaps (which keep
# degrees and bipartiteness) to minimise the number of ordered pairs at
# distance > D. Bitset BFS evaluates the cost. Failed attempts are discarded,
# so the output is always a valid graph.
# ----------------------------------------------------------------------------

C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define ATT_ITERS 12000
#define CAPMAX 5000

static uint64_t rs[2];
static struct timespec T0;
static double DL;

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

static int D, DEG, CAP;
static int n, m;
static int *deg, *adj, *eu, *ev;
static int *bdeg, *badj, *beu, *bev;
static int bn, bm;
static uint64_t *RA, *RB;
static int *side;

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Ordered pairs (v, u) with u not within distance D of v. */
static long long eval_bad(void) {
    int w = (n + 63) >> 6;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * w);
    for (int v = 0; v < n; v++) cur[(size_t)v * w + (v >> 6)] |= 1ULL << (v & 63);
    for (int lvl = 0; lvl < D; lvl++) {
        int changed = 0;
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + (size_t)v * w;
            const uint64_t *c = cur + (size_t)v * w;
            memcpy(o, c, sizeof(uint64_t) * (size_t)w);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *x = cur + (size_t)adj[(size_t)v * DEG + k] * w;
                for (int q = 0; q < w; q++) o[q] |= x[q];
            }
            for (int q = 0; q < w; q++)
                if (o[q] != c[q]) changed = 1;
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int cnt = 0;
        const uint64_t *c = cur + (size_t)v * w;
        for (int q = 0; q < w; q++) cnt += popc(c[q]);
        bad += n - cnt;
    }
    return bad;
}

static int has_edge(int a, int b) {
    const int *p = adj + (size_t)a * DEG;
    for (int k = 0; k < deg[a]; k++)
        if (p[k] == b) return 1;
    return 0;
}

static void rep(int v, int old, int nw) {
    int *p = adj + (size_t)v * DEG;
    for (int k = 0; k < deg[v]; k++)
        if (p[k] == old) { p[k] = nw; return; }
}

static void add_nb(int v, int nw) {
    adj[(size_t)v * DEG + deg[v]++] = nw;
}

/* Add vertices a (side A) and b (side B). Each step moves one old edge (x,y)
   to (x,b) and adds (a,y), so degrees of x and y are kept and a, b gain one. */
static int augment(void) {
    if (n + 2 > CAP) return 0;
    int a = n, b = n + 1;
    int nold = n;
    n += 2;
    deg[a] = 0;
    deg[b] = 0;
    for (int s = 0; s < DEG; s++) {
        int done = 0;
        for (int tries = 0; tries < 200000 && !done; tries++) {
            int i = rnd_int(m);
            int x = eu[i], y = ev[i];
            if (x >= nold || y >= nold) continue;
            if (has_edge(x, b) || has_edge(a, y)) continue;
            rep(x, y, b);
            rep(y, x, a);
            add_nb(b, x);
            add_nb(a, y);
            eu[i] = x;
            ev[i] = b;
            eu[m] = a;
            ev[m] = y;
            m++;
            done = 1;
        }
        if (!done) return 0;
    }
    return 1;
}

/* Simulated annealing over double-edge swaps. Returns the final cost; the
   state left in place is the one that produced it (0 means valid). */
static long long anneal(long long cur, int iters) {
    double t0 = 1.5, t1 = 0.05;
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 15) == 0 && elapsed() > DL) break;
        double frac = (double)it / (double)iters;
        double temp = t0 * pow(t1 / t0, frac);
        int i = rnd_int(m), j = rnd_int(m);
        if (i == j) continue;
        int u1 = eu[i], v1 = ev[i], u2 = eu[j], v2 = ev[j];
        if (u1 == u2 || v1 == v2) continue;
        if (has_edge(u1, v2) || has_edge(u2, v1)) continue;
        eu[i] = u1; ev[i] = v2;
        eu[j] = u2; ev[j] = v1;
        rep(u1, v1, v2);
        rep(v2, u2, u1);
        rep(u2, v2, v1);
        rep(v1, u1, u2);
        long long c2 = eval_bad();
        if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / temp)) {
            cur = c2;
        } else {
            eu[i] = u1; ev[i] = v1;
            eu[j] = u2; ev[j] = v2;
            rep(u1, v2, v1);
            rep(v2, u1, u2);
            rep(u2, v1, v2);
            rep(v1, u2, u1);
        }
    }
    return cur;
}

static void copy_base_to_cur(void) {
    n = bn; m = bm;
    memcpy(deg, bdeg, sizeof(int) * (size_t)CAP);
    memcpy(adj, badj, sizeof(int) * (size_t)CAP * DEG);
    memcpy(eu, beu, sizeof(int) * (size_t)CAP * DEG);
    memcpy(ev, bev, sizeof(int) * (size_t)CAP * DEG);
}

static void copy_cur_to_base(void) {
    bn = n; bm = m;
    memcpy(bdeg, deg, sizeof(int) * (size_t)CAP);
    memcpy(badj, adj, sizeof(int) * (size_t)CAP * DEG);
    memcpy(beu, eu, sizeof(int) * (size_t)CAP * DEG);
    memcpy(bev, ev, sizeof(int) * (size_t)CAP * DEG);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit  (graph on stdin)\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DL = atof(argv[4]);
    uint64_t sm = sd * 2654435761ULL + 999ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);
    if (DEG < 2 || D < 1) {
        printf("0 0\n");
        return 0;
    }

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    double mb = 0.0, pw = 1.0;
    for (int i = 0; i < D; i++) { mb += pw; pw *= (DEG - 1); if (mb > 1e6) break; }
    CAP = (int)(2.0 * mb) + 4;
    if (CAP > CAPMAX) CAP = CAPMAX;
    if (CAP < n0 + 2) CAP = n0 + 2;
    if (CAP > CAPMAX) {
        printf("0 0\n");
        return 0;
    }

    size_t NE = (size_t)CAP * DEG;
    deg = calloc((size_t)CAP, sizeof(int));
    adj = calloc(NE, sizeof(int));
    eu = calloc(NE, sizeof(int));
    ev = calloc(NE, sizeof(int));
    bdeg = calloc((size_t)CAP, sizeof(int));
    badj = calloc(NE, sizeof(int));
    beu = calloc(NE, sizeof(int));
    bev = calloc(NE, sizeof(int));
    side = malloc(sizeof(int) * (size_t)CAP);
    size_t WW = (size_t)CAP * ((CAP + 63) / 64);
    RA = malloc(sizeof(uint64_t) * WW);
    RB = malloc(sizeof(uint64_t) * WW);

    int *eu0 = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *ev0 = malloc(sizeof(int) * (size_t)(m0 + 1));
    int ok = 1;
    for (int i = 0; i < m0 && ok; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { ok = 0; break; }
        eu0[i] = u; ev0[i] = v;
        if (deg[u] >= DEG || deg[v] >= DEG) { ok = 0; break; }
        adj[(size_t)u * DEG + deg[u]++] = v;
        adj[(size_t)v * DEG + deg[v]++] = u;
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    /* Bipartition by BFS. */
    for (int v = 0; v < n0; v++) side[v] = -1;
    int *stack = malloc(sizeof(int) * (size_t)(n0 + 1));
    for (int s = 0; s < n0 && ok; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int sp = 0;
        stack[sp++] = s;
        while (sp > 0 && ok) {
            int u = stack[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[(size_t)u * DEG + k];
                if (side[v] == -1) {
                    side[v] = 1 - side[u];
                    stack[sp++] = v;
                } else if (side[v] == side[u]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    free(stack);
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    /* Reset degrees and rebuild oriented edge list (A -> B). */
    memset(deg, 0, sizeof(int) * (size_t)CAP);
    for (int i = 0; i < m0; i++) {
        int u = eu0[i], v = ev0[i];
        int a = side[u] == 0 ? u : v;
        int b = side[u] == 0 ? v : u;
        eu[i] = a;
        ev[i] = b;
        adj[(size_t)a * DEG + deg[a]++] = b;
        adj[(size_t)b * DEG + deg[b]++] = a;
    }
    free(eu0);
    free(ev0);
    n = n0;
    m = m0;

    long long bad = eval_bad();
    while (bad > 0 && elapsed() < DL) {
        bad = anneal(bad, ATT_ITERS * 4);
    }
    if (bad > 0) {
        printf("0 0\n");
        return 0;
    }
    copy_cur_to_base();

    while (elapsed() < DL) {
        copy_base_to_cur();
        if (!augment()) break;
        long long c = eval_bad();
        c = anneal(c, ATT_ITERS);
        if (c == 0) copy_cur_to_base();
    }

    printf("%d %d\n", bn, bm);
    for (int i = 0; i < bm; i++)
        printf("%d %d\n", beu[i], bev[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()

    def left():
        return 0.9 * time_limit - (time.monotonic() - start) - 1.5

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
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

    if best_n >= lib.moore_bound(d, D):
        return best

    # Stage 1: structured lift search (finds the large graphs).
    t1 = left()
    if t1 >= 2.0:
        budget = 0.6 * t1
        try:
            out = lib.run_c(C_LIFT, [d, D, seed, f"{budget:.2f}", best_n],
                            timeout=budget + 8.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    # Stage 2: unstructured growth and repair from the best valid graph so far.
    t2 = left()
    if t2 >= 2.0:
        try:
            out = lib.run_c(C_GROW, [d, D, seed + 1, f"{t2:.2f}"],
                            stdin_graph=best, timeout=t2 + 8.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
