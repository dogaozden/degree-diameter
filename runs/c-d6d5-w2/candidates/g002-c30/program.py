import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Phase 1 engine: voltage lifts of semidirect products Z_m x| Z_k2 over a base
# of K A-vertices and K B-vertices, searched by simulated annealing with
# breakout weights and an elite pool (iterated local search).
#
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart t = (i, j, s) joins
# A_i,g to B_j,g*s for all g. Each layer is a permutation, so every vertex
# has degree DEG.
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
# Phase 2 engine (new construction): grow-and-repair on the raw edge set.
#
# Input: a d-regular bipartite graph with diameter <= D. Each attempt adds two
# vertices a (A-side) and b (B-side). Pick DEG edges (x_i, y_i) that are
# removed and replaced by a-y_i and b-x_i, which keeps every degree at DEG.
# Then simulated annealing on double edge swaps (x1,y1),(x2,y2) -> (x1,y2),(x2,y1),
# which preserve regularity and bipartiteness. Cost = ordered pairs at distance
# > D, computed with bitset BFS. On cost 0 the graph is saved and growth continues.
# ----------------------------------------------------------------------------

C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define CAPE 400000
#define ITERS 40000
#define THI 3.0
#define TLO 0.2

static struct timespec T0;
static double DEADLINE;
static uint64_t rs[2];

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

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

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int DEG, DIAM, N, E;
static int *eu, *ev;           /* edge e joins A-vertex eu[e] and B-vertex ev[e] */
static int *bestEu, *bestEv;
static int bestN, bestE;
static int *deg, *adj;
static uint64_t *bufA, *bufB;
static int W;

static void ensure_arrays(void) {
    W = (N + 63) / 64;
    size_t bits = (size_t)N * (size_t)W;
    bufA = realloc(bufA, sizeof(uint64_t) * bits);
    bufB = realloc(bufB, sizeof(uint64_t) * bits);
    deg = realloc(deg, sizeof(int) * (size_t)N);
    adj = realloc(adj, sizeof(int) * (size_t)N * (size_t)DEG);
}

/* Number of ordered pairs (u,v) at distance > DIAM. Zero iff the graph is valid. */
static long long eval_cost(void) {
    int n = N, w = W;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(deg, 0, sizeof(int) * (size_t)n);
    for (int e = 0; e < E; e++) {
        int x = eu[e], y = ev[e];
        adj[(size_t)x * DEG + deg[x]++] = y;
        adj[(size_t)y * DEG + deg[y]++] = x;
    }
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)w);
    for (int v = 0; v < n; v++) cur[(size_t)v * w + (v >> 6)] |= 1ULL << (v & 63);
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * w;
            const uint64_t *src = cur + (size_t)v * w;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)w);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *s2 = cur + (size_t)adj[(size_t)v * DEG + k] * (size_t)w;
                for (int i = 0; i < w; i++) dst[i] |= s2[i];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *r = cur + (size_t)v * w;
        for (int i = 0; i < w; i++) c += popc(r[i]);
        bad += n - c;
    }
    return bad;
}

static int has_edge(int x, int y) {
    for (int e = 0; e < E; e++)
        if (eu[e] == x && ev[e] == y) return 1;
    return 0;
}

/* Add vertices a = N (A-side) and b = N+1 (B-side), keeping all degrees at DEG. */
static int grow_two(void) {
    int E0 = E, a = N, b = N + 1;
    if (E0 + DEG + 4 >= CAPE) return 0;
    int *pk = calloc((size_t)E0, sizeof(int));
    int *px = malloc(sizeof(int) * (size_t)DEG);
    int *py = malloc(sizeof(int) * (size_t)DEG);
    int *am = calloc((size_t)N + 2, sizeof(int));  /* B-vertices already joined to a */
    int *bm = calloc((size_t)N + 2, sizeof(int));  /* A-vertices already joined to b */
    int got = 0, ok = 1;
    long long tries = 0;
    while (got < DEG) {
        if (++tries > 2000000LL) { ok = 0; break; }
        int e = rnd_int(E0);
        if (pk[e]) continue;
        int x = eu[e], y = ev[e];
        if (am[y] || bm[x]) continue;
        pk[e] = 1; am[y] = 1; bm[x] = 1;
        px[got] = x; py[got] = y;
        got++;
    }
    if (ok) {
        int w = 0;
        for (int e = 0; e < E0; e++) {
            if (!pk[e]) {
                eu[w] = eu[e];
                ev[w] = ev[e];
                w++;
            }
        }
        for (int i = 0; i < DEG; i++) {
            eu[w] = a; ev[w] = py[i]; w++;
            eu[w] = px[i]; ev[w] = b; w++;
        }
        E = w;
        N += 2;
    }
    free(pk); free(px); free(py); free(am); free(bm);
    return ok;
}

/* Simulated annealing on double edge swaps. Returns 0 as soon as the cost hits 0. */
static long long anneal(int iters) {
    long long cur = eval_cost();
    if (cur == 0) return 0;
    for (int it = 0; it < iters; it++) {
        if ((it & 127) == 0 && elapsed() > DEADLINE) break;
        if (E < 2) break;
        int e1 = rnd_int(E), e2 = rnd_int(E);
        if (e1 == e2) continue;
        int x1 = eu[e1], y1 = ev[e1], x2 = eu[e2], y2 = ev[e2];
        if (x1 == x2 || y1 == y2) continue;
        if (has_edge(x1, y2) || has_edge(x2, y1)) continue;
        double temp = THI * pow(TLO / THI, (double)it / (double)iters);
        ev[e1] = y2;
        ev[e2] = y1;
        long long c2 = eval_cost();
        if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / temp)) {
            cur = c2;
            if (cur == 0) return 0;
        } else {
            ev[e1] = y1;
            ev[e2] = y2;
        }
    }
    return cur;
}

static void save_best(void) {
    bestN = N;
    bestE = E;
    memcpy(bestEu, eu, sizeof(int) * (size_t)E);
    memcpy(bestEv, ev, sizeof(int) * (size_t)E);
}

static void restore_best(void) {
    N = bestN;
    E = bestE;
    memcpy(eu, bestEu, sizeof(int) * (size_t)E);
    memcpy(ev, bestEv, sizeof(int) * (size_t)E);
    ensure_arrays();
}

#define FAIL do { printf("0 0\n"); return 0; } while (0)

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) FAIL;
    if (DEG < 1 || DIAM < 1 || n < 2 || m < 0 || m > CAPE / 4) FAIL;
    if ((long long)n * DEG != 2LL * m) FAIL;

    int *ux = malloc(sizeof(int) * (size_t)m + 4);
    int *vx = malloc(sizeof(int) * (size_t)m + 4);
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &ux[i], &vx[i]) != 2) FAIL;
        if (ux[i] < 0 || ux[i] >= n || vx[i] < 0 || vx[i] >= n || ux[i] == vx[i]) FAIL;
    }

    int *dg = calloc((size_t)n, sizeof(int));
    for (int i = 0; i < m; i++) { dg[ux[i]]++; dg[vx[i]]++; }
    for (int v = 0; v < n; v++) if (dg[v] != DEG) FAIL;

    int *nb = malloc(sizeof(int) * (size_t)n * (size_t)DEG);
    int *fill = calloc((size_t)n, sizeof(int));
    for (int i = 0; i < m; i++) {
        int u = ux[i], v = vx[i];
        nb[(size_t)u * DEG + fill[u]++] = v;
        nb[(size_t)v * DEG + fill[v]++] = u;
    }
    for (int v = 0; v < n; v++)
        for (int k = 0; k < DEG; k++)
            for (int j = k + 1; j < DEG; j++)
                if (nb[(size_t)v * DEG + k] == nb[(size_t)v * DEG + j]) FAIL;

    int *col = malloc(sizeof(int) * (size_t)n);
    int *stk = malloc(sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int k = 0; k < DEG; k++) {
                int w = nb[(size_t)u * DEG + k];
                if (col[w] == -1) {
                    col[w] = 1 - col[u];
                    stk[sp++] = w;
                } else if (col[w] == col[u]) {
                    FAIL;
                }
            }
        }
    }

    eu = malloc(sizeof(int) * CAPE);
    ev = malloc(sizeof(int) * CAPE);
    bestEu = malloc(sizeof(int) * CAPE);
    bestEv = malloc(sizeof(int) * CAPE);
    N = n;
    E = m;
    for (int i = 0; i < m; i++) {
        if (col[ux[i]] == 0) { eu[i] = ux[i]; ev[i] = vx[i]; }
        else                 { eu[i] = vx[i]; ev[i] = ux[i]; }
    }
    ensure_arrays();
    if (eval_cost() != 0) FAIL;
    save_best();

    while (elapsed() < DEADLINE) {
        restore_best();
        if (!grow_two()) continue;
        ensure_arrays();
        long long c = anneal(ITERS);
        if (c == 0) save_best();
    }

    printf("%d %d\n", bestN, bestE);
    for (int e = 0; e < bestE; e++)
        printf("%d %d\n", bestEu[e], bestEv[e]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families (Python).
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


def _regular(n, edges, d):
    """True if every vertex of the graph has degree exactly d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


# ----------------------------------------------------------------------------
# Driver: baselines, then phase 1 (group-lift annealer), then phase 2 (grow-and-repair).
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    def elapsed():
        return time.monotonic() - start

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
        for builder in (_best_pg, _araujo):
            try:
                g = builder(d)
                if g is not None:
                    consider(g[0], g[1])
            except Exception:
                pass

    if D >= 4 and elapsed() < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Phase 1: group-lift annealer, about half of the search budget.
    # Its C deadline counts from process start, so compile time and parsing get a margin.
    room = 0.85 * time_limit - elapsed() - 2.0
    if room >= 2.0:
        p1 = 0.5 * room
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{p1:.2f}", best_n],
                            timeout=min(p1 + 3.0, time_limit - elapsed() - 1.5))
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    # Phase 2: grow the current best regular graph by two vertices at a time,
    # repairing with edge-swap annealing. Only regular inputs are accepted.
    p2 = 0.85 * time_limit - elapsed() - 1.5
    if p2 >= 2.0 and _regular(best[0], best[1], d):
        try:
            out = lib.run_c(C_GROW, [d, D, seed, f"{p2:.2f}"], stdin_graph=best,
                            timeout=min(p2 + 3.0, time_limit - elapsed() - 1.0))
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
