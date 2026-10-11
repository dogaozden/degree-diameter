import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Engine 1 (lift search): voltage lifts of semidirect products Z_m x| Z_k2 over
# a base of K A-vertices and K B-vertices, searched by simulated annealing with
# breakout weights and an elite-pool iterated local search.
# ----------------------------------------------------------------------------

LIFT_C_SOURCE = r"""
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
# Engine 2 (unstructured search): fixed-degree bipartite graphs with N vertices
# per side, no group structure. Moves are 2-switches (degree- and bipartition-
# preserving). Cost = number of ordered vertex pairs farther apart than D,
# computed with bitset ball expansion. Simulated annealing; whenever the cost
# reaches 0 the graph is recorded and grown by one vertex per side (remove d
# disjoint edges, attach the two new vertices to their endpoints).
#
# Input (optional stdin): "n m" + m edges, with side A = ids 0..n/2-1 and side B =
# ids n/2..n-1, d-regular. Otherwise a random d-regular graph of size n0 is built.
# Output: best valid graph found (cost 0), or "0 0".
# ----------------------------------------------------------------------------

SA_C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 2000
#define STAGE_LEN 30000
#define T_HI 3.0
#define T_LO 0.2

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

static int DEG, DIAM, N, BEST_N;
static int *adj, *bestadj, *cnt;
static uint64_t *cur, *nxt;

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void alloc_all(void) {
    size_t V = 2 * NMAX;
    size_t WM = (V + 63) / 64;
    adj = malloc(sizeof(int) * V * (size_t)DEG);
    bestadj = malloc(sizeof(int) * V * (size_t)DEG);
    cnt = malloc(sizeof(int) * V);
    cur = malloc(sizeof(uint64_t) * V * WM);
    nxt = malloc(sizeof(uint64_t) * V * WM);
}

/* Number of ordered pairs (u,v) with dist(u,v) > DIAM (including unreachable). */
static long long eval_cost(void) {
    int V = 2 * N;
    int W = (V + 63) / 64;
    memset(cur, 0, sizeof(uint64_t) * (size_t)V * W);
    for (int v = 0; v < V; v++)
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < V; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            const int *av = adj + (size_t)v * DEG;
            for (int k = 0; k < DEG; k++) {
                const uint64_t *su = cur + (size_t)av[k] * W;
                for (int w = 0; w < W; w++) dst[w] |= su[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long sum = 0;
    for (int v = 0; v < V; v++) {
        const uint64_t *src = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) sum += popc64(src[w]);
    }
    return (long long)V * V - sum;
}

static void record_best(void) {
    memcpy(bestadj, adj, sizeof(int) * (size_t)(2 * N) * DEG);
    BEST_N = N;
}

static int has_edge(int a, int b) {
    const int *av = adj + (size_t)a * DEG;
    for (int k = 0; k < DEG; k++)
        if (av[k] == b) return 1;
    return 0;
}

static void replace_in(int v, int oldu, int newu) {
    int *av = adj + (size_t)v * DEG;
    for (int k = 0; k < DEG; k++)
        if (av[k] == oldu) { av[k] = newu; return; }
}

/* Remove (x1,y1),(x2,y2) and add (x1,y2),(x2,y1). x's are side A, y's side B. */
static void sw(int x1, int y1, int x2, int y2) {
    replace_in(x1, y1, y2);
    replace_in(x2, y2, y1);
    replace_in(y1, x1, x2);
    replace_in(y2, x2, x1);
}

static int propose(int *x1, int *y1, int *x2, int *y2) {
    int a1 = rnd_int(N), k1 = rnd_int(DEG);
    int a2 = rnd_int(N), k2 = rnd_int(DEG);
    if (a1 == a2) return 0;
    int b1 = adj[(size_t)a1 * DEG + k1];
    int b2 = adj[(size_t)a2 * DEG + k2];
    if (b1 == b2) return 0;
    if (has_edge(a1, b2) || has_edge(a2, b1)) return 0;
    *x1 = a1; *y1 = b1; *x2 = a2; *y2 = b2;
    return 1;
}

static int random_init(int n0) {
    N = n0;
    int *perm = malloc(sizeof(int) * (size_t)N);
    for (int v = 0; v < 2 * N; v++) cnt[v] = 0;
    int ok_all = 1;
    for (int l = 0; l < DEG && ok_all; l++) {
        int ok = 0;
        for (int tr = 0; tr < 200000 && !ok; tr++) {
            for (int i = 0; i < N; i++) perm[i] = i;
            for (int i = N - 1; i > 0; i--) {
                int j = rnd_int(i + 1);
                int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
            }
            ok = 1;
            for (int a = 0; a < N && ok; a++) {
                int b = N + perm[a];
                for (int k = 0; k < cnt[a]; k++)
                    if (adj[(size_t)a * DEG + k] == b) { ok = 0; break; }
            }
            if (ok) {
                for (int a = 0; a < N; a++) {
                    int b = N + perm[a];
                    adj[(size_t)a * DEG + cnt[a]++] = b;
                    adj[(size_t)b * DEG + cnt[b]++] = a;
                }
            }
        }
        if (!ok) ok_all = 0;
    }
    free(perm);
    return ok_all;
}

static int read_start(void) {
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || m <= 0 || (n & 1)) return 0;
    int Nn = n / 2;
    if (Nn > NMAX - 1 || Nn < DEG || m != Nn * DEG) return 0;
    for (int v = 0; v < n; v++) cnt[v] = 0;
    int good = 1;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (!good) continue;
        if (u > v) { int t = u; u = v; v = t; }
        if (u < 0 || u >= Nn || v < Nn || v >= n) { good = 0; continue; }
        if (cnt[u] >= DEG || cnt[v] >= DEG) { good = 0; continue; }
        int dup = 0;
        for (int k = 0; k < cnt[u]; k++)
            if (adj[(size_t)u * DEG + k] == v) { dup = 1; break; }
        if (dup) { good = 0; continue; }
        adj[(size_t)u * DEG + cnt[u]++] = v;
        adj[(size_t)v * DEG + cnt[v]++] = u;
    }
    if (!good) return 0;
    for (int v = 0; v < n; v++)
        if (cnt[v] != DEG) return 0;
    N = Nn;
    return 1;
}

/* Add one vertex to each side: remove DEG disjoint edges (ra_i, rb_i), then join
   the new A vertex N0 to all rb_i and the new B vertex N0 to all ra_i. */
static int grow(void) {
    int N0 = N;
    int *remB = malloc(sizeof(int) * (size_t)N0);
    int *ra = malloc(sizeof(int) * (size_t)DEG);
    int *rb = malloc(sizeof(int) * (size_t)DEG);
    char *usedA = calloc((size_t)N0, 1);
    char *usedB = calloc((size_t)N0, 1);
    int rem = 0;
    for (int a = 0; a < N0; a++) remB[a] = -1;
    for (int tr = 0; tr < 100000 && rem < DEG; tr++) {
        int a = rnd_int(N0), k = rnd_int(DEG);
        int b = adj[(size_t)a * DEG + k] - N0;
        if (usedA[a] || usedB[b]) continue;
        usedA[a] = 1; usedB[b] = 1;
        ra[rem] = a; rb[rem] = b; remB[a] = b;
        rem++;
    }
    int ok = (rem == DEG);
    if (ok) {
        int N1 = N0 + 1;
        int E = N1 * DEG;
        int *pa = malloc(sizeof(int) * (size_t)E);
        int *pj = malloc(sizeof(int) * (size_t)E);
        int ne = 0;
        for (int a = 0; a < N0; a++)
            for (int k = 0; k < DEG; k++) {
                int b = adj[(size_t)a * DEG + k] - N0;
                if (remB[a] == b) continue;
                pa[ne] = a; pj[ne] = b; ne++;
            }
        for (int i = 0; i < DEG; i++) {
            pa[ne] = N0; pj[ne] = rb[i]; ne++;
            pa[ne] = ra[i]; pj[ne] = N0; ne++;
        }
        N = N1;
        for (int v = 0; v < 2 * N; v++) cnt[v] = 0;
        for (int e = 0; e < ne; e++) {
            int a = pa[e], b = N + pj[e];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
        free(pa); free(pj);
    }
    free(remB); free(ra); free(rb); free(usedA); free(usedB);
    return ok;
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
    int n0 = argc > 5 ? atoi(argv[5]) : 0;
    if (DEG < 2 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);
    alloc_all();
    BEST_N = 0;

    if (!read_start()) {
        if (n0 < DEG) n0 = DEG;
        if (n0 > NMAX - 1) n0 = NMAX - 1;
        if (!random_init(n0)) {
            printf("0 0\n");
            return 0;
        }
    }

    long long cost = eval_cost();
    if (cost == 0) record_best();
    int it = 0;
    while (elapsed() < DEADLINE) {
        if (cost == 0) {
            record_best();
            if (N + 1 > NMAX || !grow()) break;
            cost = eval_cost();
            it = 0;
            continue;
        }
        double frac = (double)(it % STAGE_LEN) / (double)STAGE_LEN;
        double temp = T_HI * pow(T_LO / T_HI, frac);
        it++;
        int x1, y1, x2, y2;
        if (!propose(&x1, &y1, &x2, &y2)) continue;
        sw(x1, y1, x2, y2);
        long long nc = eval_cost();
        if (nc <= cost || rnd_unit() < exp(-(double)(nc - cost) / temp)) {
            cost = nc;
            if (cost == 0) record_best();
        } else {
            sw(x1, y2, x2, y1);
        }
    }

    if (BEST_N > 0) {
        printf("%d %d\n", 2 * BEST_N, BEST_N * DEG);
        for (int a = 0; a < BEST_N; a++)
            for (int k = 0; k < DEG; k++)
                printf("%d %d\n", a, bestadj[(size_t)a * DEG + k]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: constructions, fallbacks and the two searches.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _regular_bipartite_relabel(n, edges, d):
    """If (n, edges) is d-regular bipartite with equal sides, return (2N, edges) with
    side A = ids 0..N-1 and side B = ids N..2N-1. Otherwise return None."""
    if n < 2 or not edges:
        return None
    adj = lib.adjacency(n, edges)
    if any(len(a) != d for a in adj):
        return None
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    A = [v for v in range(n) if color[v] == 0]
    B = [v for v in range(n) if color[v] == 1]
    if not A or len(A) != len(B):
        return None
    N = len(A)
    idx = [0] * n
    for i, v in enumerate(A):
        idx[v] = i
    for j, v in enumerate(B):
        idx[v] = N + j
    out = []
    for u, v in edges:
        if color[u] == 0:
            out.append((idx[u], idx[v]))
        else:
            out.append((idx[v], idx[u]))
    return 2 * N, out


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
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if best_n >= lib.moore_bound(d, D):
        return best

    end_target = 0.93 * time_limit

    def remaining():
        # 2.0 s reserved for a cold compile and parsing.
        return end_target - elapsed() - 2.0

    # Stage A: voltage-lift engine on about a third of the budget.
    t_a = 0.35 * remaining()
    if t_a >= 1.0:
        try:
            out = lib.run_c(LIFT_C_SOURCE, [d, D, seed, f"{t_a:.2f}", best_n],
                            timeout=t_a + 10.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    # Stage B: unstructured annealing with growth, seeded by the best graph so far
    # when that graph is d-regular bipartite.
    t_b = remaining()
    if t_b >= 1.0:
        rel = None
        try:
            rel = _regular_bipartite_relabel(best[0], best[1], d)
        except Exception:
            rel = None
        n0 = max(d, best_n // 2)
        try:
            out = lib.run_c(SA_C_SOURCE, [d, D, seed + 1, f"{t_b:.2f}", n0],
                            stdin_graph=rel, timeout=t_b + 10.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
