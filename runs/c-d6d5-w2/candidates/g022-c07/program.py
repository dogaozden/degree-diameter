import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Engine 1 (lift search): voltage lifts of semidirect products Z_m x| Z_k2 over
# a base of K A-vertices and K B-vertices, searched by simulated annealing with
# breakout weights and an elite-pool iterated local search. This is the parent
# engine, unchanged.
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
# Engine 2 (new, bold): grow-and-repair on general bipartite graphs.
#
# Starting from a valid d-regular bipartite graph, it adds one A vertex and one
# B vertex. A matching of d edges (a_k, b_k) is removed, the new A vertex x is
# joined to every b_k and the new B vertex y to every a_k. Degrees stay exactly
# d, but the diameter is usually broken. Simulated annealing then repairs it
# with 2-switches ((a1,b1),(a2,b2)) -> ((a1,b2),(a2,b1)), which keep every
# degree and the bipartition. Cost = number of ordered vertex pairs at distance
# more than DIAM. Distances come from bitset ball expansion, which is much
# faster than per-source BFS. Whenever cost reaches 0 the graph is recorded
# and the grow step repeats.
# ----------------------------------------------------------------------------

C_SWITCH = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define GROWMAX 300
#define PHASE_L 15000
#define TEMP_HI 4.0
#define TEMP_LO 0.15

static uint64_t rs[2];
static struct timespec TS0;
static double DEADLINE;
static int DEG, DIAM, N, M, CAP, WC, MCAP;
static int *ea, *eb, *pb_a, *pb_b, *best_a, *best_b, *nbr, *ncnt, *perm, *selE, *stA, *stB;
static unsigned char *mat;
static uint64_t *X, *Y;
static int bestN = 0, bestM = 0;
static int curst = 0;

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
    return (double)(ts.tv_sec - TS0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - TS0.tv_nsec);
}

static long long eval_cost(void) {
    int W = (N + 63) >> 6;
    memset(ncnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < M; e++) {
        int a = ea[e], b = eb[e];
        if (ncnt[a] < DEG) nbr[(size_t)a * DEG + ncnt[a]] = b;
        ncnt[a]++;
        if (ncnt[b] < DEG) nbr[(size_t)b * DEG + ncnt[b]] = a;
        ncnt[b]++;
    }
    memset(X, 0, sizeof(uint64_t) * (size_t)N * WC);
    for (int v = 0; v < N; v++) X[(size_t)v * WC + (v >> 6)] |= 1ULL << (v & 63);
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = Y + (size_t)v * WC;
            const uint64_t *src = X + (size_t)v * WC;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int k = 0; k < DEG; k++) {
                int u = nbr[(size_t)v * DEG + k];
                const uint64_t *s2 = X + (size_t)u * WC;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        uint64_t *tmp = X; X = Y; Y = tmp;
    }
    long long total = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *src = X + (size_t)v * WC;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += __builtin_popcountll(src[w]);
        total += N - pc;
    }
    return total;
}

static void rebuild_mat(void) {
    for (int x = 0; x < N; x++) memset(mat + (size_t)x * CAP, 0, (size_t)N);
    for (int e = 0; e < M; e++) {
        mat[(size_t)ea[e] * CAP + eb[e]] = 1;
        mat[(size_t)eb[e] * CAP + ea[e]] = 1;
    }
}

static void save_best(void) {
    bestN = N;
    bestM = M;
    memcpy(best_a, ea, sizeof(int) * (size_t)M);
    memcpy(best_b, eb, sizeof(int) * (size_t)M);
}

/* Add two vertices x (side A) and y (side B), each of degree DEG, by rerouting a matching. */
static int grow(void) {
    int ok = 0;
    for (int att = 0; att < 60 && !ok; att++) {
        for (int e = 0; e < M; e++) perm[e] = e;
        for (int e = M - 1; e > 0; e--) {
            int j = rnd_int(e + 1);
            int t = perm[e]; perm[e] = perm[j]; perm[j] = t;
        }
        curst++;
        int cnt = 0;
        for (int k = 0; k < M && cnt < DEG; k++) {
            int e = perm[k];
            if (stA[ea[e]] != curst && stB[eb[e]] != curst) {
                stA[ea[e]] = curst;
                stB[eb[e]] = curst;
                selE[cnt++] = e;
            }
        }
        if (cnt == DEG) ok = 1;
    }
    if (!ok) return 0;
    int x = N, y = N + 1;
    for (int k = 0; k < DEG; k++) {
        int e = selE[k];
        int a = ea[e], b = eb[e];
        mat[(size_t)a * CAP + b] = 0;
        mat[(size_t)b * CAP + a] = 0;
        ea[e] = x;
        eb[e] = b;
        mat[(size_t)x * CAP + b] = 1;
        mat[(size_t)b * CAP + x] = 1;
        ea[M + k] = a;
        eb[M + k] = y;
        mat[(size_t)a * CAP + y] = 1;
        mat[(size_t)y * CAP + a] = 1;
    }
    M += DEG;
    N += 2;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit  (graph on stdin)\n");
        return 1;
    }
    timespec_get(&TS0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    uint64_t sm = sd * 2654435761ULL + 777ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 < 0 || DEG < 2 || DIAM < 1)
        goto fail_empty;

    CAP = n0 + 2 * GROWMAX;
    WC = (CAP + 63) >> 6;
    MCAP = CAP * DEG / 2 + DEG + 8;

    int *eu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *deg = calloc((size_t)n0, sizeof(int));
    ea = malloc(sizeof(int) * (size_t)MCAP);
    eb = malloc(sizeof(int) * (size_t)MCAP);
    pb_a = malloc(sizeof(int) * (size_t)MCAP);
    pb_b = malloc(sizeof(int) * (size_t)MCAP);
    best_a = malloc(sizeof(int) * (size_t)MCAP);
    best_b = malloc(sizeof(int) * (size_t)MCAP);
    perm = malloc(sizeof(int) * (size_t)MCAP);
    selE = malloc(sizeof(int) * (size_t)DEG);
    nbr = malloc(sizeof(int) * (size_t)CAP * DEG);
    ncnt = calloc((size_t)CAP, sizeof(int));
    stA = calloc((size_t)CAP, sizeof(int));
    stB = calloc((size_t)CAP, sizeof(int));
    mat = calloc((size_t)CAP * CAP, 1);
    X = calloc((size_t)CAP * WC, sizeof(uint64_t));
    Y = calloc((size_t)CAP * WC, sizeof(uint64_t));
    int *col = malloc(sizeof(int) * (size_t)n0);
    int *queue = malloc(sizeof(int) * (size_t)n0);

    for (int e = 0; e < m0; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) goto fail;
        if (u < 0 || u >= n0 || v < 0 || v >= n0 || u == v) goto fail;
        if (mat[(size_t)u * CAP + v]) goto fail;
        mat[(size_t)u * CAP + v] = 1;
        mat[(size_t)v * CAP + u] = 1;
        eu[e] = u;
        ev[e] = v;
        deg[u]++;
        deg[v]++;
    }
    for (int v = 0; v < n0; v++)
        if (deg[v] != DEG) goto fail;

    /* 2-colour the graph; side A is colour 0. */
    for (int v = 0; v < n0; v++) ncnt[v] = 0;
    for (int e = 0; e < m0; e++) {
        int u = eu[e], v = ev[e];
        nbr[(size_t)u * DEG + ncnt[u]++] = v;
        nbr[(size_t)v * DEG + ncnt[v]++] = u;
    }
    for (int v = 0; v < n0; v++) col[v] = -1;
    for (int s = 0; s < n0; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int k = 0; k < DEG; k++) {
                int v = nbr[(size_t)u * DEG + k];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    queue[qt++] = v;
                } else if (col[v] == col[u]) {
                    goto fail;
                }
            }
        }
    }
    for (int e = 0; e < m0; e++) {
        if (col[eu[e]] == 0) {
            ea[e] = eu[e];
            eb[e] = ev[e];
        } else {
            ea[e] = ev[e];
            eb[e] = eu[e];
        }
    }
    N = n0;
    M = m0;
    rebuild_mat();

    long long cost = eval_cost();
    while (elapsed() < DEADLINE) {
        if (cost == 0) {
            if (N > bestN) save_best();
            if (N + 2 > CAP || !grow()) break;
            cost = eval_cost();
            continue;
        }
        /* Annealing phase from the current state. */
        long long pbest = cost;
        memcpy(pb_a, ea, sizeof(int) * (size_t)M);
        memcpy(pb_b, eb, sizeof(int) * (size_t)M);
        for (int it = 0; it < PHASE_L && cost > 0; it++) {
            if ((it & 63) == 0 && elapsed() > DEADLINE) break;
            int i = rnd_int(M), j = rnd_int(M);
            if (i == j) continue;
            int a1 = ea[i], b1 = eb[i], a2 = ea[j], b2 = eb[j];
            if (a1 == a2 || b1 == b2) continue;
            if (mat[(size_t)a1 * CAP + b2] || mat[(size_t)a2 * CAP + b1]) continue;
            mat[(size_t)a1 * CAP + b1] = 0; mat[(size_t)b1 * CAP + a1] = 0;
            mat[(size_t)a2 * CAP + b2] = 0; mat[(size_t)b2 * CAP + a2] = 0;
            mat[(size_t)a1 * CAP + b2] = 1; mat[(size_t)b2 * CAP + a1] = 1;
            mat[(size_t)a2 * CAP + b1] = 1; mat[(size_t)b1 * CAP + a2] = 1;
            eb[i] = b2;
            eb[j] = b1;
            long long c2 = eval_cost();
            long long delta = c2 - cost;
            double temp = TEMP_HI * pow(TEMP_LO / TEMP_HI, (double)it / PHASE_L);
            if (delta <= 0 || rnd_unit() < exp(-(double)delta / temp)) {
                cost = c2;
                if (cost < pbest) {
                    pbest = cost;
                    memcpy(pb_a, ea, sizeof(int) * (size_t)M);
                    memcpy(pb_b, eb, sizeof(int) * (size_t)M);
                }
            } else {
                eb[i] = b1;
                eb[j] = b2;
                mat[(size_t)a1 * CAP + b2] = 0; mat[(size_t)b2 * CAP + a1] = 0;
                mat[(size_t)a2 * CAP + b1] = 0; mat[(size_t)b1 * CAP + a2] = 0;
                mat[(size_t)a1 * CAP + b1] = 1; mat[(size_t)b1 * CAP + a1] = 1;
                mat[(size_t)a2 * CAP + b2] = 1; mat[(size_t)b2 * CAP + a2] = 1;
            }
        }
        if (cost == 0) continue;
        /* Restore the best state of this phase and reheat from it. */
        memcpy(ea, pb_a, sizeof(int) * (size_t)M);
        memcpy(eb, pb_b, sizeof(int) * (size_t)M);
        rebuild_mat();
        cost = pbest;
    }

    if (bestN > 0) {
        printf("%d %d\n", bestN, bestM);
        for (int i = 0; i < bestM; i++)
            printf("%d %d\n", best_a[i], best_b[i]);
    } else {
        printf("0 0\n");
    }
    return 0;

fail:
fail_empty:
    printf("0 0\n");
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


def _regular(n, edges, d):
    """True if every vertex of (n, edges) has degree exactly d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


# ----------------------------------------------------------------------------
# Driver: baselines, then the lift search, then grow-and-repair from the best.
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

    def spare():
        # 92% of the limit, minus 2.5 s for two possible cold compiles and parsing.
        return 0.92 * time_limit - 2.5 - (time.monotonic() - start)

    # Stage 1: lift search (parent engine) gets about 45% of the usable time.
    total = spare()
    if total >= 1.0:
        b1 = 0.45 * total
        try:
            out = lib.run_c(C_LIFT, [d, D, seed, f"{b1:.2f}", best_n],
                            timeout=b1 + 4.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Stage 2: grow-and-repair from the best valid regular graph found so far.
    rem = spare()
    if rem >= 2.0 and _regular(best[0], best[1], d):
        try:
            out = lib.run_c(C_SWITCH, [d, D, seed + 1, f"{rem:.2f}"],
                            stdin_graph=best, timeout=rem + 4.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
