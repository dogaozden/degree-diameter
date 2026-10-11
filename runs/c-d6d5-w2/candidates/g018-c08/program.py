import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Engine A: voltage lifts of semidirect products Z_m x| Z_k2 over a base of
# K A-vertices and K B-vertices, searched by simulated annealing with breakout
# weights and an elite pool (iterated local search). Unchanged from the parent.
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
# Engine B (new, different construction): direct search on the bipartite graph.
#
# Keeps a d-regular bipartite graph with N vertices per side (A = 0..N-1,
# B = N..2N-1). Moves are degree-preserving edge switches
# (a1-b1, a2-b2) -> (a1-b2, a2-b1), scored by the number of unordered vertex
# pairs at distance > D, computed with bitset BFS. Simulated annealing with
# reheating cycles runs on this cost. Whenever the cost reaches 0, the graph is
# valid and is recorded; then one new A/B vertex pair is added (each new vertex
# takes d edges by subdividing d existing edges), and annealing repairs the
# diameter. The start is a regular graph from stdin (for example a lift) or
# K_{d,d}.
# ----------------------------------------------------------------------------

GROW_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NCAP_MAX 2500
#define CYC 30000
#define THI 2.0
#define TLO 0.05

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

static int DEG, DIAM, N, NCAP, WCAP;
static int *nA, *nB, *usedB, *perm, *pk_a, *pk_i, *pk_b, *best_nA;
static unsigned char *adjM;
static uint64_t *bsA, *bsB;
static int best_N = 0;

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int find_in(const int *row, int val) {
    for (int j = 0; j < DEG; j++)
        if (row[j] == val) return j;
    return -1;
}

/* Swap the B-targets of slots (a1,i1) and (a2,i2). Applying it twice restores the graph. */
static void swap_targets(int a1, int i1, int a2, int i2) {
    int b1 = nA[a1 * DEG + i1], b2 = nA[a2 * DEG + i2];
    nA[a1 * DEG + i1] = b2;
    nA[a2 * DEG + i2] = b1;
    int j = find_in(nB + (size_t)b1 * DEG, a1);
    nB[b1 * DEG + j] = a2;
    int k = find_in(nB + (size_t)b2 * DEG, a2);
    nB[b2 * DEG + k] = a1;
    adjM[a1 * NCAP + b1] = 0;
    adjM[a2 * NCAP + b2] = 0;
    adjM[a1 * NCAP + b2] = 1;
    adjM[a2 * NCAP + b1] = 1;
}

/* Number of unordered vertex pairs at distance > DIAM. Zero iff the graph is valid. */
static long long eval_cost(void) {
    int V = 2 * N, W = (V + 63) / 64;
    uint64_t *cur = bsA, *nxt = bsB, *tp;
    for (int v = 0; v < V; v++) {
        uint64_t *row = cur + (size_t)v * WCAP;
        for (int w = 0; w < W; w++) row[w] = 0;
        row[v >> 6] |= 1ULL << (v & 63);
    }
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < V; v++) {
            uint64_t *o = nxt + (size_t)v * WCAP;
            const uint64_t *c = cur + (size_t)v * WCAP;
            for (int w = 0; w < W; w++) o[w] = c[w];
            if (v < N) {
                const int *row = nA + (size_t)v * DEG;
                for (int i = 0; i < DEG; i++) {
                    const uint64_t *s = cur + (size_t)(N + row[i]) * WCAP;
                    for (int w = 0; w < W; w++) o[w] |= s[w];
                }
            } else {
                const int *row = nB + (size_t)(v - N) * DEG;
                for (int i = 0; i < DEG; i++) {
                    const uint64_t *s = cur + (size_t)row[i] * WCAP;
                    for (int w = 0; w < W; w++) o[w] |= s[w];
                }
            }
        }
        tp = cur; cur = nxt; nxt = tp;
    }
    long long tot = 0;
    for (int v = 0; v < V; v++) {
        const uint64_t *c = cur + (size_t)v * WCAP;
        int cntb = 0;
        for (int w = 0; w < W; w++) cntb += popc(c[w]);
        tot += V - cntb;
    }
    return tot / 2;
}

/* K_{DEG,DEG} as the starting graph (valid for DIAM >= 2). */
static void init_kdd(void) {
    memset(adjM, 0, (size_t)NCAP * NCAP);
    N = DEG;
    for (int a = 0; a < N; a++)
        for (int i = 0; i < DEG; i++) {
            nA[a * DEG + i] = i;
            nB[a * DEG + i] = i;
            adjM[a * NCAP + i] = 1;
        }
}

/* Read a regular bipartite start graph with A = 0..n/2-1 and B = n/2..n-1. */
static int load_start(int n, int m) {
    int Ns = n / 2;
    int ok = (n % 2 == 0) && Ns >= 1 && Ns + 2 <= NCAP && m == Ns * DEG;
    int *cA = calloc(NCAP, sizeof(int));
    int *cB = calloc(NCAP, sizeof(int));
    memset(adjM, 0, (size_t)NCAP * NCAP);
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (!ok) continue;
        if (u > v) { int t = u; u = v; v = t; }
        if (!(u >= 0 && u < Ns && v >= Ns && v < n)) { ok = 0; continue; }
        int a = u, b = v - Ns;
        if (adjM[a * NCAP + b] || cA[a] >= DEG || cB[b] >= DEG) { ok = 0; continue; }
        adjM[a * NCAP + b] = 1;
        nA[a * DEG + cA[a]++] = b;
        nB[b * DEG + cB[b]++] = a;
    }
    if (ok)
        for (int x = 0; x < Ns; x++)
            if (cA[x] != DEG || cB[x] != DEG) { ok = 0; break; }
    free(cA);
    free(cB);
    if (!ok) {
        memset(adjM, 0, (size_t)NCAP * NCAP);
        return 0;
    }
    N = Ns;
    return 1;
}

/* Add one A vertex and one B vertex. Each new vertex takes DEG edges by subdividing
   DEG old edges (a_k, b_k) with pairwise distinct a_k and b_k. Returns 0 if no plan exists;
   the graph is unchanged in that case. */
static int grow(void) {
    if (N + 1 > NCAP) return 0;
    int old = N;
    for (int t = 0; t < old; t++) { perm[t] = t; usedB[t] = 0; }
    for (int t = old - 1; t > 0; t--) {
        int j = rnd_int(t + 1);
        int tmp = perm[t]; perm[t] = perm[j]; perm[j] = tmp;
    }
    int np = 0;
    for (int t = 0; t < old && np < DEG; t++) {
        int a = perm[t];
        int s = rnd_int(DEG);
        for (int q = 0; q < DEG; q++) {
            int i = (s + q) % DEG;
            int b = nA[a * DEG + i];
            if (usedB[b]) continue;
            usedB[b] = 1;
            pk_a[np] = a; pk_i[np] = i; pk_b[np] = b;
            np++;
            break;
        }
    }
    if (np < DEG) return 0;
    int na = old, nb = old;
    N = old + 1;
    for (int k = 0; k < DEG; k++) {
        int a = pk_a[k], i = pk_i[k], b = pk_b[k];
        nA[a * DEG + i] = nb;
        int j = find_in(nB + (size_t)b * DEG, a);
        nB[b * DEG + j] = na;
        adjM[a * NCAP + b] = 0;
        adjM[a * NCAP + nb] = 1;
        adjM[na * NCAP + b] = 1;
        nA[na * DEG + k] = b;
        nB[nb * DEG + k] = a;
    }
    return 1;
}

static void record(void) {
    if (N <= best_N) return;
    memcpy(best_nA, nA, sizeof(int) * (size_t)N * DEG);
    best_N = N;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit   (stdin: optional start graph)\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    if (DEG < 2 || DEG > 64 || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int hn = 0, hm = 0;
    if (scanf("%d %d", &hn, &hm) != 2) { hn = 0; hm = 0; }
    if (hn > 2 * NCAP_MAX) { hn = 0; hm = 0; }

    double ms = 0.0, p = 1.0;
    for (int i = 0; i < DIAM; i++) {
        ms += p;
        p *= (DEG - 1);
        if (ms > 1e7) break;
    }
    long long cap = (ms < NCAP_MAX) ? (long long)ms : NCAP_MAX;
    cap += 2;
    if (hn / 2 + 2 > cap) cap = hn / 2 + 2;
    if (DEG + 2 > cap) cap = DEG + 2;
    if (cap > NCAP_MAX + 2) cap = NCAP_MAX + 2;
    NCAP = (int)cap;
    WCAP = (2 * NCAP + 63) / 64;

    nA = malloc(sizeof(int) * (size_t)NCAP * DEG);
    nB = malloc(sizeof(int) * (size_t)NCAP * DEG);
    best_nA = malloc(sizeof(int) * (size_t)NCAP * DEG);
    usedB = malloc(sizeof(int) * (size_t)NCAP);
    perm = malloc(sizeof(int) * (size_t)NCAP);
    pk_a = malloc(sizeof(int) * (size_t)DEG);
    pk_i = malloc(sizeof(int) * (size_t)DEG);
    pk_b = malloc(sizeof(int) * (size_t)DEG);
    adjM = calloc((size_t)NCAP * NCAP, 1);
    bsA = calloc((size_t)2 * NCAP * WCAP, sizeof(uint64_t));
    bsB = calloc((size_t)2 * NCAP * WCAP, sizeof(uint64_t));

    init_kdd();
    record();
    if (hn > 0) {
        if (!load_start(hn, hm)) init_kdd();
    }

    long long cost = eval_cost();
    long long it = 0;
    int cyc = 0;
    for (;;) {
        if ((it & 127) == 0 && elapsed() > DEADLINE) break;
        it++;
        if (cost == 0) {
            record();
            if (N >= NCAP) break;
            if (grow()) {
                cost = eval_cost();
                cyc = 0;
                continue;
            }
            /* Could not add a vertex pair: shake the valid graph with one random switch. */
            int a1 = rnd_int(N), i1 = rnd_int(DEG), a2 = rnd_int(N), i2 = rnd_int(DEG);
            int b1 = nA[a1 * DEG + i1], b2 = nA[a2 * DEG + i2];
            if (a1 != a2 && b1 != b2 && !adjM[a1 * NCAP + b2] && !adjM[a2 * NCAP + b1]) {
                swap_targets(a1, i1, a2, i2);
                cost = eval_cost();
            }
            continue;
        }
        double T = THI * pow(TLO / THI, (double)cyc / CYC);
        if (++cyc >= CYC) cyc = 0;
        int a1 = rnd_int(N), i1 = rnd_int(DEG), a2 = rnd_int(N), i2 = rnd_int(DEG);
        int b1 = nA[a1 * DEG + i1], b2 = nA[a2 * DEG + i2];
        if (a1 == a2 || b1 == b2 || adjM[a1 * NCAP + b2] || adjM[a2 * NCAP + b1]) continue;
        swap_targets(a1, i1, a2, i2);
        long long nc = eval_cost();
        if (nc <= cost || rnd_unit() < exp(-(double)(nc - cost) / T)) {
            cost = nc;
        } else {
            swap_targets(a1, i1, a2, i2);
        }
    }

    printf("%d %d\n", 2 * best_N, best_N * DEG);
    for (int a = 0; a < best_N; a++)
        for (int i = 0; i < DEG; i++)
            printf("%d %d\n", a, best_N + best_nA[a * DEG + i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python helpers and driver.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _halves_regular(n, edges, d):
    """True if the graph is d-regular with every edge from the first half to the second half."""
    if n % 2:
        return False
    half = n // 2
    deg = [0] * n
    for u, v in edges:
        a, b = min(u, v), max(u, v)
        if not (a < half <= b):
            return False
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        cyc = [(i, (i + 1) % n) for i in range(n)]
        if lib.is_valid(n, cyc, d, D):
            return n, cyc
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2 and optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    pg = _best_pg(d)
    if pg is not None:
        consider(*pg)

    # Already at the Moore bound: nothing larger is possible.
    if best[0] >= lib.moore_bound(d, D):
        return best

    def left():
        # Margin for process start, the cached compile step, parsing and validation.
        return 0.92 * time_limit - (time.monotonic() - start) - 1.5

    # Phase A: the lift search (proven record family) gets the larger share.
    budget_a = 0.6 * left()
    if budget_a >= 1.0:
        try:
            out = lib.run_c(LIFT_SOURCE, [d, D, seed, f"{budget_a:.2f}", best[0]],
                            timeout=budget_a + 8.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    # Phase B: grow the best regular graph found so far by adding vertex pairs and repairing
    # the diameter by edge-switch annealing. The result is kept only if it validates.
    budget_b = left()
    if budget_b >= 1.0:
        stdin = best if _halves_regular(best[0], best[1], d) else None
        try:
            out = lib.run_c(GROW_SOURCE, [d, D, seed, f"{budget_b:.2f}"],
                            stdin_graph=stdin, timeout=budget_b + 8.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
