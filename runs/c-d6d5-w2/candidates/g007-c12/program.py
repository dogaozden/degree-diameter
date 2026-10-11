import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New two-stage pipeline for the hard targets.
#
# Stage 1 (C_LIFT): the voltage-lift annealer from the parent. It finds a
#   large lift over a semidirect group, which is still the best known source.
# Stage 2 (C_GROW): a different construction. It takes the stage-1 graph as a
#   start and grows it without any group structure. Each growth step inserts a
#   pair of new vertices x (side A) and y (side B). It removes DEG pairwise
#   vertex-disjoint edges (a_i, b_i), joins x to every b_i and y to every a_i,
#   so all degrees are preserved and the graph stays bipartite. Then it repairs
#   diameter with simulated annealing over degree- and bipartition-preserving
#   edge switches (a,b),(c,d) -> (a,d),(c,b), minimising the number of ordered
#   vertex pairs at distance > D. Each evaluation is a bitset BFS.
#
# Safety: the best valid graph seen by any stage is kept. The Python side checks
# every result with lib.is_valid and falls back to the best valid graph so far,
# so no case can return an invalid graph.
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

/* Breakout state: per-block weights, per-block uncovered counts, weighted cost of last eval. */
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

/* Returns the true cost (sum of uncovered ordered pairs over block reps).
   Sets unc[r] per block and last_w to the weighted cost. */
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

/* Random kicks: voltage changes and within-layer target swaps (both keep layers permutations). */
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

/* Annealing on the weighted cost with breakout weight bumps.
   Caller must have just called eval_cost() so that cost and last_w describe the start state.
   Best state (by true cost) goes to bestJ/bestS. Returns the best true cost. */
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
                /* Stuck: raise the weight of every block that is still uncovered. */
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

/* A zero-cost run is a valid graph: load it and emit if it beats the record. */
static void finish_run(long long bc) {
    if (bc == 0) {
        memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
        memcpy(dS, bestS, sizeof(int) * (size_t)T);
        for (int t = 0; t < T; t++) build_perm(t);
        if (2 * K * G > best_n) emit();
    }
}

/* Keep the elite pool: only positive-cost configurations, replacing the worst entry when full. */
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

/* Choose an eligible pool entry (its group order must still beat the record); best of 3 samples. */
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
            /* Iterated local search: perturb an elite configuration and re-anneal. */
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

        /* Fresh random lift over a group of order near the record. */
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

#define NMAX 4096
#define WMAX 64
#define DMAX 32
#define STALL 30000

static int DEG, DIAM, N, W, n0, n1;
static int *adj, *dg, *side, *S0, *S1;
static uint64_t *bufA, *bufB, *cur, *nxt;
static int *snapAdj, *snapDg, *validAdj, *validDg;
static int validN = 0;
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

static inline int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int v, int u) {
    for (int i = 0; i < dg[v]; i++)
        if (adj[v * DEG + i] == u) return 1;
    return 0;
}

static void rem_nb(int v, int u) {
    for (int i = 0; i < dg[v]; i++)
        if (adj[v * DEG + i] == u) {
            adj[v * DEG + i] = adj[v * DEG + dg[v] - 1];
            dg[v]--;
            return;
        }
}

static void add_nb(int v, int u) { adj[v * DEG + dg[v]++] = u; }

static void replace_nb(int v, int o, int nw) {
    for (int i = 0; i < dg[v]; i++)
        if (adj[v * DEG + i] == o) {
            adj[v * DEG + i] = nw;
            return;
        }
}

/* Number of ordered pairs at distance > DIAM (0 iff connected with diameter <= DIAM). */
static long long eval(void) {
    W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        uint64_t *c = cur + (size_t)v * W;
        memset(c, 0, sizeof(uint64_t) * (size_t)W);
        c[v >> 6] |= 1ULL << (v & 63);
    }
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < dg[v]; i++) {
                const uint64_t *t = cur + (size_t)adj[v * DEG + i] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long unc_total = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *c = cur + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(c[w]);
        unc_total += N - cnt;
    }
    return unc_total;
}

static int rand_s0(void) {
    for (int t = 0; t < 100000; t++) {
        int a = S0[rnd_int(n0)];
        if (dg[a] > 0) return a;
    }
    return -1;
}

/* Pick edges (a,b),(c,d) with a,c on side 0 and b,d on side 1 such that the switch is legal. */
static int try_move(int *oa, int *ob, int *oc, int *od) {
    for (int tr = 0; tr < 50; tr++) {
        int a = rand_s0();
        if (a < 0) return 0;
        int b = adj[a * DEG + rnd_int(dg[a])];
        int c = rand_s0();
        if (c < 0) return 0;
        int d = adj[c * DEG + rnd_int(dg[c])];
        if (a == c || b == d) continue;
        if (has_edge(a, d) || has_edge(c, b)) continue;
        *oa = a; *ob = b; *oc = c; *od = d;
        return 1;
    }
    return 0;
}

/* (a,b),(c,d) -> (a,d),(c,b). Degrees and bipartition are preserved. */
static void do_switch(int a, int b, int c, int d) {
    replace_nb(a, b, d);
    replace_nb(c, d, b);
    replace_nb(b, a, c);
    replace_nb(d, c, a);
}

/* Insert a new pair x (side 0), y (side 1) with DEG distinct edges removed and re-attached. */
static int grow(void) {
    if (N + 2 > NMAX) return 0;
    int A[DMAX], B[DMAX], k = 0;
    for (int t = 0; t < 20000 && k < DEG; t++) {
        int a = rand_s0();
        if (a < 0) break;
        int b = adj[a * DEG + rnd_int(dg[a])];
        int ok = 1;
        for (int i = 0; i < k; i++)
            if (A[i] == a || B[i] == b) { ok = 0; break; }
        if (ok) { A[k] = a; B[k] = b; k++; }
    }
    if (k < DEG) return 0;
    int x = N, y = N + 1;
    side[x] = 0; side[y] = 1;
    dg[x] = 0; dg[y] = 0;
    S0[n0++] = x;
    S1[n1++] = y;
    for (int i = 0; i < k; i++) {
        rem_nb(A[i], B[i]);
        rem_nb(B[i], A[i]);
        add_nb(A[i], y);
        add_nb(y, A[i]);
        add_nb(B[i], x);
        add_nb(x, B[i]);
    }
    N += 2;
    return 1;
}

static void saveSnap(void) {
    memcpy(snapAdj, adj, sizeof(int) * (size_t)N * DEG);
    memcpy(snapDg, dg, sizeof(int) * (size_t)N);
}

static void restoreSnap(void) {
    memcpy(adj, snapAdj, sizeof(int) * (size_t)N * DEG);
    memcpy(dg, snapDg, sizeof(int) * (size_t)N);
}

static void saveValid(void) {
    validN = N;
    memcpy(validAdj, adj, sizeof(int) * (size_t)N * DEG);
    memcpy(validDg, dg, sizeof(int) * (size_t)N);
}

/* Read "n m" and m edges into the adjacency lists. Returns 0 on any malformed input. */
static int read_graph(int *n_out) {
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || m <= 0 || n > NMAX - 2) return 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (dg[u] >= DEG || dg[v] >= DEG) return 0;
        if (has_edge(u, v)) return 0;
        add_nb(u, v);
        add_nb(v, u);
    }
    *n_out = n;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 4) {
        fprintf(stderr, "usage: prog d D seed [time_limit]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = argc > 4 ? atof(argv[4]) : 10.0;
    uint64_t sm = sd * 2654435761ULL + 777ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);
    if (DEG < 1 || DEG > DMAX || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    adj = malloc(sizeof(int) * (size_t)NMAX * DEG);
    dg = calloc(NMAX, sizeof(int));
    side = malloc(sizeof(int) * NMAX);
    S0 = malloc(sizeof(int) * NMAX);
    S1 = malloc(sizeof(int) * NMAX);
    bufA = malloc(sizeof(uint64_t) * (size_t)NMAX * WMAX);
    bufB = malloc(sizeof(uint64_t) * (size_t)NMAX * WMAX);
    snapAdj = malloc(sizeof(int) * (size_t)NMAX * DEG);
    snapDg = malloc(sizeof(int) * NMAX);
    validAdj = malloc(sizeof(int) * (size_t)NMAX * DEG);
    validDg = malloc(sizeof(int) * NMAX);
    cur = bufA;
    nxt = bufB;

    int n = 0;
    if (!read_graph(&n)) {
        printf("0 0\n");
        return 0;
    }
    N = n;

    /* Bipartition by BFS; reject non-bipartite input. */
    int *queue = malloc(sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < dg[u]; i++) {
                int w = adj[u * DEG + i];
                if (side[w] < 0) {
                    side[w] = 1 - side[u];
                    queue[qt++] = w;
                } else if (side[w] == side[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    free(queue);
    n0 = n1 = 0;
    for (int v = 0; v < n; v++) {
        if (side[v] == 0) S0[n0++] = v;
        else S1[n1++] = v;
    }
    if (n0 == 0 || n1 == 0) {
        printf("0 0\n");
        return 0;
    }

    long long cost = eval();
    saveSnap();
    long long snapCost = cost;
    int stall = 0;
    while (elapsed() < DEADLINE) {
        if (cost == 0) {
            saveValid();
            if (!grow()) break;
            cost = eval();
            saveSnap();
            snapCost = cost;
            stall = 0;
            continue;
        }
        int a, b, c, d;
        if (!try_move(&a, &b, &c, &d)) break;
        do_switch(a, b, c, d);
        long long nc = eval();
        long long delta = nc - cost;
        double temp = 2.0 * (1.0 - (double)stall / STALL) + 0.2;
        if (delta <= 0 || rnd_unit() < exp(-(double)delta / temp)) {
            cost = nc;
        } else {
            do_switch(a, d, c, b);
        }
        if (cost < snapCost) {
            snapCost = cost;
            saveSnap();
            stall = 0;
        } else if (++stall >= STALL) {
            restoreSnap();
            cost = eval();
            snapCost = cost;
            stall = 0;
        }
    }
    if (cost == 0 && validN < N) saveValid();

    if (validN <= 0) {
        printf("0 0\n");
        return 0;
    }
    long long deg_sum = 0;
    for (int v = 0; v < validN; v++) deg_sum += validDg[v];
    printf("%d %lld\n", validN, deg_sum / 2);
    for (int v = 0; v < validN; v++)
        for (int i = 0; i < validDg[v]; i++) {
            int u = validAdj[v * DEG + i];
            if (v < u) printf("%d %d\n", v, u);
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
# Driver: baselines, then stage 1 (lift annealer), then stage 2 (grow and repair).
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

    # Two C compiles (cached after the first run) plus parsing and validation.
    usable = 0.90 * time_limit - (time.monotonic() - start) - 3.0
    if usable < 2.0:
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    # Stage 1: voltage-lift annealer (the parent's best known source).
    b1 = 0.55 * usable
    try:
        out = lib.run_c(C_LIFT, [d, D, seed, f"{b1:.2f}", best_n],
                        timeout=b1 + 6.0)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except Exception:
        pass

    # Stage 2: grow the best valid graph so far by vertex insertion plus
    # edge-switch annealing. This does not use group structure.
    remaining = 0.90 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_GROW, [d, D, seed, f"{remaining:.2f}"],
                            stdin_graph=best, timeout=remaining + 6.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
