import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine. Two phases share one time budget:
#
# Phase 1 (lift search, first ~50% of the budget): voltage lifts of semidirect
# products Z_m x| Z_k2 over a base of K A-vertices and K B-vertices, searched by
# simulated annealing with breakout weights and an elite pool (ILS), as in the
# parent.
#
# Phase 2 (NEW: pair insertion + repair, the rest of the budget): take the best
# graph found so far, which has n vertices, and try to build a valid graph on
# n + 2 vertices. A new A-vertex x and a new B-vertex y are inserted by edge
# splitting: DEG-1 edges (a,b) are each replaced by (x,b) and (a,y), with all a
# and all b distinct, and then the edge (x,y) is added. Every degree becomes
# exactly DEG and the other degrees are unchanged. The diameter is usually
# broken, so degree-preserving double-edge swaps are annealed to minimise the
# number of ordered vertex pairs at distance > DIAM. Reachability uses bitsets,
# so one full cost evaluation costs roughly n * DIAM * (n/64) * DEG word ops.
# On success the graph is committed as the new base and the insertion repeats,
# so the order grows by 2 each time it succeeds.
#
# Vertices in output: A-vertex a -> a, B-vertex b -> nA + b.
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
#define RP_ITERS 2500

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
static double SA_END;
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
        if ((it & 63) == 0 && elapsed() > SA_END) break;
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

/* ------------------------------------------------------------------------
   Repair phase: insert a vertex pair by edge splitting, then anneal with
   degree-preserving double-edge swaps. Bitset BFS gives the cost.
   ------------------------------------------------------------------------ */
static int rp_bna, rp_bnb, rp_bE;
static int *rp_bA = NULL, *rp_bB = NULL;
static int rp_wna, rp_wnb, rp_wE;
static int *rp_wA = NULL, *rp_wB = NULL;
static unsigned char *rp_amat = NULL;
static int *rp_adj = NULL, *rp_deg = NULL;
static uint64_t *rp_r0 = NULL, *rp_r1 = NULL;

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void rp_free_work(void) {
    free(rp_wA); free(rp_wB); free(rp_amat); free(rp_adj); free(rp_deg);
    free(rp_r0); free(rp_r1);
    rp_wA = rp_wB = NULL;
    rp_amat = NULL;
    rp_adj = rp_deg = NULL;
    rp_r0 = rp_r1 = NULL;
}

/* Number of ordered pairs at distance > DIAM (0 means valid). A-vertex a is node a,
   B-vertex b is node rp_wna + b. */
static long long rp_cost(void) {
    int na = rp_wna, nb = rp_wnb, N = na + nb;
    int W = (N + 63) / 64;
    for (int v = 0; v < N; v++) rp_deg[v] = 0;
    for (int e = 0; e < rp_wE; e++) {
        int a = rp_wA[e], b = na + rp_wB[e];
        if (rp_deg[a] >= DEG || rp_deg[b] >= DEG) return BIGC;
        rp_adj[(size_t)a * DEG + rp_deg[a]++] = b;
        rp_adj[(size_t)b * DEG + rp_deg[b]++] = a;
    }
    uint64_t *cur = rp_r0, *nxt = rp_r1;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int k = 0; k < rp_deg[v]; k++) {
                const uint64_t *o = cur + (size_t)rp_adj[(size_t)v * DEG + k] * W;
                for (int w = 0; w < W; w++) dst[w] |= o[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long cov = 0;
    for (size_t i = 0; i < (size_t)N * W; i++) cov += popc64(cur[i]);
    return (long long)N * N - cov;
}

/* Split DEG-1 random base edges (all endpoints distinct) into a new A-vertex x and
   a new B-vertex y, then add (x, y). Degrees of x and y become exactly DEG. */
static int rp_insert(void) {
    int x = rp_bna, y = rp_bnb;
    int cap = rp_bE + DEG + 4;
    rp_wA = malloc(sizeof(int) * (size_t)cap);
    rp_wB = malloc(sizeof(int) * (size_t)cap);
    memcpy(rp_wA, rp_bA, sizeof(int) * (size_t)rp_bE);
    memcpy(rp_wB, rp_bB, sizeof(int) * (size_t)rp_bE);
    rp_wna = x + 1;
    rp_wnb = y + 1;
    rp_wE = rp_bE;
    int *uA = calloc((size_t)rp_wna, sizeof(int));
    int *uB = calloc((size_t)rp_wnb, sizeof(int));
    uA[x] = 1;
    uB[y] = 1;
    int ok = 1;
    for (int s = 0; s < DEG - 1 && ok; s++) {
        int e = -1;
        for (int tr = 0; tr < 100000; tr++) {
            int c = rnd_int(rp_bE);
            if (!uA[rp_wA[c]] && !uB[rp_wB[c]]) { e = c; break; }
        }
        if (e < 0) { ok = 0; break; }
        int a = rp_wA[e], b = rp_wB[e];
        uA[a] = 1;
        uB[b] = 1;
        rp_wA[e] = x;                                   /* edge (x, b) replaces (a, b) */
        rp_wA[rp_wE] = a; rp_wB[rp_wE] = y; rp_wE++;    /* edge (a, y) */
    }
    if (ok) { rp_wA[rp_wE] = x; rp_wB[rp_wE] = y; rp_wE++; }
    free(uA);
    free(uB);
    return ok;
}

/* Store the working graph as the new base and as the emitted best. */
static void rp_commit(void) {
    free(rp_bA); free(rp_bB);
    rp_bA = malloc(sizeof(int) * (size_t)rp_wE);
    rp_bB = malloc(sizeof(int) * (size_t)rp_wE);
    memcpy(rp_bA, rp_wA, sizeof(int) * (size_t)rp_wE);
    memcpy(rp_bB, rp_wB, sizeof(int) * (size_t)rp_wE);
    rp_bna = rp_wna;
    rp_bnb = rp_wnb;
    rp_bE = rp_wE;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)rp_wE);
    for (int i = 0; i < rp_wE; i++) {
        best_e[2 * i] = rp_wA[i];
        best_e[2 * i + 1] = rp_wna + rp_wB[i];
    }
    best_m = rp_wE;
    best_n = rp_wna + rp_wnb;
}

/* One attempt: insert a pair from the base, anneal the swaps. Returns 1 on success. */
static int rp_attempt(double end, int iters) {
    if (!rp_insert()) {
        free(rp_wA); free(rp_wB);
        rp_wA = rp_wB = NULL;
        return 0;
    }
    int na = rp_wna, nb = rp_wnb, N = na + nb;
    int W = (N + 63) / 64;
    rp_amat = calloc((size_t)na * nb, 1);
    rp_adj = malloc(sizeof(int) * (size_t)N * DEG);
    rp_deg = malloc(sizeof(int) * (size_t)N);
    rp_r0 = malloc(sizeof(uint64_t) * (size_t)N * W);
    rp_r1 = malloc(sizeof(uint64_t) * (size_t)N * W);
    for (int e = 0; e < rp_wE; e++) rp_amat[(size_t)rp_wA[e] * nb + rp_wB[e]] = 1;

    long long cur = rp_cost();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && elapsed() > end) break;
        int e1 = rnd_int(rp_wE), e2 = rnd_int(rp_wE);
        if (e1 == e2) continue;
        int a1 = rp_wA[e1], b1 = rp_wB[e1], a2 = rp_wA[e2], b2 = rp_wB[e2];
        if (a1 == a2 || b1 == b2) continue;
        if (rp_amat[(size_t)a1 * nb + b2] || rp_amat[(size_t)a2 * nb + b1]) continue;
        rp_wB[e1] = b2;
        rp_wB[e2] = b1;
        rp_amat[(size_t)a1 * nb + b1] = 0;
        rp_amat[(size_t)a2 * nb + b2] = 0;
        rp_amat[(size_t)a1 * nb + b2] = 1;
        rp_amat[(size_t)a2 * nb + b1] = 1;
        long long c2 = rp_cost();
        double temp = 3.0 * (1.0 - (double)it / iters) + 0.2;
        if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / temp)) {
            cur = c2;
        } else {
            rp_wB[e1] = b1;
            rp_wB[e2] = b2;
            rp_amat[(size_t)a1 * nb + b2] = 0;
            rp_amat[(size_t)a2 * nb + b1] = 0;
            rp_amat[(size_t)a1 * nb + b1] = 1;
            rp_amat[(size_t)a2 * nb + b2] = 1;
        }
    }
    int ok = (cur == 0);
    if (ok) rp_commit();
    rp_free_work();
    return ok;
}

static void repair_phase(double end) {
    if (best_m == 0 || DEG < 2) return;
    /* Lift outputs have two halves of equal size: A-ids first, then B-ids. */
    int h = best_n / 2;
    rp_bna = h;
    rp_bnb = best_n - h;
    rp_bE = best_m;
    rp_bA = malloc(sizeof(int) * (size_t)rp_bE);
    rp_bB = malloc(sizeof(int) * (size_t)rp_bE);
    for (int i = 0; i < rp_bE; i++) {
        int u = best_e[2 * i], v = best_e[2 * i + 1];
        if (u < h) { rp_bA[i] = u; rp_bB[i] = v - h; }
        else { rp_bA[i] = v; rp_bB[i] = u - h; }
    }
    while (elapsed() < end) rp_attempt(end, RP_ITERS);
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

    /* Phase 1 ends at half the budget; phase 2 (repair) gets the rest. */
    SA_END = (DEG >= 2) ? 0.5 * DEADLINE : DEADLINE;

    static const int kc[5] = {1, 1, 2, 2, 3};
    while (elapsed() < SA_END) {
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

    /* Phase 2: insert vertex pairs into the best graph and repair. */
    repair_phase(DEADLINE);

    if (best_m > 0) {
        printf("%d %d\n", best_n, best_m);
        if (best_e) {
            for (int i = 0; i < best_m; i++)
                printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
        }
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


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then the C search (lift annealing, then pair
# insertion with bitset repair).
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

    # Give the C search nearly all of the budget. The reserve covers the
    # one-off C compile (which runs outside the C deadline), parsing and
    # validation. Compile is about 1 s on a cold cache and is cached after.
    remaining = 0.90 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 6.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
