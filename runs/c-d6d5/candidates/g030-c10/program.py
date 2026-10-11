import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Two-stage search for d-regular-ish bipartite graphs with diameter D.
#
# Stage 1 (mode 0): voltage lifts of semidirect products Z_m x| Z_k2 over a
# base of K A-vertices and K B-vertices, searched by simulated annealing with
# breakout weights and an elite pool (iterated local search). This is the
# parent's engine, unchanged in behaviour.
#
# Stage 2 (mode 1, NEW): unstructured repair. Start from the best graph found
# so far, which has a known A/B split. Insert one new A-vertex and one new
# B-vertex by degree-preserving edge subdivisions: each step takes an edge
# (x,y), replaces it by (x,b) and adds (a,y), so every old degree is kept and
# a, b gain DEG edges. Then anneal with degree-preserving 2-switches
# (a1-b1, a2-b2 -> a1-b2, a2-b1) on the number of ordered pairs at distance
# greater than D. Distances use bitset BFS from all vertices at once. If the
# cost reaches 0 the graph is valid and one more pair is tried. If not, the
# last valid graph is kept.
#
# Every C output is validated in Python with lib.is_valid. A baseline (PG,
# GQ, or K_{d,d}) is always kept as a fallback.
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

#define RP_EXTRA 600
#define RP_T0 3.0
#define RP_TEND 0.2

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

/* ---------------- Stage 2: unstructured repair (mode 1) ---------------- */

static int rp_N, rp_M, rp_MAXV, rp_DEG, rp_DIAM;
static int *rp_adj, *rp_dg, *rp_ea, *rp_eb;
static int *bk_adj, *bk_dg, *bk_ea, *bk_eb;
static int bk_N, bk_M;
static unsigned char *rp_side;
static uint64_t *rp_A, *rp_B;

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int rp_has_edge(int a, int b) {
    const int *l = rp_adj + (size_t)a * rp_DEG;
    for (int k = 0; k < rp_dg[a]; k++)
        if (l[k] == b) return 1;
    return 0;
}

static void rp_replace(int v, int old, int nw) {
    int *l = rp_adj + (size_t)v * rp_DEG;
    for (int k = 0; k < rp_dg[v]; k++)
        if (l[k] == old) { l[k] = nw; return; }
}

static void rp_add_nb(int v, int w) {
    rp_adj[(size_t)v * rp_DEG + rp_dg[v]] = w;
    rp_dg[v]++;
}

/* Degree-preserving 2-switch on edges i=(p1,q1), j=(p2,q2) -> (p1,q2), (p2,q1).
   Applying it again to the same indices undoes it. */
static void rp_apply_switch(int i, int j) {
    int p1 = rp_ea[i], q1 = rp_eb[i], p2 = rp_ea[j], q2 = rp_eb[j];
    rp_replace(p1, q1, q2);
    rp_replace(q2, p2, p1);
    rp_replace(p2, q2, q1);
    rp_replace(q1, p1, p2);
    rp_eb[i] = q2;
    rp_eb[j] = q1;
}

/* Number of ordered pairs at distance > DIAM, via bitset BFS from every vertex. */
static long long rp_cost(void) {
    int N = rp_N, W = (N + 63) / 64;
    uint64_t *cur = rp_A, *nxt = rp_B;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++)
        cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int s = 0; s < rp_DIAM; s++) {
        for (int v = 0; v < N; v++) {
            uint64_t *out = nxt + (size_t)v * W;
            const uint64_t *in = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) out[w] = in[w];
            const int *l = rp_adj + (size_t)v * rp_DEG;
            for (int k = 0; k < rp_dg[v]; k++) {
                const uint64_t *src = cur + (size_t)l[k] * W;
                for (int w = 0; w < W; w++) out[w] |= src[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *in = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(in[w]);
        bad += N - c;
    }
    return bad;
}

/* Add an A-vertex a and a B-vertex b. Each of DEG steps takes an edge (x,y),
   replaces it by (x,b), and adds (a,y). Old degrees are unchanged. */
static int rp_insert_pair(void) {
    if (rp_N + 2 > rp_MAXV) return 0;
    int a = rp_N, b = rp_N + 1;
    rp_side[a] = 0;
    rp_side[b] = 1;
    rp_dg[a] = 0;
    rp_dg[b] = 0;
    rp_N += 2;
    for (int k = 0; k < rp_DEG; k++) {
        int done = 0;
        if (rp_M == 0) return 0;
        for (int tr = 0; tr < 400 && !done; tr++) {
            if (rp_M >= rp_MAXV * rp_DEG) return 0;
            int i = rnd_int(rp_M);
            int x = rp_ea[i], y = rp_eb[i];
            if (rp_has_edge(a, y) || rp_has_edge(x, b)) continue;
            rp_replace(x, y, b);
            rp_add_nb(b, x);
            rp_replace(y, x, a);
            rp_add_nb(a, y);
            rp_eb[i] = b;
            rp_ea[rp_M] = a;
            rp_eb[rp_M] = y;
            rp_M++;
            done = 1;
        }
        if (!done) return 0;
    }
    return 1;
}

/* Simulated annealing on 2-switches. Returns 1 if a valid graph (cost 0) is reached before end. */
static int rp_anneal(double end) {
    if (rp_M < 2) return 0;
    long long cur = rp_cost();
    if (cur == 0) return 1;
    double t0 = elapsed();
    double span = end - t0;
    if (span <= 0) return 0;
    double frac = 0.0;
    for (long long it = 0; ; it++) {
        if ((it & 31) == 0) {
            double now = elapsed();
            if (now >= end) break;
            frac = (now - t0) / span;
        }
        double temp = RP_T0 * pow(RP_TEND / RP_T0, frac);
        int i = rnd_int(rp_M), j = rnd_int(rp_M);
        if (i == j) continue;
        int a1 = rp_ea[i], a2 = rp_ea[j], b1 = rp_eb[i], b2 = rp_eb[j];
        if (a1 == a2 || b1 == b2) continue;
        if (rp_has_edge(a1, b2) || rp_has_edge(a2, b1)) continue;
        rp_apply_switch(i, j);
        long long nc = rp_cost();
        if (nc <= cur || rnd_unit() < exp(-(double)(nc - cur) / temp)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            rp_apply_switch(i, j);
        }
    }
    return 0;
}

static void rp_save(void) {
    size_t na = (size_t)rp_MAXV * (size_t)rp_DEG;
    memcpy(bk_adj, rp_adj, sizeof(int) * na);
    memcpy(bk_dg, rp_dg, sizeof(int) * (size_t)rp_MAXV);
    memcpy(bk_ea, rp_ea, sizeof(int) * na);
    memcpy(bk_eb, rp_eb, sizeof(int) * na);
    bk_N = rp_N;
    bk_M = rp_M;
}

static void rp_restore(void) {
    size_t na = (size_t)rp_MAXV * (size_t)rp_DEG;
    memcpy(rp_adj, bk_adj, sizeof(int) * na);
    memcpy(rp_dg, bk_dg, sizeof(int) * (size_t)rp_MAXV);
    memcpy(rp_ea, bk_ea, sizeof(int) * na);
    memcpy(rp_eb, bk_eb, sizeof(int) * na);
    rp_N = bk_N;
    rp_M = bk_M;
}

static void repair_main(int nA, double deadline) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || m < 0) {
        printf("0 0\n");
        return;
    }
    rp_DEG = DEG;
    rp_DIAM = DIAM;
    rp_MAXV = n + RP_EXTRA;
    int W = (rp_MAXV + 63) / 64;
    size_t cap = (size_t)rp_MAXV * (size_t)DEG;
    rp_adj = malloc(sizeof(int) * cap);
    rp_dg = calloc((size_t)rp_MAXV, sizeof(int));
    rp_ea = malloc(sizeof(int) * cap);
    rp_eb = malloc(sizeof(int) * cap);
    bk_adj = malloc(sizeof(int) * cap);
    bk_dg = calloc((size_t)rp_MAXV, sizeof(int));
    bk_ea = malloc(sizeof(int) * cap);
    bk_eb = malloc(sizeof(int) * cap);
    rp_side = calloc((size_t)rp_MAXV, 1);
    rp_A = malloc(sizeof(uint64_t) * (size_t)rp_MAXV * (size_t)W);
    rp_B = malloc(sizeof(uint64_t) * (size_t)rp_MAXV * (size_t)W);
    rp_N = n;
    rp_M = 0;
    for (int v = 0; v < n; v++) rp_side[v] = (unsigned char)(v >= nA ? 1 : 0);

    int ok = 1;
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || rp_side[u] == rp_side[v] || u == v) {
            ok = 0;
            continue;
        }
        int a = (rp_side[u] == 0) ? u : v;
        int b = (a == u) ? v : u;
        if (rp_dg[a] >= DEG || rp_dg[b] >= DEG || rp_has_edge(a, b)) { ok = 0; continue; }
        rp_add_nb(a, b);
        rp_add_nb(b, a);
        rp_ea[rp_M] = a;
        rp_eb[rp_M] = b;
        rp_M++;
    }
    if (!ok) {
        printf("0 0\n");
        return;
    }
    if (rp_cost() != 0) {
        if (!rp_anneal(deadline)) {
            printf("0 0\n");
            return;
        }
    }
    rp_save();
    while (elapsed() < deadline && rp_N + 2 <= rp_MAXV) {
        if (!rp_insert_pair()) { rp_restore(); break; }
        if (!rp_anneal(deadline)) { rp_restore(); break; }
        rp_save();
    }
    printf("%d %d\n", rp_N, rp_M);
    for (int i = 0; i < rp_M; i++)
        printf("%d %d\n", rp_ea[i], rp_eb[i]);
}

/* ---------------- main ---------------- */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n] [mode] [nA]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int start_n = argc > 5 ? atoi(argv[5]) : 0;
    int mode = argc > 6 ? atoi(argv[6]) : 0;
    int nA = argc > 7 ? atoi(argv[7]) : 0;
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

    if (mode == 1) {
        repair_main(nA, DEADLINE);
        return 0;
    }

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
# Driver: baselines, then lift search (stage 1), then repair (stage 2).
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    hn, he = lib.haar_graph(d, range(d))
    best = (hn, he)
    best_nA = d  # A side of the current best graph is vertices 0..best_nA-1

    def consider(n, e, nA):
        nonlocal best, best_nA
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_nA = nA

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1], pg[0] // 2)

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1], gq[0] // 2)

    if best[0] >= lib.moore_bound(d, D):
        return best

    def remaining():
        return 0.92 * time_limit - (time.monotonic() - start) - 1.5

    # Stage 1: voltage-lift search for a larger graph. Lift output has A side = n/2.
    rem = remaining()
    if rem >= 2.0:
        t1 = 0.4 * rem
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{t1:.2f}", best[0], 0, 0],
                            timeout=t1 + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e, n // 2)
        except Exception:
            pass

    # Stage 2: unstructured repair from the best graph, inserting vertex pairs.
    rem = remaining()
    if rem >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed + 1, f"{rem:.2f}", 0, 1, best_nA],
                            stdin_graph=best, timeout=rem + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e, n // 2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
