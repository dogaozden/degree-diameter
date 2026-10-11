import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine, two phases in one process (one run_c call):
#
# Phase 1 (first half of the budget): voltage lifts of semidirect products
# Z_m x| Z_k2 over a base of K A-vertices and K B-vertices, searched by
# simulated annealing with breakout weights and an elite pool (ILS).
#
# Phase 2 (second half): unstructured repair and growth. The best graph from
# phase 1 is loaded as a plain bipartite graph. Moves are degree-preserving
# edge swaps, edge additions and endpoint rewires, scored by the number of
# ordered vertex pairs at distance > D plus the total degree deficit. When a
# zero-bad state is reached, the graph is recorded and a new (A, B) vertex
# pair is appended. Each epoch restarts from the best recorded graph.
#
# Validity: every emitted graph has max degree <= d, no self-loops, no
# duplicate edges, is bipartite (A/B sides are preserved by every move), and
# has diameter <= D (bad == 0). Python still checks everything with lib.is_valid.
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
static int best_half = 0;
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
    best_half = K * G;
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

/* ---------------- Phase 2: unstructured repair and growth ---------------- */

#define RP_MAXN 2048
#define RP_WMAX (RP_MAXN / 64)
#define RP_EPOCH 12000

static int rp_n = 0, rp_W = 0, rp_bn = 0, rp_bm = 0, rp_half = 0;
static int *rp_be = NULL;
static int *rp_adj = NULL, *rp_deg = NULL, *rp_side = NULL;
static unsigned char *rp_mat = NULL;
static uint64_t *rp_r0 = NULL, *rp_r1 = NULL;
static long long rp_lastbad = 0;

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void rp_remove_from(int a, int b) {
    int *L = rp_adj + (size_t)a * DEG;
    int dg = rp_deg[a];
    for (int i = 0; i < dg; i++)
        if (L[i] == b) { L[i] = L[dg - 1]; rp_deg[a] = dg - 1; return; }
}

static void rp_add(int a, int b) {
    rp_adj[(size_t)a * DEG + rp_deg[a]++] = b;
    rp_adj[(size_t)b * DEG + rp_deg[b]++] = a;
    rp_mat[(size_t)a * RP_MAXN + b] = 1;
    rp_mat[(size_t)b * RP_MAXN + a] = 1;
}

static void rp_del(int a, int b) {
    rp_remove_from(a, b);
    rp_remove_from(b, a);
    rp_mat[(size_t)a * RP_MAXN + b] = 0;
    rp_mat[(size_t)b * RP_MAXN + a] = 0;
}

static int rp_adjq(int a, int b) { return rp_mat[(size_t)a * RP_MAXN + b]; }

static int rp_rand_side(int s) {
    for (int t = 0; t < 1000; t++) {
        int v = rnd_int(rp_n);
        if (rp_side[v] == s) return v;
    }
    return -1;
}

/* Number of ordered pairs at distance > DIAM, via bitset balls. */
static long long rp_bad(void) {
    int n = rp_n, W = rp_W;
    uint64_t *cur = rp_r0, *nxt = rp_r1;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            const int *L = rp_adj + (size_t)v * DEG;
            int dg = rp_deg[v];
            for (int i = 0; i < dg; i++) {
                const uint64_t *cu = cur + (size_t)L[i] * W;
                for (int w = 0; w < W; w++) o[w] |= cu[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *c = cur + (size_t)v * W;
        int cn = 0;
        for (int w = 0; w < W; w++) cn += pc64(c[w]);
        bad += n - cn;
    }
    return bad;
}

static long long rp_deficit(void) {
    long long s = 0;
    for (int v = 0; v < rp_n; v++) s += DEG - rp_deg[v];
    return s;
}

static long long rp_cost(void) {
    long long b = rp_bad();
    rp_lastbad = b;
    return b + rp_deficit();
}

static void rp_grow(void) {
    int a = rp_n, b = rp_n + 1;
    rp_side[a] = 0;
    rp_side[b] = 1;
    rp_deg[a] = 0;
    rp_deg[b] = 0;
    rp_n += 2;
    rp_W = (rp_n + 63) >> 6;
}

static void rp_clear(void) {
    for (int v = 0; v < rp_n; v++) {
        for (int i = 0; i < rp_deg[v]; i++) {
            int u = rp_adj[(size_t)v * DEG + i];
            rp_mat[(size_t)v * RP_MAXN + u] = 0;
        }
        rp_deg[v] = 0;
    }
}

static void rp_restore(void) {
    rp_clear();
    rp_n = rp_bn;
    rp_W = (rp_n + 63) >> 6;
    for (int i = 0; i < rp_bm; i++) rp_add(rp_be[2 * i], rp_be[2 * i + 1]);
}

static void rp_record(void) {
    long long s = 0;
    for (int v = 0; v < rp_n; v++) s += rp_deg[v];
    int m = (int)(s / 2);
    int *ne = malloc(sizeof(int) * 2 * (size_t)(m > 0 ? m : 1));
    int idx = 0;
    for (int v = 0; v < rp_n; v++)
        for (int i = 0; i < rp_deg[v]; i++) {
            int u = rp_adj[(size_t)v * DEG + i];
            if (v < u) { ne[idx++] = v; ne[idx++] = u; }
        }
    free(rp_be);
    rp_be = ne;
    rp_bm = m;
    rp_bn = rp_n;
}

static void repair_phase(void) {
    if (best_m <= 0 || best_n <= 0 || best_n + 2 > RP_MAXN || best_half <= 0) return;
    rp_adj = calloc((size_t)RP_MAXN * DEG, sizeof(int));
    rp_deg = calloc(RP_MAXN, sizeof(int));
    rp_side = calloc(RP_MAXN, sizeof(int));
    rp_mat = calloc((size_t)RP_MAXN * RP_MAXN, 1);
    rp_r0 = calloc((size_t)RP_MAXN * RP_WMAX, sizeof(uint64_t));
    rp_r1 = calloc((size_t)RP_MAXN * RP_WMAX, sizeof(uint64_t));
    if (!rp_adj || !rp_deg || !rp_side || !rp_mat || !rp_r0 || !rp_r1) return;

    rp_half = best_half;
    for (int v = 0; v < best_n; v++) rp_side[v] = (v >= best_half);
    rp_bn = best_n;
    rp_bm = best_m;
    rp_be = malloc(sizeof(int) * 2 * (size_t)best_m);
    memcpy(rp_be, best_e, sizeof(int) * 2 * (size_t)best_m);
    rp_n = 0;
    rp_W = 0;
    rp_restore();

    while (elapsed() < DEADLINE && rp_bn + 2 <= RP_MAXN) {
        rp_restore();
        rp_grow();
        long long cur = rp_cost();
        for (int it = 0; it < RP_EPOCH; it++) {
            if (elapsed() > DEADLINE) break;
            double frac = (double)it / RP_EPOCH;
            double temp = 1.2 * exp(-3.0 * frac) + 0.05;
            int acc = 0;
            int mv = rnd_int(10);
            if (mv < 5) {
                int a1 = rp_rand_side(0), a2 = rp_rand_side(0);
                if (a1 < 0 || a2 < 0 || a1 == a2 || rp_deg[a1] == 0 || rp_deg[a2] == 0) continue;
                int b1 = rp_adj[(size_t)a1 * DEG + rnd_int(rp_deg[a1])];
                int b2 = rp_adj[(size_t)a2 * DEG + rnd_int(rp_deg[a2])];
                if (b1 == b2 || rp_adjq(a1, b2) || rp_adjq(a2, b1)) continue;
                rp_del(a1, b1); rp_del(a2, b2);
                rp_add(a1, b2); rp_add(a2, b1);
                long long nc = rp_cost();
                if (nc <= cur || rnd_unit() < exp(-(double)(nc - cur) / temp)) {
                    cur = nc; acc = 1;
                } else {
                    rp_del(a1, b2); rp_del(a2, b1);
                    rp_add(a1, b1); rp_add(a2, b2);
                }
            } else if (mv < 7) {
                int a = rp_rand_side(0), b = rp_rand_side(1);
                if (a < 0 || b < 0 || rp_deg[a] >= DEG || rp_deg[b] >= DEG || rp_adjq(a, b)) continue;
                rp_add(a, b);
                long long nc = rp_cost();
                if (nc <= cur || rnd_unit() < exp(-(double)(nc - cur) / temp)) {
                    cur = nc; acc = 1;
                } else {
                    rp_del(a, b);
                }
            } else {
                int a = rp_rand_side(0);
                if (a < 0 || rp_deg[a] == 0) continue;
                int b1 = rp_adj[(size_t)a * DEG + rnd_int(rp_deg[a])];
                int b2 = rp_rand_side(1);
                if (b2 < 0 || b2 == b1 || rp_deg[b2] >= DEG || rp_adjq(a, b2)) continue;
                rp_del(a, b1);
                rp_add(a, b2);
                long long nc = rp_cost();
                if (nc <= cur || rnd_unit() < exp(-(double)(nc - cur) / temp)) {
                    cur = nc; acc = 1;
                } else {
                    rp_del(a, b2);
                    rp_add(a, b1);
                }
            }
            if (acc && rp_lastbad == 0) {
                rp_record();
                if (rp_bn + 2 > RP_MAXN) break;
                rp_grow();
                cur = rp_cost();
            }
        }
    }

    if (rp_be != NULL && rp_bn > best_n) {
        free(best_e);
        best_e = rp_be;
        rp_be = NULL;
        best_n = rp_bn;
        best_m = rp_bm;
    }
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

    double total_t = DEADLINE;
    DEADLINE = total_t * 0.5;

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

    DEADLINE = total_t;
    repair_phase();

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
# Driver: baselines in Python, then one C run (group-lift search, then repair).
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

    remaining = 0.92 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
