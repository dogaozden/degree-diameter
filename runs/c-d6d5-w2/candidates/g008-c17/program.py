import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Two-phase C engine.
#
# Phase 1 (about 65% of the budget): voltage-lift search over semidirect
# products Z_m x| Z_k2 with K base vertices per side, as in the parent. It uses
# breakout-weighted annealing, an elite pool and ILS. The best valid lift is
# kept.
#
# Phase 2 (remaining budget): a different construction. Starting from the
# phase-1 graph, which must be DEG-regular and bipartite with A = first half of
# the labels, it inserts two new vertices by removing a matching of DEG edges
# and rewiring it through the new A and B vertices. This keeps every degree at
# DEG. Simulated annealing over 2-switches then repairs diameter, with the cost
# = number of vertex pairs at distance > DIAM. Diameter is checked exactly with
# bitset balls. Failed attempts roll back to the last valid snapshot.
#
# Every output graph is valid by construction: switches keep A-B edges and
# degrees, insertions keep regularity, and the cost-0 test is the exact
# diameter test. Python re-checks with lib.is_valid and falls back if needed.
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
#define MAXDEG 64
#define EXTRA_V 600
#define P2_ITERS 6000
#define P2_T0 3.0
#define P2_T1 0.15
#define P1_FRAC 0.65

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

/* ---------------- Phase 1: voltage lifts ---------------- */

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

static void phase1(void) {
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
}

/* ---------------- Phase 2: edge-switch repair with vertex insertion ---------------- */

static int MAXN, WMAX;
static int NV, NE;
static int *p2adj;            /* p2adj[v*DEG + k] */
static int *p2ex, *p2ey;      /* edge list: ex in A, ey in B */
static int *snapadj, *snapex, *snapey;
static int snapNV, snapNE;
static uint64_t *RA, *RB;
static int *markA, *markB;
static int markst = 0;

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void replace_nb(int v, int oldu, int newu) {
    int *row = p2adj + (size_t)v * DEG;
    for (int k = 0; k < DEG; k++)
        if (row[k] == oldu) { row[k] = newu; return; }
}

static int has_edge(int u, int v) {
    const int *row = p2adj + (size_t)u * DEG;
    for (int k = 0; k < DEG; k++)
        if (row[k] == v) return 1;
    return 0;
}

/* Edges (a,b),(c,d) become (a,d),(c,b). Applying it twice undoes it. */
static void do_switch(int i, int j) {
    int a = p2ex[i], b = p2ey[i], c = p2ex[j], d = p2ey[j];
    replace_nb(a, b, d);
    replace_nb(d, c, a);
    replace_nb(c, d, b);
    replace_nb(b, a, c);
    p2ey[i] = d;
    p2ey[j] = b;
}

/* Exact number of unordered vertex pairs at distance > DIAM (bitset balls). */
static long long eval_bad(void) {
    int W = (NV + 63) >> 6;
    for (int v = 0; v < NV; v++) {
        uint64_t *row = RA + (size_t)v * WMAX;
        memset(row, 0, sizeof(uint64_t) * (size_t)W);
        row[v >> 6] |= 1ULL << (v & 63);
    }
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < NV; v++) {
            uint64_t *dst = RB + (size_t)v * WMAX;
            const uint64_t *src = RA + (size_t)v * WMAX;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
            const int *row = p2adj + (size_t)v * DEG;
            for (int k = 0; k < DEG; k++) {
                const uint64_t *s2 = RA + (size_t)row[k] * WMAX;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        uint64_t *tmp = RA; RA = RB; RB = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < NV; v++) {
        const uint64_t *row = RA + (size_t)v * WMAX;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc64(row[w]);
        bad += NV - pc;
    }
    return bad / 2;
}

/* Remove a matching of DEG edges (x_i, y_i); add new A vertex a and new B vertex b
   with (x_i, b) and (a, y_i). Every degree is kept, and two vertices are added. */
static int insert_pair(void) {
    if (NV + 2 > MAXN) return 0;
    int chosen[MAXDEG];
    int cnt_c = 0;
    markst++;
    for (int tries = 0; tries < 4000 && cnt_c < DEG; tries++) {
        int e = rnd_int(NE);
        int x = p2ex[e], y = p2ey[e];
        if (markA[x] == markst || markB[y] == markst) continue;
        markA[x] = markst;
        markB[y] = markst;
        chosen[cnt_c++] = e;
    }
    if (cnt_c < DEG) return 0;
    int cx[MAXDEG], cy[MAXDEG];
    for (int i = 0; i < DEG; i++) {
        cx[i] = p2ex[chosen[i]];
        cy[i] = p2ey[chosen[i]];
    }
    int a = NV, b = NV + 1;
    NV += 2;
    for (int i = 0; i < DEG; i++) {
        int e = chosen[i];
        int x = cx[i], y = cy[i];
        p2ey[e] = b;
        replace_nb(x, y, b);
        replace_nb(y, x, a);
        p2ex[NE] = a;
        p2ey[NE] = y;
        NE++;
    }
    for (int i = 0; i < DEG; i++) {
        p2adj[(size_t)a * DEG + i] = cy[i];
        p2adj[(size_t)b * DEG + i] = cx[i];
    }
    return 1;
}

static void snap_save(void) {
    snapNV = NV;
    snapNE = NE;
    memcpy(snapadj, p2adj, sizeof(int) * (size_t)NV * DEG);
    memcpy(snapex, p2ex, sizeof(int) * (size_t)NE);
    memcpy(snapey, p2ey, sizeof(int) * (size_t)NE);
}

static void snap_restore(void) {
    NV = snapNV;
    NE = snapNE;
    memcpy(p2adj, snapadj, sizeof(int) * (size_t)NV * DEG);
    memcpy(p2ex, snapex, sizeof(int) * (size_t)NE);
    memcpy(p2ey, snapey, sizeof(int) * (size_t)NE);
}

/* Simulated annealing on 2-switches; returns 1 once the graph has diameter <= DIAM. */
static int p2_attempt(int iters) {
    long long cost = eval_bad();
    if (cost == 0) return 1;
    for (int it = 0; it < iters; it++) {
        if (elapsed() > DEADLINE) return 0;
        int i = rnd_int(NE), j = rnd_int(NE);
        if (i == j) continue;
        int a = p2ex[i], b = p2ey[i], c = p2ex[j], d = p2ey[j];
        if (a == c || b == d) continue;
        if (has_edge(a, d) || has_edge(c, b)) continue;
        do_switch(i, j);
        double temp = P2_T0 * (1.0 - (double)it / iters) + P2_T1;
        long long nc = eval_bad();
        long long delta = nc - cost;
        if (delta <= 0 || rnd_unit() < exp(-(double)delta / temp)) {
            cost = nc;
            if (cost == 0) return 1;
        } else {
            do_switch(i, j);
        }
    }
    return 0;
}

static void emit_graph(int n, int m, const int *ex, const int *ey) {
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    for (int i = 0; i < m; i++) {
        best_e[2 * i] = ex[i];
        best_e[2 * i + 1] = ey[i];
    }
    best_n = n;
    best_m = m;
}

static void phase2(void) {
    if (best_m <= 0 || DEG > MAXDEG) return;
    int n = best_n, m = best_m;
    MAXN = n + EXTRA_V;
    WMAX = (MAXN + 63) >> 6;
    size_t ecap = (size_t)MAXN * DEG;
    p2adj = malloc(sizeof(int) * ecap);
    p2ex = malloc(sizeof(int) * ecap);
    p2ey = malloc(sizeof(int) * ecap);
    snapadj = malloc(sizeof(int) * ecap);
    snapex = malloc(sizeof(int) * ecap);
    snapey = malloc(sizeof(int) * ecap);
    RA = malloc(sizeof(uint64_t) * (size_t)MAXN * WMAX);
    RB = malloc(sizeof(uint64_t) * (size_t)MAXN * WMAX);
    markA = calloc((size_t)MAXN, sizeof(int));
    markB = calloc((size_t)MAXN, sizeof(int));
    int *fill = calloc((size_t)MAXN, sizeof(int));

    NV = n;
    NE = 0;
    int ok = 1;
    for (int e = 0; e < m && ok; e++) {
        int u = best_e[2 * e], v = best_e[2 * e + 1];
        if (u > v) { int t = u; u = v; v = t; }
        if (u < 0 || v >= n || u >= n / 2 || v < n / 2) { ok = 0; break; }
        if (fill[u] >= DEG || fill[v] >= DEG) { ok = 0; break; }
        p2ex[NE] = u;
        p2ey[NE] = v;
        NE++;
        p2adj[(size_t)u * DEG + fill[u]++] = v;
        p2adj[(size_t)v * DEG + fill[v]++] = u;
    }
    for (int v = 0; v < n && ok; v++)
        if (fill[v] != DEG) ok = 0;
    free(fill);
    if (!ok || eval_bad() != 0) return;

    snap_save();
    while (elapsed() < DEADLINE) {
        if (NV + 2 > MAXN) break;
        if (!insert_pair()) continue;
        if (p2_attempt(P2_ITERS)) {
            snap_save();
            emit_graph(NV, NE, p2ex, p2ey);
        } else {
            snap_restore();
        }
    }
}

/* ---------------- main ---------------- */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    double TOTAL = atof(argv[4]);
    if (DEG < 1 || DIAM < 1 || DEG > MAXDEG) {
        printf("0 0\n");
        return 0;
    }

    best_n = 0;
    best_m = 0;
    best_e = NULL;
    {
        int n = 0, m = 0;
        if (scanf("%d %d", &n, &m) == 2 && n > 0 && m > 0) {
            int *tmp = malloc(sizeof(int) * 2 * (size_t)m);
            int ok = 1;
            for (int i = 0; i < 2 * m && ok; i++)
                if (scanf("%d", &tmp[i]) != 1) ok = 0;
            if (ok) {
                best_e = tmp;
                best_n = n;
                best_m = m;
            } else {
                free(tmp);
            }
        }
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

    DEADLINE = P1_FRAC * TOTAL;
    phase1();
    DEADLINE = TOTAL;
    phase2();

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
# Safe baseline families (Python).
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
# Driver: baselines in Python, then the two-phase C engine.
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

    # The baseline is passed on stdin as the starting graph. The C program
    # spends about 65% of its budget on lift search and the rest on
    # edge-switch repair with vertex insertion.
    remaining = 0.92 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                            stdin_graph=best, timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
