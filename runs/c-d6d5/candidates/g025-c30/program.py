import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: two phases in one program.
#
# Phase 1 (about 60% of the budget): voltage lifts of semidirect products
# Z_m x| Z_k2 over a base of K A-vertices and K B-vertices, searched by
# simulated annealing with breakout weights and an elite pool (ILS). This is
# the proven search from the parent program.
#
# Phase 2 (the rest): a different search, "grow and repair". The best graph so
# far (lift or start graph from stdin) is grown one vertex pair at a time. A new
# A-vertex and B-vertex are attached by splitting random existing edges
# (x,y) -> (x,nb),(na,y), which keeps every old degree fixed. Then a simulated
# annealer with degree-preserving edge switches and free edge additions repairs
# the bad pairs. It uses bitset BFS to count unreachable ordered pairs exactly.
# A grown graph is kept only if it reaches cost 0, so every output is valid.
#
# Vertices of a lift: A_i,g = i*G + g and B_j,h = (K+j)*G + h.
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
#define GMAXN 2100
#define GMAXD 32
#define GMAXW 33

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

static void parent_search(void) {
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
        if (no == 0) { opts[no++] = 1; }
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

/* ---------------------------------------------------------------------------
   Phase 2: grow and repair on a bipartite graph with max degree DEG.
   Vertices 0..gn-1; gside gives a proper 2-colouring used for moves.
   --------------------------------------------------------------------------- */

static int gn = 0;
static int gD = 0;
static int gdeg[GMAXN];
static int gadj[GMAXN][GMAXD];
static int gside[GMAXN];
static uint64_t gbufA[GMAXN * GMAXW];
static uint64_t gbufB[GMAXN * GMAXW];

static int sv_n = 0;
static int sv_deg[GMAXN];
static int sv_adj[GMAXN][GMAXD];

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int gadj_has(int x, int y) {
    for (int i = 0; i < gdeg[x]; i++)
        if (gadj[x][i] == y) return 1;
    return 0;
}

static void gadj_replace(int x, int old, int nw) {
    for (int i = 0; i < gdeg[x]; i++)
        if (gadj[x][i] == old) { gadj[x][i] = nw; return; }
}

/* Replace edges (x,y),(x2,y2) by (x,y2),(x2,y). Degrees are unchanged. */
static void swap_edges(int x, int y, int x2, int y2) {
    gadj_replace(x, y, y2);
    gadj_replace(y, x, x2);
    gadj_replace(x2, y2, y);
    gadj_replace(y2, x2, x);
}

/* Number of ordered pairs at distance > gD (0 iff valid). */
static long long geval(void) {
    int n = gn, W = (n + 63) >> 6;
    uint64_t *cur = gbufA, *nxt = gbufB;
    for (int v = 0; v < n; v++) {
        uint64_t *c = cur + (size_t)v * GMAXW;
        for (int w = 0; w < W; w++) c[w] = 0;
        c[v >> 6] |= 1ULL << (v & 63);
    }
    for (int lvl = 0; lvl < gD; lvl++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + (size_t)v * GMAXW;
            const uint64_t *c = cur + (size_t)v * GMAXW;
            for (int w = 0; w < W; w++) o[w] = c[w];
            for (int i = 0; i < gdeg[v]; i++) {
                const uint64_t *c2 = cur + (size_t)gadj[v][i] * GMAXW;
                for (int w = 0; w < W; w++) o[w] |= c2[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long reach = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *c = cur + (size_t)v * GMAXW;
        for (int w = 0; w < W; w++) reach += pc64(c[w]);
    }
    return (long long)n * n - reach;
}

/* Load an edge list (pairs in e) into gadj. Returns 1 if it is a bipartite graph with degree <= DEG. */
static int load_edges(int n, int m, const int *e) {
    gn = 0;
    if (n <= 0 || n > GMAXN - 2 || m <= 0 || DEG > GMAXD) return 0;
    for (int v = 0; v < n; v++) { gdeg[v] = 0; gside[v] = -1; }
    for (int i = 0; i < m; i++) {
        int u = e[2 * i], v = e[2 * i + 1];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (gdeg[u] >= DEG || gdeg[v] >= DEG) return 0;
        if (gadj_has(u, v)) return 0;
        gadj[u][gdeg[u]++] = v;
        gadj[v][gdeg[v]++] = u;
    }
    int *q = malloc(sizeof(int) * (size_t)n);
    if (!q) return 0;
    int ok = 1;
    for (int s = 0; s < n && ok; s++) {
        if (gside[s] != -1) continue;
        gside[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t && ok) {
            int x = q[h++];
            for (int i = 0; i < gdeg[x]; i++) {
                int y = gadj[x][i];
                if (gside[y] == -1) {
                    gside[y] = 1 - gside[x];
                    q[t++] = y;
                } else if (gside[y] == gside[x]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    free(q);
    if (!ok) return 0;
    gn = n;
    gD = DEG;
    return 1;
}

static void save_state(void) {
    sv_n = gn;
    memcpy(sv_deg, gdeg, sizeof(int) * (size_t)gn);
    memcpy(sv_adj, gadj, sizeof(int) * (size_t)gn * GMAXD);
}

static void restore_state(void) {
    gn = sv_n;
    memcpy(gdeg, sv_deg, sizeof(int) * (size_t)gn);
    memcpy(gadj, sv_adj, sizeof(int) * (size_t)gn * GMAXD);
}

/* Add an A-vertex na and a B-vertex nb. Split random old edges (x,y) into (x,nb),(na,y). */
static int grow_add_pair(void) {
    if (gn + 2 > GMAXN) return 0;
    int nold = gn, na = gn, nb = gn + 1;
    gn += 2;
    gside[na] = 0;
    gside[nb] = 1;
    gdeg[na] = 0;
    gdeg[nb] = 0;
    int tries = 0;
    while (gdeg[na] < gD && tries < 200000) {
        tries++;
        int x = rnd_int(nold);
        if (gside[x] != 0 || gdeg[x] == 0) continue;
        int y = gadj[x][rnd_int(gdeg[x])];
        if (y >= nold) continue;
        if (gadj_has(na, y) || gadj_has(nb, x)) continue;
        gadj_replace(x, y, nb);
        gadj_replace(y, x, na);
        gadj[na][gdeg[na]++] = y;
        gadj[nb][gdeg[nb]++] = x;
    }
    return 1;
}

/* Add an edge between two vertices with spare degree on opposite sides (always helps). */
static int grow_add_edge(void) {
    for (int tr = 0; tr < 60; tr++) {
        int x = rnd_int(gn), y = rnd_int(gn);
        if (gside[x] != 0 || gside[y] != 1) continue;
        if (gdeg[x] >= gD || gdeg[y] >= gD) continue;
        if (gadj_has(x, y)) continue;
        gadj[x][gdeg[x]++] = y;
        gadj[y][gdeg[y]++] = x;
        return 1;
    }
    return 0;
}

static int grow_switch(int *ox, int *oy, int *ox2, int *oy2) {
    int x = -1, x2 = -1;
    for (int tr = 0; tr < 60 && x < 0; tr++) {
        int c = rnd_int(gn);
        if (gside[c] == 0 && gdeg[c] > 0) x = c;
    }
    for (int tr = 0; tr < 60 && x2 < 0; tr++) {
        int c = rnd_int(gn);
        if (gside[c] == 0 && gdeg[c] > 0) x2 = c;
    }
    if (x < 0 || x2 < 0 || x == x2) return 0;
    int y = gadj[x][rnd_int(gdeg[x])];
    int y2 = gadj[x2][rnd_int(gdeg[x2])];
    if (y == y2) return 0;
    if (gadj_has(x, y2) || gadj_has(x2, y)) return 0;
    swap_edges(x, y, x2, y2);
    *ox = x; *oy = y; *ox2 = x2; *oy2 = y2;
    return 1;
}

static long long grow_anneal(long long iters, double T0t, double T1t, long long cost) {
    for (long long it = 0; it < iters && cost > 0; it++) {
        if ((it & 255) == 0 && elapsed() > DEADLINE) break;
        double p = (double)it / (double)iters;
        double temp = T0t * pow(T1t / T0t, p);
        if (rnd_int(8) == 0) {
            if (grow_add_edge()) cost = geval();
            continue;
        }
        int x, y, x2, y2;
        if (!grow_switch(&x, &y, &x2, &y2)) continue;
        long long c2 = geval();
        if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
        } else {
            swap_edges(x, y2, x2, y);
        }
    }
    return cost;
}

static void record_state(void) {
    int m = 0;
    for (int v = 0; v < gn; v++)
        for (int i = 0; i < gdeg[v]; i++)
            if (gadj[v][i] > v) m++;
    int *e = malloc(sizeof(int) * 2 * (size_t)(m > 0 ? m : 1));
    if (!e) return;
    int idx = 0;
    for (int v = 0; v < gn; v++)
        for (int i = 0; i < gdeg[v]; i++) {
            int u = gadj[v][i];
            if (u > v) { e[idx++] = v; e[idx++] = u; }
        }
    free(best_e);
    best_e = e;
    best_m = m;
    best_n = gn;
}

static void grow_phase(void) {
    if (!load_edges(best_n, best_m, best_e)) return;
    long long cap = 4000;
    while (elapsed() < DEADLINE) {
        save_state();
        if (!grow_add_pair()) break;
        long long cost = geval();
        cost = grow_anneal(cap, 6.0, 0.3, cost);
        if (cost == 0) {
            if (gn > best_n) record_state();
            cap = 4000;
        } else {
            restore_state();
            cap *= 2;
            if (cap > 400000) cap = 400000;
        }
    }
}

/* Optional start graph on stdin ("n m" then m lines "u v", or "0 0"). */
static int load_start(void) {
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || m <= 0 || n > GMAXN - 2 || m > 200000) return 0;
    int *eu = malloc(sizeof(int) * 2 * (size_t)m);
    if (!eu) return 0;
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[2 * i], &eu[2 * i + 1]) != 2) { free(eu); return 0; }
    }
    if (!load_edges(n, m, eu)) { free(eu); return 0; }
    free(best_e);
    best_e = eu;
    best_m = m;
    best_n = n;
    return 1;
}

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
    best_n = 0;
    best_m = 0;
    if (DEG < 1 || DIAM < 1 || DEG > GMAXD) {
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

    load_start();

    DEADLINE = 0.6 * TOTAL;
    parent_search();
    if (best_m == 0) {
        DEADLINE = TOTAL;
        parent_search();
    }
    DEADLINE = TOTAL;
    grow_phase();

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
# Driver: baselines in Python, then the C engine (lift search, then grow and repair).
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

    # Give the C search nearly all of the budget. The start graph goes on stdin,
    # so the grow-and-repair phase can extend it.
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
