"""Two-phase search for near-Moore bipartite graphs.

Phase 1 runs the voltage-lift annealer (Z_m x| Z_k lifts with breakout weights and an
elite pool) to get a strong structured start.

Phase 2 is the bold change: a direct graph-level search on the bipartite graph itself,
with no group structure. Moves are edge additions, endpoint moves and edge switches.
The cost is the number of ordered vertex pairs at distance > D, computed with bitset
BFS. Whenever the cost reaches 0, the graph is snapshotted and two vertices (one per
side) are added. After a stall the search restores the snapshot and applies random
kicks. Every candidate is checked with lib.is_valid before it can replace the fallback.
"""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Phase 1 C engine: voltage lifts of semidirect products Z_m x| Z_k2 over a base of
# K A-vertices and K B-vertices, searched by simulated annealing with breakout
# weights and an elite pool (iterated local search).
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
# Phase 2 C engine: graph-level search on a bipartite graph (no group structure).
# ----------------------------------------------------------------------------

C_GRAPH = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define GROWMAX 160
#define EPOCH 20000
#define STAG 25000
#define KICK 12

static struct timespec T0;
static double DL;
static uint64_t rs[2];

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s0 = rs[0], s1 = rs[1];
    uint64_t r = s0 + s1;
    s1 ^= s0;
    rs[0] = ((s0 << 24) | (s0 >> 40)) ^ s1 ^ (s1 << 16);
    rs[1] = (s1 << 37) | (s1 >> 27);
    return r;
}

static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int d, D, n, capn, W, ne, cape, nA, nB;
static int *side, *deg, *adj, *ea, *eb, *sea, *seb, *Al, *Bl, *fA, *fB;
static int snap_n = -1, snap_ne = 0;
static uint64_t *bufA, *bufB;

static int is_adj(int a, int b) {
    const int *p = adj + (size_t)a * d;
    for (int k = 0; k < deg[a]; k++)
        if (p[k] == b) return 1;
    return 0;
}

static void add_adj(int u, int v) {
    adj[(size_t)u * d + deg[u]] = v;
    deg[u]++;
}

static void del_adj(int u, int v) {
    int *p = adj + (size_t)u * d;
    for (int k = 0; k < deg[u]; k++)
        if (p[k] == v) {
            p[k] = p[deg[u] - 1];
            deg[u]--;
            return;
        }
}

static void rep_adj(int u, int old, int nw) {
    int *p = adj + (size_t)u * d;
    for (int k = 0; k < deg[u]; k++)
        if (p[k] == old) {
            p[k] = nw;
            return;
        }
}

static void edge_add(int a, int b) {
    int k = ne++;
    ea[k] = a;
    eb[k] = b;
    add_adj(a, b);
    add_adj(b, a);
}

/* Move the B endpoint of edge k to vertex e (a keeps its degree, e gains, old b loses). */
static void set_b(int k, int e) {
    int a = ea[k], b = eb[k];
    rep_adj(a, b, e);
    del_adj(b, a);
    add_adj(e, a);
    eb[k] = e;
}

/* Move the A endpoint of edge k to vertex x. */
static void set_a(int k, int x) {
    int a = ea[k], b = eb[k];
    rep_adj(b, a, x);
    del_adj(a, b);
    add_adj(x, b);
    ea[k] = x;
}

/* Switch edges (a1,b1),(a2,b2) into (a1,b2),(a2,b1). Applying it twice undoes it. */
static void sw(int k1, int k2) {
    int a1 = ea[k1], b1 = eb[k1], a2 = ea[k2], b2 = eb[k2];
    rep_adj(a1, b1, b2);
    rep_adj(b1, a1, a2);
    rep_adj(a2, b2, b1);
    rep_adj(b2, a2, a1);
    eb[k1] = b2;
    eb[k2] = b1;
}

static void rebuild(void) {
    for (int v = 0; v < capn; v++) deg[v] = 0;
    for (int k = 0; k < ne; k++) {
        add_adj(ea[k], eb[k]);
        add_adj(eb[k], ea[k]);
    }
    nA = nB = 0;
    for (int v = 0; v < n; v++) {
        if (side[v] == 0) Al[nA++] = v;
        else Bl[nB++] = v;
    }
}

/* Ordered pairs (v,u) with dist > D, via bitset balls of growing radius. */
static long long eval_bad(void) {
    int Wn = (n + 63) >> 6;
    uint64_t *cur = bufA, *nxt = bufB;
    for (int v = 0; v < n; v++) {
        uint64_t *c = cur + (size_t)v * W;
        for (int j = 0; j < Wn; j++) c[j] = 0;
        c[v >> 6] |= (uint64_t)1 << (v & 63);
    }
    for (int lvl = 0; lvl < D; lvl++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            for (int j = 0; j < Wn; j++) o[j] = c[j];
            const int *p = adj + (size_t)v * d;
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *cu = cur + (size_t)p[k] * W;
                for (int j = 0; j < Wn; j++) o[j] |= cu[j];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *c = cur + (size_t)v * W;
        int cnt = 0;
        for (int j = 0; j < Wn; j++) cnt += __builtin_popcountll(c[j]);
        bad += n - cnt;
    }
    return bad;
}

static void take_snapshot(void) {
    snap_n = n;
    snap_ne = ne;
    memcpy(sea, ea, sizeof(int) * (size_t)ne);
    memcpy(seb, eb, sizeof(int) * (size_t)ne);
}

static void restore_snapshot(void) {
    n = snap_n;
    ne = snap_ne;
    memcpy(ea, sea, sizeof(int) * (size_t)ne);
    memcpy(eb, seb, sizeof(int) * (size_t)ne);
    rebuild();
}

static void grow(void) {
    int a = n, b = n + 1;
    side[a] = 0;
    side[b] = 1;
    deg[a] = 0;
    deg[b] = 0;
    n += 2;
    Al[nA++] = a;
    Bl[nB++] = b;
}

static void kick_one(void) {
    for (int tries = 0; tries < 20; tries++) {
        if (ne < 2) return;
        int k1 = rndi(ne), k2 = rndi(ne);
        if (k1 == k2) continue;
        if (ea[k1] == ea[k2] || eb[k1] == eb[k2]) continue;
        if (is_adj(ea[k1], eb[k2]) || is_adj(ea[k2], eb[k1])) continue;
        sw(k1, k2);
        return;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit < graph\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DL = atof(argv[4]);
    uint64_t sm = sd * 2654435761ULL + 99991ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int n_in = 0, m_in = 0;
    if (scanf("%d %d", &n_in, &m_in) != 2 || n_in < 1 || m_in < 0 || d < 1 || D < 1) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(m_in + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m_in + 1));
    for (int i = 0; i < m_in; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (eu[i] < 0 || eu[i] >= n_in || ev[i] < 0 || ev[i] >= n_in || eu[i] == ev[i]) {
            printf("0 0\n");
            return 0;
        }
    }
    int *dg = calloc((size_t)n_in, sizeof(int));
    for (int i = 0; i < m_in; i++) {
        dg[eu[i]]++;
        dg[ev[i]]++;
    }
    for (int v = 0; v < n_in; v++)
        if (dg[v] > d) {
            printf("0 0\n");
            return 0;
        }
    int *off = calloc((size_t)n_in + 1, sizeof(int));
    for (int v = 0; v < n_in; v++) off[v + 1] = off[v] + dg[v];
    int *fillp = calloc((size_t)n_in, sizeof(int));
    int *lst = malloc(sizeof(int) * (size_t)(2 * m_in + 1));
    for (int i = 0; i < m_in; i++) {
        lst[off[eu[i]] + fillp[eu[i]]++] = ev[i];
        lst[off[ev[i]] + fillp[ev[i]]++] = eu[i];
    }
    int *col = malloc(sizeof(int) * (size_t)n_in);
    int *qu = malloc(sizeof(int) * (size_t)n_in);
    for (int v = 0; v < n_in; v++) col[v] = -1;
    for (int s = 0; s < n_in; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        qu[qt++] = s;
        while (qh < qt) {
            int u = qu[qh++];
            for (int j = off[u]; j < off[u + 1]; j++) {
                int w = lst[j];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    qu[qt++] = w;
                } else if (col[w] == col[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    capn = n_in + GROWMAX;
    W = (capn + 63) >> 6;
    cape = capn * d + 4;
    side = malloc(sizeof(int) * (size_t)capn);
    deg = calloc((size_t)capn, sizeof(int));
    adj = malloc(sizeof(int) * (size_t)capn * (size_t)d);
    ea = malloc(sizeof(int) * (size_t)cape);
    eb = malloc(sizeof(int) * (size_t)cape);
    sea = malloc(sizeof(int) * (size_t)cape);
    seb = malloc(sizeof(int) * (size_t)cape);
    Al = malloc(sizeof(int) * (size_t)capn);
    Bl = malloc(sizeof(int) * (size_t)capn);
    fA = malloc(sizeof(int) * (size_t)capn);
    fB = malloc(sizeof(int) * (size_t)capn);
    bufA = malloc(sizeof(uint64_t) * (size_t)capn * (size_t)W);
    bufB = malloc(sizeof(uint64_t) * (size_t)capn * (size_t)W);
    for (int v = 0; v < capn; v++) side[v] = 0;
    for (int v = 0; v < n_in; v++) side[v] = col[v];

    n = n_in;
    ne = 0;
    for (int i = 0; i < m_in; i++) {
        int u = eu[i], v = ev[i];
        if (side[u] == 0) {
            ea[ne] = u;
            eb[ne] = v;
        } else {
            ea[ne] = v;
            eb[ne] = u;
        }
        ne++;
    }
    rebuild();

    long long cost = eval_bad();
    if (cost == 0) take_snapshot();

    long long it = 0, ep = 0, last_grow = 0;
    while (1) {
        if ((it & 31) == 0 && elapsed() > DL) break;
        it++;
        ep++;
        if (ep >= EPOCH) ep = 0;

        if (cost == 0) {
            if (n > snap_n) take_snapshot();
            if (n + 2 > capn) break;
            grow();
            cost = eval_bad();
            last_grow = it;
            ep = 0;
            continue;
        }
        if (it - last_grow > STAG) {
            if (snap_n >= 0 && n > snap_n) restore_snapshot();
            for (int q = 0; q < KICK; q++) kick_one();
            cost = eval_bad();
            last_grow = it;
            ep = 0;
            continue;
        }
        if (nA < 1 || nB < 1) break;

        double T = 2.0 * pow(0.075, (double)ep / EPOCH);
        double u = rndu();
        if (u < 0.2) {
            int nfa = 0, nfb = 0;
            for (int i = 0; i < nA; i++)
                if (deg[Al[i]] < d) fA[nfa++] = Al[i];
            for (int i = 0; i < nB; i++)
                if (deg[Bl[i]] < d) fB[nfb++] = Bl[i];
            if (nfa > 0 && nfb > 0) {
                for (int tr = 0; tr < 40; tr++) {
                    int a = fA[rndi(nfa)], b = fB[rndi(nfb)];
                    if (!is_adj(a, b)) {
                        edge_add(a, b);
                        cost = eval_bad();
                        break;
                    }
                }
            }
        } else if (u < 0.55) {
            if (ne < 1) continue;
            int k = rndi(ne);
            if (rndu() < 0.5) {
                int e = Bl[rndi(nB)];
                if (deg[e] >= d || e == eb[k] || is_adj(ea[k], e)) continue;
                int old = eb[k];
                set_b(k, e);
                long long nc = eval_bad();
                int ok = (nc <= cost) || (rndu() < exp(-(double)(nc - cost) / T));
                if (ok) cost = nc;
                else set_b(k, old);
            } else {
                int x = Al[rndi(nA)];
                if (deg[x] >= d || x == ea[k] || is_adj(x, eb[k])) continue;
                int old = ea[k];
                set_a(k, x);
                long long nc = eval_bad();
                int ok = (nc <= cost) || (rndu() < exp(-(double)(nc - cost) / T));
                if (ok) cost = nc;
                else set_a(k, old);
            }
        } else {
            if (ne < 2) continue;
            int k1 = rndi(ne), k2 = rndi(ne);
            if (k1 == k2) continue;
            if (ea[k1] == ea[k2] || eb[k1] == eb[k2]) continue;
            if (is_adj(ea[k1], eb[k2]) || is_adj(ea[k2], eb[k1])) continue;
            sw(k1, k2);
            long long nc = eval_bad();
            int ok = (nc <= cost) || (rndu() < exp(-(double)(nc - cost) / T));
            if (ok) cost = nc;
            else sw(k1, k2);
        }
    }

    if (snap_n < 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", snap_n, snap_ne);
    for (int k = 0; k < snap_ne; k++)
        printf("%d %d\n", sea[k], seb[k]);
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


# ----------------------------------------------------------------------------
# Driver: baselines, then the lift annealer (phase 1), then graph-level search (phase 2).
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    def left():
        """Seconds still available for C runs, keeping a safety margin."""
        return 0.9 * time_limit - (time.monotonic() - start) - 1.5

    def hard_timeout(t):
        """Subprocess timeout that stays inside the case's time limit."""
        return max(1.0, min(t + 3.0, time_limit - (time.monotonic() - start) - 2.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    if D >= 3:
        for builder in (_best_pg, _araujo):
            try:
                g = builder(d)
                if g is not None:
                    consider(g[0], g[1])
            except Exception:
                pass

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    avail = left()
    if avail < 2.0:
        return best

    # Phase 1: voltage-lift annealer on semidirect-product groups.
    t1 = 0.55 * avail
    try:
        out = lib.run_c(C_LIFT, [d, D, seed, f"{t1:.2f}", best_n],
                        timeout=hard_timeout(t1))
        n1, e1 = lib.parse_graph_text(out)
        consider(n1, e1)
    except Exception:
        pass

    # Phase 2: direct graph-level search that grows the best graph found so far.
    t2 = left()
    if t2 >= 2.0:
        try:
            out = lib.run_c(C_GRAPH, [d, D, seed, f"{t2:.2f}"],
                            stdin_graph=best, timeout=hard_timeout(t2))
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
