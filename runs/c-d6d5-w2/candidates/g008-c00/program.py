import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 (C): voltage lifts of semidirect products Z_m x| Z_k2 over a base of
# K A-vertices and K B-vertices, searched by simulated annealing with breakout
# weights and an elite pool (ILS). Produces the start graph for stage 2.
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
# Stage 2 (C): a different construction. Start from a valid d-regular bipartite
# graph and GROW it by vertex insertion: remove a matching of d edges, attach
# two new vertices (one per side) to the freed endpoints. Then repair the
# diameter with degree-preserving double-edge switches under simulated
# annealing, where the cost is the number of ordered vertex pairs at distance
# more than D. Ball sizes are computed with bitsets for all sources at once.
# When a repair succeeds the graph is saved; when a repair stalls, the last
# valid graph is restored and a new insertion is tried.
# ----------------------------------------------------------------------------

SWITCH_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2400
#define MAXD 64
#define MAXW ((MAXN + 63) / 64)
#define PATIENCE 30000
#define TEMP 1.2

static struct timespec T0;
static double DEADLINE;

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

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

static int DEG, D, N;
static int side[MAXN];
static int *nb, *svnb;
static int svN = 0;
static int have_valid = 0;
static uint64_t *R0, *R1;

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int find_slot(int v, int u) {
    const int *a = nb + (size_t)v * DEG;
    for (int k = 0; k < DEG; k++)
        if (a[k] == u) return k;
    return -1;
}

/* Number of ordered pairs (v, w) with dist(v, w) > D. Zero iff valid. */
static long long eval_bad(void) {
    int W = (N + 63) / 64;
    size_t tot = (size_t)N * W;
    memset(R0, 0, sizeof(uint64_t) * tot);
    for (int v = 0; v < N; v++)
        R0[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int lvl = 0; lvl < D; lvl++) {
        for (int v = 0; v < N; v++) {
            uint64_t *row = R1 + (size_t)v * W;
            memcpy(row, R0 + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            const int *av = nb + (size_t)v * DEG;
            for (int k = 0; k < DEG; k++) {
                const uint64_t *src = R0 + (size_t)av[k] * W;
                for (int w = 0; w < W; w++) row[w] |= src[w];
            }
        }
        uint64_t *t = R0; R0 = R1; R1 = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *row = R0 + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(row[w]);
        bad += N - c;
    }
    return bad;
}

typedef struct { int a1, i, a2, j, b1, b2, k1, k2; } Mv;

/* Double-edge switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Keeps degrees and bipartiteness. */
static int do_switch(Mv *m) {
    int a1 = rnd_int(N), a2 = rnd_int(N);
    if (side[a1] != 0 || side[a2] != 0 || a1 == a2) return 0;
    int i = rnd_int(DEG), j = rnd_int(DEG);
    int b1 = nb[(size_t)a1 * DEG + i], b2 = nb[(size_t)a2 * DEG + j];
    if (b1 == b2) return 0;
    if (find_slot(a1, b2) >= 0 || find_slot(a2, b1) >= 0) return 0;
    int k1 = find_slot(b1, a1), k2 = find_slot(b2, a2);
    nb[(size_t)a1 * DEG + i] = b2;
    nb[(size_t)a2 * DEG + j] = b1;
    nb[(size_t)b1 * DEG + k1] = a2;
    nb[(size_t)b2 * DEG + k2] = a1;
    m->a1 = a1; m->i = i; m->a2 = a2; m->j = j;
    m->b1 = b1; m->b2 = b2; m->k1 = k1; m->k2 = k2;
    return 1;
}

static void undo_switch(const Mv *m) {
    nb[(size_t)m->a1 * DEG + m->i] = m->b1;
    nb[(size_t)m->a2 * DEG + m->j] = m->b2;
    nb[(size_t)m->b1 * DEG + m->k1] = m->a1;
    nb[(size_t)m->b2 * DEG + m->k2] = m->a2;
}

/* Vertex insertion: remove a matching of DEG edges (a_k,b_k), add x (side 0) joined to all b_k
   and y (side 1) joined to all a_k. Degrees are preserved and the graph stays simple. */
static int do_insert(void) {
    if (N + 2 > MAXN) return 0;
    int ia[MAXD], ib[MAXD], cnt = 0;
    for (long tries = 0; cnt < DEG && tries < 200000; tries++) {
        int a = rnd_int(N);
        if (side[a] != 0) continue;
        int b = nb[(size_t)a * DEG + rnd_int(DEG)];
        int dup = 0;
        for (int t = 0; t < cnt; t++)
            if (ia[t] == a || ib[t] == b) { dup = 1; break; }
        if (dup) continue;
        ia[cnt] = a; ib[cnt] = b; cnt++;
    }
    if (cnt < DEG) return 0;
    int x = N, y = N + 1;
    side[x] = 0;
    side[y] = 1;
    for (int k = 0; k < DEG; k++) {
        nb[(size_t)x * DEG + k] = ib[k];
        nb[(size_t)y * DEG + k] = ia[k];
    }
    for (int k = 0; k < DEG; k++) {
        int s1 = find_slot(ia[k], ib[k]);
        nb[(size_t)ia[k] * DEG + s1] = y;
        int s2 = find_slot(ib[k], ia[k]);
        nb[(size_t)ib[k] * DEG + s2] = x;
    }
    N += 2;
    return 1;
}

static void save_valid(void) {
    memcpy(svnb, nb, sizeof(int) * (size_t)N * DEG);
    svN = N;
    have_valid = 1;
}

static void restore_valid(void) {
    memcpy(nb, svnb, sizeof(int) * (size_t)svN * DEG);
    N = svN;
}

/* Reads "n m" and m edges. Requires a DEG-regular, bipartite, simple graph. */
static int load_start(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 2 || n > MAXN || m <= 0) return 0;
    int *eu = malloc(sizeof(int) * (size_t)m);
    int *ev = malloc(sizeof(int) * (size_t)m);
    int *deg = calloc((size_t)n, sizeof(int));
    int *fill = calloc((size_t)n, sizeof(int));
    int *q = malloc(sizeof(int) * (size_t)n);
    int ok = 1;
    for (int e = 0; e < m && ok; e++) {
        if (scanf("%d %d", &eu[e], &ev[e]) != 2) { ok = 0; break; }
        if (eu[e] < 0 || eu[e] >= n || ev[e] < 0 || ev[e] >= n || eu[e] == ev[e]) { ok = 0; break; }
        deg[eu[e]]++;
        deg[ev[e]]++;
    }
    for (int v = 0; v < n && ok; v++)
        if (deg[v] != DEG) ok = 0;
    if (ok) {
        N = n;
        nb = malloc(sizeof(int) * (size_t)MAXN * DEG);
        svnb = malloc(sizeof(int) * (size_t)MAXN * DEG);
        for (int e = 0; e < m; e++) {
            int u = eu[e], v = ev[e];
            nb[(size_t)u * DEG + fill[u]++] = v;
            nb[(size_t)v * DEG + fill[v]++] = u;
        }
        for (int v = 0; v < n; v++) side[v] = -1;
        for (int s = 0; s < n && ok; s++) {
            if (side[s] != -1) continue;
            side[s] = 0;
            int head = 0, tail = 0;
            q[tail++] = s;
            while (head < tail && ok) {
                int u = q[head++];
                for (int k = 0; k < DEG; k++) {
                    int w = nb[(size_t)u * DEG + k];
                    if (side[w] == -1) {
                        side[w] = 1 - side[u];
                        q[tail++] = w;
                    } else if (side[w] == side[u]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
    }
    free(eu); free(ev); free(deg); free(fill); free(q);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    if (DEG < 1 || DEG > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    if (!load_start()) {
        printf("0 0\n");
        return 0;
    }
    R0 = malloc(sizeof(uint64_t) * (size_t)MAXN * MAXW);
    R1 = malloc(sizeof(uint64_t) * (size_t)MAXN * MAXW);

    if (eval_bad() == 0) save_valid();

    if (have_valid) {
        long long iter = 0;
        while (elapsed() < DEADLINE) {
            restore_valid();
            if (!do_insert()) break;
            long long cost = eval_bad();
            long long ebest = cost, stag = 0;
            while (cost > 0 && stag < PATIENCE) {
                if ((iter++ & 127) == 0 && elapsed() > DEADLINE) break;
                Mv mv;
                if (!do_switch(&mv)) continue;
                long long c2 = eval_bad();
                if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / TEMP)) {
                    cost = c2;
                } else {
                    undo_switch(&mv);
                }
                if (cost < ebest) { ebest = cost; stag = 0; }
                else stag++;
            }
            if (cost == 0) save_valid();
        }
    }

    if (!have_valid) {
        printf("0 0\n");
        return 0;
    }
    int cntA = 0;
    for (int v = 0; v < svN; v++)
        if (side[v] == 0) cntA++;
    printf("%d %d\n", svN, cntA * DEG);
    for (int v = 0; v < svN; v++) {
        if (side[v] != 0) continue;
        for (int k = 0; k < DEG; k++)
            printf("%d %d\n", v, svnb[(size_t)v * DEG + k]);
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
# Driver: baselines, then stage 1 (lift search) and stage 2 (insertion + switch
# repair started from the best valid graph). Every stage output is validated
# before it can replace the current best.
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

    # Overall deadline for all C work, leaving margin for compiles, parsing and validation.
    final = start + 0.9 * time_limit - 2.0

    # Stage 1: voltage-lift annealing over semidirect products.
    left = final - time.monotonic()
    if left >= 4.0:
        s1 = 0.5 * left - 1.0
        try:
            out = lib.run_c(LIFT_SOURCE, [d, D, seed, f"{s1:.2f}", best_n],
                            timeout=s1 + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Stage 2: grow the best valid graph by vertex insertion, repair by edge switches.
    left = final - time.monotonic()
    if left >= 4.0 and d >= 2 and D >= 2:
        s2 = left - 2.0
        try:
            out = lib.run_c(SWITCH_SOURCE, [d, D, seed + 1, f"{s2:.2f}"],
                            stdin_graph=best, timeout=s2 + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
