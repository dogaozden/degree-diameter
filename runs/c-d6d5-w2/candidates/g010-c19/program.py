import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 engine (unchanged parent): voltage lifts of semidirect products
# Z_m x| Z_k over a base of K A-vertices and K B-vertices, searched by
# simulated annealing with breakout weights and an elite-pool ILS.
# It gives the group-lift graphs that the edge-switch stage starts from.
# ----------------------------------------------------------------------------

PARENT_C_SOURCE = r"""
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
# Stage 2 engine (new, substantially different search space): no group.
# A bipartite graph with max degree DEG and sides A (ids 0..h-1) and B
# (ids h..2h-1). The state is any graph; moves are edge switches
# (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), which keep every degree. Cost is the
# number of ordered vertex pairs at distance > DIAM, computed exactly with
# bitset BFS. Simulated annealing drives cost to 0. When it succeeds, the
# graph grows by one vertex per side: a random matching of up to DEG edges
# is removed and new vertices a', b' are joined to its endpoints. Degrees
# never exceed DEG, so the result stays bipartite and valid whenever cost
# is 0. The best valid snapshot is printed at the end.
# ----------------------------------------------------------------------------

EDGE_C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define HCAP 2048
#define T_HI 3.0
#define T_LO 0.2
#define BASE_STAGE 1.5

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

static int DEG, DIAM, HMAX, h, M, NE;
static int *eu, *ev;
static unsigned char *mat;
static int *cntd, *adj;
static uint64_t *reachA, *reachB;
static int *sv_eu, *sv_ev, sv_h, sv_M, have_snap;
static int *ord, *selA, *selB;
static unsigned char *usedA, *usedB;

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int a, int b) {
    eu[M] = a;
    ev[M] = b;
    M++;
    mat[(size_t)a * HMAX + b] = 1;
}

static void remove_edge(int a, int b) {
    for (int e = 0; e < M; e++) {
        if (eu[e] == a && ev[e] == b) {
            M--;
            eu[e] = eu[M];
            ev[e] = ev[M];
            break;
        }
    }
    mat[(size_t)a * HMAX + b] = 0;
}

/* Exact number of ordered vertex pairs at distance > DIAM (0 iff valid). */
static long long eval_cost(void) {
    int nv = 2 * h;
    int W = (nv + 63) >> 6;
    for (int v = 0; v < nv; v++) cntd[v] = 0;
    for (int e = 0; e < M; e++) {
        int a = eu[e], b = h + ev[e];
        adj[(size_t)a * DEG + cntd[a]++] = b;
        adj[(size_t)b * DEG + cntd[b]++] = a;
    }
    uint64_t *cur = reachA, *nxt = reachB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)nv * W);
    for (int v = 0; v < nv; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        uint64_t diff = 0;
        for (int v = 0; v < nv; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *in = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) o[w] = in[w];
            for (int k = 0; k < cntd[v]; k++) {
                const uint64_t *s = cur + (size_t)adj[(size_t)v * DEG + k] * W;
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
            for (int w = 0; w < W; w++) diff |= o[w] ^ in[w];
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
        if (!diff) break;
    }
    long long bad = 0;
    for (int v = 0; v < nv; v++) {
        int c = 0;
        const uint64_t *p = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += popc(p[w]);
        bad += nv - c;
    }
    return bad;
}

static void save_snapshot(void) {
    memcpy(sv_eu, eu, sizeof(int) * (size_t)M);
    memcpy(sv_ev, ev, sizeof(int) * (size_t)M);
    sv_h = h;
    sv_M = M;
    have_snap = 1;
}

static void restore_snapshot(void) {
    h = sv_h;
    M = sv_M;
    memcpy(eu, sv_eu, sizeof(int) * (size_t)M);
    memcpy(ev, sv_ev, sizeof(int) * (size_t)M);
    memset(mat, 0, (size_t)HMAX * HMAX);
    for (int e = 0; e < M; e++) mat[(size_t)eu[e] * HMAX + ev[e]] = 1;
}

/* Remove a random matching of up to DEG edges, then add vertices a' = b' = h. */
static void grow_one(void) {
    for (int e = 0; e < M; e++) ord[e] = e;
    for (int i = M - 1; i > 0; i--) {
        int j = rnd_int(i + 1);
        int t = ord[i]; ord[i] = ord[j]; ord[j] = t;
    }
    memset(usedA, 0, (size_t)HMAX);
    memset(usedB, 0, (size_t)HMAX);
    int k = 0;
    for (int i = 0; i < M && k < DEG; i++) {
        int e = ord[i];
        int a = eu[e], b = ev[e];
        if (!usedA[a] && !usedB[b]) {
            usedA[a] = 1;
            usedB[b] = 1;
            selA[k] = a;
            selB[k] = b;
            k++;
        }
    }
    for (int i = 0; i < k; i++) remove_edge(selA[i], selB[i]);
    int na = h;
    h++;
    for (int i = 0; i < k; i++) {
        add_edge(na, selB[i]);
        add_edge(selA[i], na);
    }
}

/* Simulated annealing with edge switches. Returns the cost of the final state. */
static long long anneal(long long cur, double stage_end) {
    double t0 = elapsed();
    double dur = stage_end - t0;
    if (dur < 1e-3) dur = 1e-3;
    double temp = T_HI;
    long long it = 0;
    while (cur > 0) {
        if ((it & 31) == 0) {
            double now = elapsed();
            if (now >= stage_end || now >= DEADLINE) break;
            double frac = (now - t0) / dur;
            if (frac > 1.0) frac = 1.0;
            temp = T_HI * pow(T_LO / T_HI, frac);
        }
        it++;
        int e1 = rnd_int(M), e2 = rnd_int(M);
        if (e1 == e2) continue;
        int a1 = eu[e1], b1 = ev[e1], a2 = eu[e2], b2 = ev[e2];
        if (a1 == a2 || b1 == b2) continue;
        if (mat[(size_t)a1 * HMAX + b2] || mat[(size_t)a2 * HMAX + b1]) continue;
        mat[(size_t)a1 * HMAX + b1] = 0;
        mat[(size_t)a2 * HMAX + b2] = 0;
        mat[(size_t)a1 * HMAX + b2] = 1;
        mat[(size_t)a2 * HMAX + b1] = 1;
        ev[e1] = b2;
        ev[e2] = b1;
        long long c2 = eval_cost();
        if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / temp)) {
            cur = c2;
        } else {
            mat[(size_t)a1 * HMAX + b2] = 0;
            mat[(size_t)a2 * HMAX + b1] = 0;
            mat[(size_t)a1 * HMAX + b1] = 1;
            mat[(size_t)a2 * HMAX + b2] = 1;
            ev[e1] = b1;
            ev[e2] = b2;
        }
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit   (stdin: optional graph, A ids < n/2)\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    if (DEG < 3 || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }

    /* Bipartite Moore bound 2 * sum_{i<DIAM} (DEG-1)^i, capped. */
    long long mb = 0, p = 1;
    for (int i = 0; i < DIAM; i++) {
        mb += p;
        if (mb > 100000) break;
        p *= (DEG - 1);
        if (p > 100000000LL) p = 100000000LL;
    }
    mb *= 2;
    HMAX = (int)(mb / 2);
    if (HMAX > HCAP) HMAX = HCAP;
    if (HMAX < DEG) {
        printf("0 0\n");
        return 0;
    }

    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    NE = DEG * HMAX + DEG + 4;
    eu = malloc(sizeof(int) * (size_t)NE);
    ev = malloc(sizeof(int) * (size_t)NE);
    sv_eu = malloc(sizeof(int) * (size_t)NE);
    sv_ev = malloc(sizeof(int) * (size_t)NE);
    ord = malloc(sizeof(int) * (size_t)NE);
    mat = calloc((size_t)HMAX * HMAX, 1);
    cntd = malloc(sizeof(int) * (size_t)(2 * HMAX));
    adj = malloc(sizeof(int) * (size_t)2 * HMAX * DEG);
    int WMAX = (2 * HMAX + 63) >> 6;
    reachA = malloc(sizeof(uint64_t) * (size_t)2 * HMAX * WMAX);
    reachB = malloc(sizeof(uint64_t) * (size_t)2 * HMAX * WMAX);
    selA = malloc(sizeof(int) * (size_t)DEG);
    selB = malloc(sizeof(int) * (size_t)DEG);
    usedA = calloc((size_t)HMAX, 1);
    usedB = calloc((size_t)HMAX, 1);
    have_snap = 0;
    sv_h = 0;
    sv_M = 0;

    /* Optional start graph on stdin: "n m" then edges; side A = ids < n/2. */
    h = 0;
    M = 0;
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) == 2 && n0 > 0 && m0 > 0 && n0 % 2 == 0 && n0 / 2 <= HMAX) {
        int hh = n0 / 2, ok = 1;
        int *dg = calloc((size_t)n0, sizeof(int));
        for (int i = 0; i < m0 && ok; i++) {
            int x, y;
            if (scanf("%d %d", &x, &y) != 2) { ok = 0; break; }
            if (x > y) { int t = x; x = y; y = t; }
            if (x < 0 || x >= hh || y < hh || y >= n0) { ok = 0; break; }
            int a = x, b = y - hh;
            if (mat[(size_t)a * HMAX + b] || M >= NE) { ok = 0; break; }
            add_edge(a, b);
            dg[x]++;
            dg[y]++;
        }
        for (int v = 0; v < n0 && ok; v++)
            if (dg[v] > DEG) ok = 0;
        free(dg);
        if (ok) {
            h = hh;
        } else {
            memset(mat, 0, (size_t)HMAX * HMAX);
            M = 0;
        }
    }
    if (h == 0) {
        /* Default start: K_{DEG,DEG}, which is valid for DIAM >= 2. */
        h = DEG;
        M = 0;
        for (int a = 0; a < h; a++)
            for (int s = 0; s < DEG; s++) add_edge(a, (a + s) % h);
    }

    long long cur = eval_cost();
    int fails = 0;
    double stage = BASE_STAGE;
    while (elapsed() < DEADLINE) {
        if (cur == 0) {
            save_snapshot();
            if (h >= HMAX) break;
            grow_one();
            cur = eval_cost();
            fails = 0;
            stage = BASE_STAGE;
            continue;
        }
        double se = elapsed() + stage;
        if (se > DEADLINE) se = DEADLINE;
        cur = anneal(cur, se);
        if (cur > 0 && elapsed() < DEADLINE) {
            fails++;
            stage = BASE_STAGE * pow(1.3, fails);
            if (stage > 25.0) stage = 25.0;
            if (have_snap && fails % 3 == 0) {
                restore_snapshot();
                cur = eval_cost();
            }
        }
    }
    if (cur == 0) save_snapshot();

    if (have_snap) {
        printf("%d %d\n", 2 * sv_h, sv_M);
        for (int e = 0; e < sv_M; e++)
            printf("%d %d\n", sv_eu[e], sv_h + sv_ev[e]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Baselines and driver.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()

    def spent():
        return time.monotonic() - start

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        cyc = [(i, (i + 1) % n) for i in range(n)]
        if lib.is_valid(n, cyc, d, D):
            return n, cyc
        return lib.haar_graph(d, range(d))

    # Safe fallback: K_{d,d} (valid for D >= 2).
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

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Stage 1: group-lift search (the parent engine). It produces the
    # record-level seed. Budget: about 36% of the time, minus a compile reserve.
    b1 = 0.36 * time_limit - spent() - 1.0
    if b1 >= 1.0:
        try:
            out = lib.run_c(PARENT_C_SOURCE, [d, D, seed, f"{b1:.2f}", best_n],
                            timeout=b1 + 8.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    # Stage 2: edge-switch annealing that grows the best valid graph by
    # one vertex per side whenever it reaches zero cost. Most of the rest of
    # the budget goes here, with a reserve for compile and validation.
    b2 = 0.9 * time_limit - spent() - 2.5
    if b2 >= 2.0:
        try:
            out = lib.run_c(EDGE_C_SOURCE, [d, D, seed, f"{b2:.2f}"],
                            stdin_graph=best, timeout=b2 + 8.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
