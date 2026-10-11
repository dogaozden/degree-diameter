import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Engine A (group lifts, from the parent): voltage lifts of semidirect products
# Z_m x| Z_k2 over K A-vertices and K B-vertices, annealed with breakout weights
# and an elite pool (ILS). Used to obtain a strong start graph.
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
# Engine B (new, unstructured): edge-switch annealing on a general bipartite
# graph with max degree DG. Starts from a valid graph given on stdin. The cost
# is the number of ordered vertex pairs at distance > DIAM, computed with
# bitset BFS. Moves are degree-preserving double-edge switches. When the graph
# is valid, two vertices (one per side) are inserted with degree DG built from
# edge subdivisions, which keeps the graph valid-or-nearly-valid and grows n.
# If annealing stagnates, the search reverts to the best valid graph.
# ----------------------------------------------------------------------------

GROW_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define EXTRA 900
#define STAG 30000
#define T0S 6.0
#define T1S 0.2

static uint64_t rs[2];
static struct timespec TS0;
static double DEADLINE;
static int DG, DIAM, n, M, CAP, WCAP, bestN, bestM;
static unsigned char *mat;
static int *adjl, *degv, *side, *ea, *eb, *bestEa, *bestEb;
static uint64_t *bsA, *bsB;

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

static int rnd_int(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - TS0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - TS0.tv_nsec);
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Edge (ea[i], eb[i]) has ea on side 0 and eb on side 1. mat[a*CAP+b] marks edges. */
static void add_raw(int a, int b) {
    mat[(size_t)a * CAP + b] = 1;
    adjl[(size_t)a * DG + degv[a]++] = b;
    adjl[(size_t)b * DG + degv[b]++] = a;
    ea[M] = a; eb[M] = b; M++;
}

static void load(int nn, int m, const int *xa, const int *xb) {
    memset(mat, 0, (size_t)CAP * CAP);
    memset(degv, 0, sizeof(int) * (size_t)CAP);
    M = 0;
    n = nn;
    for (int i = 0; i < m; i++) {
        int a = xa[i], b = xb[i];
        if (mat[(size_t)a * CAP + b] || degv[a] >= DG || degv[b] >= DG) continue;
        add_raw(a, b);
    }
}

static void save_best(void) {
    bestN = n;
    bestM = M;
    memcpy(bestEa, ea, sizeof(int) * (size_t)M);
    memcpy(bestEb, eb, sizeof(int) * (size_t)M);
}

/* Replace neighbour `old` of v by `nw` in v's list. */
static void repl(int v, int old, int nw) {
    int *p = adjl + (size_t)v * DG;
    for (int i = 0; i < degv[v]; i++)
        if (p[i] == old) { p[i] = nw; return; }
}

/* Edges k=(a,b), l=(c,e) become (a,e), (c,b). Degrees are unchanged.
   Applying it again to the same pair of edge slots undoes it. */
static void do_switch(int k, int l) {
    int a = ea[k], b = eb[k], c = ea[l], e = eb[l];
    ea[k] = a; eb[k] = e;
    ea[l] = c; eb[l] = b;
    mat[(size_t)a * CAP + b] = 0;
    mat[(size_t)c * CAP + e] = 0;
    mat[(size_t)a * CAP + e] = 1;
    mat[(size_t)c * CAP + b] = 1;
    repl(a, b, e);
    repl(c, e, b);
    repl(b, a, c);
    repl(e, c, a);
}

/* Number of ordered pairs (v,w) with dist(v,w) > DIAM. Zero iff valid. */
static long long eval_bad(void) {
    int W = (n + 63) >> 6;
    uint64_t *A = bsA, *B = bsB;
    for (int v = 0; v < n; v++) {
        uint64_t *row = A + (size_t)v * WCAP;
        for (int w = 0; w < W; w++) row[w] = 0;
        row[v >> 6] |= 1ULL << (v & 63);
    }
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = B + (size_t)v * WCAP;
            const uint64_t *src = A + (size_t)v * WCAP;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            const int *nb = adjl + (size_t)v * DG;
            for (int i = 0; i < degv[v]; i++) {
                const uint64_t *s2 = A + (size_t)nb[i] * WCAP;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        uint64_t *t = A; A = B; B = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *row = A + (size_t)v * WCAP;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(row[w]);
        bad += n - c;
    }
    return bad;
}

/* Insert two vertices x (side 0) and y (side 1). Each insertion takes an edge (a,b)
   and replaces it by (a,y) and (x,b), so degrees of a and b are kept and x, y gain. */
static void grow(void) {
    int x = n, y = n + 1;
    side[x] = 0;
    side[y] = 1;
    n += 2;
    int tries = 0;
    while (degv[x] < DG && degv[y] < DG && tries < 400000) {
        tries++;
        int k = rnd_int(M);
        int a = ea[k], b = eb[k];
        if (mat[(size_t)x * CAP + b] || mat[(size_t)a * CAP + y]) continue;
        mat[(size_t)a * CAP + b] = 0;
        repl(b, a, x);
        repl(a, b, y);
        mat[(size_t)a * CAP + y] = 1;
        adjl[(size_t)x * DG + degv[x]++] = b;
        adjl[(size_t)y * DG + degv[y]++] = a;
        mat[(size_t)x * CAP + b] = 1;
        ea[k] = a; eb[k] = y;
        ea[M] = x; eb[M] = b; M++;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit < graph\n");
        return 1;
    }
    timespec_get(&TS0, TIME_UTC);
    DG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);

    int n0 = 0, m0 = 0;
    if (DG < 1 || DIAM < 1 || scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    int *u = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *v = malloc(sizeof(int) * (size_t)(m0 + 1));
    int mm = 0;
    for (int i = 0; i < m0; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a < 0 || b < 0 || a >= n0 || b >= n0) { printf("0 0\n"); return 0; }
        u[mm] = a; v[mm] = b; mm++;
    }
    m0 = mm;

    int *col = malloc(sizeof(int) * (size_t)n0);
    for (int i = 0; i < n0; i++) col[i] = -1;
    for (int s = 0; s < n0; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int changed = 1;
        while (changed) {
            changed = 0;
            for (int i = 0; i < m0; i++) {
                int a = u[i], b = v[i];
                if (col[a] >= 0 && col[b] < 0) { col[b] = 1 - col[a]; changed = 1; }
                else if (col[b] >= 0 && col[a] < 0) { col[a] = 1 - col[b]; changed = 1; }
                else if (col[a] >= 0 && col[a] == col[b]) { printf("0 0\n"); return 0; }
            }
        }
    }

    CAP = n0 + EXTRA;
    WCAP = (CAP + 63) / 64;
    int ECAP = CAP * DG + 16;
    mat = calloc((size_t)CAP * CAP, 1);
    adjl = malloc(sizeof(int) * (size_t)CAP * DG);
    degv = calloc((size_t)CAP, sizeof(int));
    side = calloc((size_t)CAP, sizeof(int));
    ea = malloc(sizeof(int) * (size_t)ECAP);
    eb = malloc(sizeof(int) * (size_t)ECAP);
    bestEa = malloc(sizeof(int) * (size_t)ECAP);
    bestEb = malloc(sizeof(int) * (size_t)ECAP);
    bsA = malloc(sizeof(uint64_t) * (size_t)CAP * WCAP);
    bsB = malloc(sizeof(uint64_t) * (size_t)CAP * WCAP);
    for (int i = 0; i < n0; i++) side[i] = col[i];

    int *xa = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *xb = malloc(sizeof(int) * (size_t)(m0 + 1));
    for (int i = 0; i < m0; i++) {
        if (col[u[i]] == 0) { xa[i] = u[i]; xb[i] = v[i]; }
        else { xa[i] = v[i]; xb[i] = u[i]; }
    }

    uint64_t sm = sd * 2654435761ULL + 999ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    bestN = 0; bestM = 0;
    load(n0, m0, xa, xb);
    long long cur = eval_bad();
    if (cur == 0) save_best();

    int since = 0;
    while (elapsed() < DEADLINE) {
        if (M == 0) break;
        if (cur == 0) {
            save_best();
            if (n + 2 > CAP) break;
            grow();
            cur = eval_bad();
            since = 0;
            continue;
        }
        since++;
        if (since >= STAG) {
            /* Stagnation: restart from the best valid graph. */
            if (bestN > 0) {
                load(bestN, bestM, bestEa, bestEb);
                cur = eval_bad();
            }
            since = 0;
            continue;
        }
        int k = -1, l = -1, ok = 0;
        for (int tr = 0; tr < 64 && !ok; tr++) {
            k = rnd_int(M);
            l = rnd_int(M);
            if (k == l) continue;
            int a = ea[k], b = eb[k], c = ea[l], e = eb[l];
            if (a == c || b == e) continue;
            if (mat[(size_t)a * CAP + e] || mat[(size_t)c * CAP + b]) continue;
            ok = 1;
        }
        if (!ok) continue;
        double frac = (double)since / STAG;
        double T = T0S * pow(T1S / T0S, frac);
        do_switch(k, l);
        long long nb = eval_bad();
        if (nb <= cur || rnd_unit() < exp(-(double)(nb - cur) / T)) {
            cur = nb;
        } else {
            do_switch(k, l);
        }
    }
    if (cur == 0) save_best();

    if (bestN > 0) {
        printf("%d %d\n", bestN, bestM);
        for (int i = 0; i < bestM; i++) printf("%d %d\n", bestEa[i], bestEb[i]);
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
# Driver: baselines, then group-lift search (engine A) to get a strong start,
# then unstructured edge-switch growth (engine B) from that start.
# Every candidate is checked with lib.is_valid; the best valid one is returned.
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

    # Two compiles plus two runs. Reserve 4 s for compiles, parsing and validation.
    remaining = 0.90 * time_limit - (time.monotonic() - start) - 4.0
    if remaining < 2.0:
        return best

    # Phase A: group-lift search gives a strong start graph (never 0 unless it fails).
    p1 = 0.60 * remaining
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{p1:.2f}", 0], timeout=p1 + 10.0)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except Exception:
        pass

    # Phase B: unstructured edge-switch growth from the best valid graph so far.
    left = 0.90 * time_limit - (time.monotonic() - start) - 2.0
    if left >= 2.0:
        try:
            out = lib.run_c(GROW_SOURCE, [d, D, seed, f"{left:.2f}"],
                            stdin_graph=best, timeout=left + 10.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
