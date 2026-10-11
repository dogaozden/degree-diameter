"""Two-stage search for d-regular bipartite graphs of diameter <= D.

Stage 1 runs the voltage-lift annealer (lifts of semidirect products, with breakout
weights and an elite pool) to get a strong valid start.

Stage 2 is a new, unstructured search. It starts from the best valid graph and
repeatedly (a) adds two vertices, one on each side, by removing d disjoint edges and
rewiring their endpoints to the new vertices, which keeps every degree at d, and
(b) runs simulated annealing over degree-preserving bipartite edge swaps to drive
the number of bad ordered vertex pairs (distance > D) back to zero. Each success is
saved and the process repeats. Every returned graph is re-checked with lib.is_valid,
and a K_{d,d} fallback guarantees a valid answer.
"""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 engine: voltage lifts over semidirect products (unchanged search).
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
# Stage 2 engine: bipartite edge-swap annealing with vertex extension.
# ----------------------------------------------------------------------------

C_EDGE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define CHUNK 4000
#define T_HI 4.0
#define T_LO 0.3
#define MAXEXT 300

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

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Graph state: every edge is stored as (EA = A-side endpoint, EB = B-side endpoint). */
static int DEG, DIAM, N, M, MAXN, MAXM, W0;
static int *deg, *adjl, *EA, *EB, *bEA, *bEB;
static int best_n = 0, best_m = 0;
static uint64_t *R1, *R2;
static long long cur_cost;

static int has_nb(int v, int u) {
    const int *p = adjl + (size_t)v * DEG;
    for (int e = 0; e < deg[v]; e++) if (p[e] == u) return 1;
    return 0;
}

static void replace_nb(int v, int old, int nw) {
    int *p = adjl + (size_t)v * DEG;
    for (int e = 0; e < deg[v]; e++) if (p[e] == old) { p[e] = nw; return; }
}

static void rm_nb(int v, int u) {
    int *p = adjl + (size_t)v * DEG;
    for (int e = 0; e < deg[v]; e++) {
        if (p[e] == u) { p[e] = p[deg[v] - 1]; deg[v]--; return; }
    }
}

static void add_edge(int a, int b) {
    EA[M] = a; EB[M] = b; M++;
    adjl[(size_t)a * DEG + deg[a]++] = b;
    adjl[(size_t)b * DEG + deg[b]++] = a;
}

static void remove_pair(int a, int b) {
    for (int e = 0; e < M; e++) {
        if (EA[e] == a && EB[e] == b) {
            rm_nb(a, b);
            rm_nb(b, a);
            int last = M - 1;
            EA[e] = EA[last];
            EB[e] = EB[last];
            M--;
            return;
        }
    }
}

/* Bad ordered pairs: N*N minus the number of (v, w) with dist(v, w) <= DIAM. */
static long long eval_cost(void) {
    int Wn = (N + 63) >> 6;
    size_t tot = (size_t)N * Wn;
    uint64_t *cur = R1, *nxt = R2;
    memset(cur, 0, sizeof(uint64_t) * tot);
    for (int v = 0; v < N; v++) cur[(size_t)v * Wn + (v >> 6)] |= 1ULL << (v & 63);
    for (int lvl = 0; lvl < DIAM; lvl++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * Wn;
            const uint64_t *c = cur + (size_t)v * Wn;
            memcpy(o, c, sizeof(uint64_t) * (size_t)Wn);
            const int *p = adjl + (size_t)v * DEG;
            for (int e = 0; e < deg[v]; e++) {
                const uint64_t *u = cur + (size_t)p[e] * Wn;
                for (int w = 0; w < Wn; w++) o[w] |= u[w];
            }
            for (int w = 0; w < Wn; w++) if (o[w] != c[w]) changed = 1;
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long long cov = 0;
    for (size_t i = 0; i < tot; i++) cov += popc64(cur[i]);
    return (long long)N * N - cov;
}

/* Swap: edges (a,b),(c,d) become (a,d),(c,b). Caller checks validity. */
static void apply_swap(int i, int j, int a, int b, int c, int d) {
    replace_nb(a, b, d);
    replace_nb(b, a, c);
    replace_nb(c, d, b);
    replace_nb(d, c, a);
    EB[i] = d;
    EB[j] = b;
}

static void undo_swap(int i, int j, int a, int b, int c, int d) {
    replace_nb(a, d, b);
    replace_nb(d, a, c);
    replace_nb(c, b, d);
    replace_nb(b, c, a);
    EB[i] = b;
    EB[j] = d;
}

/* Add one A-side vertex x and one B-side vertex y, both of degree DEG.
   Remove DEG edges (a_k, b_k) with distinct endpoints; join x to every b_k and y to every a_k. */
static int extend(void) {
    if (N + 2 > MAXN || M < DEG) return 0;
    int ra[32], rb[32], ns = 0, tries = 0;
    while (ns < DEG && tries < 100000) {
        tries++;
        int e = rnd_int(M);
        int a = EA[e], b = EB[e], bad = 0;
        for (int k = 0; k < ns; k++) if (ra[k] == a || rb[k] == b) { bad = 1; break; }
        if (!bad) { ra[ns] = a; rb[ns] = b; ns++; }
    }
    if (ns < DEG) return 0;
    for (int k = 0; k < ns; k++) remove_pair(ra[k], rb[k]);
    int x = N, y = N + 1;
    N += 2;
    for (int k = 0; k < ns; k++) {
        add_edge(x, rb[k]);
        add_edge(ra[k], y);
    }
    return 1;
}

static void save_best(void) {
    if (N <= best_n) return;
    best_n = N;
    best_m = M;
    memcpy(bEA, EA, sizeof(int) * (size_t)M);
    memcpy(bEB, EB, sizeof(int) * (size_t)M);
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
    DEADLINE = atof(argv[4]);
    if (DEG < 1 || DEG > 32 || DIAM < 1) { printf("0 0\n"); return 0; }
    uint64_t sm = sd * 2654435761ULL + 99991ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 < 0) { printf("0 0\n"); return 0; }
    MAXN = n0 + 2 * MAXEXT + 2;
    MAXM = MAXN * DEG + 4;
    W0 = (MAXN + 63) >> 6;
    deg = calloc((size_t)MAXN, sizeof(int));
    adjl = calloc((size_t)MAXN * DEG, sizeof(int));
    EA = malloc(sizeof(int) * (size_t)MAXM);
    EB = malloc(sizeof(int) * (size_t)MAXM);
    bEA = malloc(sizeof(int) * (size_t)MAXM);
    bEB = malloc(sizeof(int) * (size_t)MAXM);
    R1 = malloc(sizeof(uint64_t) * (size_t)MAXN * W0);
    R2 = malloc(sizeof(uint64_t) * (size_t)MAXN * W0);
    int *tu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *tv = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *side = malloc(sizeof(int) * (size_t)MAXN);
    int *stk = malloc(sizeof(int) * (size_t)MAXN);

    int ok = 1;
    for (int i = 0; i < m0 && ok; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { ok = 0; break; }
        if (deg[u] >= DEG || deg[v] >= DEG || has_nb(u, v)) { ok = 0; break; }
        tu[i] = u; tv[i] = v;
        adjl[(size_t)u * DEG + deg[u]++] = v;
        adjl[(size_t)v * DEG + deg[v]++] = u;
    }
    if (!ok) { printf("0 0\n"); return 0; }

    N = n0;
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N && ok; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0 && ok) {
            int v = stk[--sp];
            for (int e = 0; e < deg[v]; e++) {
                int u = adjl[(size_t)v * DEG + e];
                if (side[u] < 0) { side[u] = 1 - side[v]; stk[sp++] = u; }
                else if (side[u] == side[v]) { ok = 0; break; }
            }
        }
    }
    if (!ok) { printf("0 0\n"); return 0; }

    M = 0;
    for (int i = 0; i < m0; i++) {
        int u = tu[i], v = tv[i];
        if (side[u] == 0) { EA[M] = u; EB[M] = v; }
        else { EA[M] = v; EB[M] = u; }
        M++;
    }
    if (M < 2) { printf("0 0\n"); return 0; }

    cur_cost = eval_cost();
    while (elapsed() < DEADLINE && M >= 2) {
        if (cur_cost == 0) {
            save_best();
            if (!extend()) break;
            cur_cost = eval_cost();
            continue;
        }
        for (int it = 0; it < CHUNK && cur_cost > 0; it++) {
            if ((it & 63) == 0 && elapsed() > DEADLINE) break;
            double temp = T_HI * pow(T_LO / T_HI, (double)it / CHUNK);
            int i = rnd_int(M), j = rnd_int(M);
            if (i == j) continue;
            int a = EA[i], b = EB[i], c = EA[j], d = EB[j];
            if (a == c || b == d) continue;
            if (has_nb(a, d) || has_nb(c, b)) continue;
            apply_swap(i, j, a, b, c, d);
            long long nc = eval_cost();
            if (nc <= cur_cost || rnd_unit() < exp(-(double)(nc - cur_cost) / temp)) {
                cur_cost = nc;
            } else {
                undo_swap(i, j, a, b, c, d);
            }
        }
    }
    if (cur_cost == 0) save_best();

    if (best_n > 0 && best_m > 0) {
        printf("%d %d\n", best_n, best_m);
        for (int i = 0; i < best_m; i++) printf("%d %d\n", bEA[i], bEB[i]);
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
# Driver: baselines, stage 1 lift search, stage 2 edge-swap extension.
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

    def left():
        return 0.93 * time_limit - (time.monotonic() - start) - 1.0

    # Stage 1: voltage-lift search, about half of the remaining budget.
    rem = left()
    if rem >= 1.0:
        budget1 = 0.5 * rem
        try:
            out = lib.run_c(C_LIFT, [d, D, seed, f"{budget1:.2f}", best_n],
                            timeout=budget1 + 5.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Stage 2: extend the best valid graph by edge-swap annealing (new search space).
    rem = left()
    if rem >= 1.0:
        try:
            out = lib.run_c(C_EDGE, [d, D, seed, f"{rem:.2f}"],
                            stdin_graph=best, timeout=rem + 5.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
