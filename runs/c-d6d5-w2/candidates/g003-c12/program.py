import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Engine A (unchanged parent construction): voltage lifts of semidirect products
# Z_m x| Z_k2 over a base of K A-vertices and K B-vertices, searched by simulated
# annealing with breakout weights and an elite-pool iterated local search.
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
# Engine B (new construction): grow a d-regular bipartite graph by adding one
# A-vertex and one B-vertex at a time. The new vertices take over d edges
# (x_i, y_i) that are removed, so every degree stays d. Then 2-switch moves
# (which keep the graph d-regular and bipartite) are annealed to minimise the
# number of ordered vertex pairs at distance > D. A successful grow step is
# kept; a failed one is rolled back to the last valid graph.
#
# Input (stdin): "n m" then m lines "a b", with a < n/2 <= b (regular bipartite).
# Arguments: d D seed time_limit cap, cap = capacity on each side.
# Output: "n m" and the edges in the same format, or "0 0".
# ----------------------------------------------------------------------------

GROW_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define ATT_IT 6000

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;
static int DEG, DIAM, NCAP, N, W;
static int *adj;
static int *saved_adj;
static int saved_N;
static uint64_t *Rcur, *Rnxt;
static size_t ADJSZ;

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

/* Vertex slots: A-vertex i is slot i; B-vertex j is slot NCAP + j. Active: A 0..N-1, B 0..N-1. */
static inline int slot(int k) { return k < N ? k : NCAP + (k - N); }

static int find_idx(int v, int u) {
    const int *av = adj + (size_t)v * DEG;
    for (int k = 0; k < DEG; k++)
        if (av[k] == u) return k;
    return -1;
}

static int has_edge(int a, int b) { return find_idx(a, b) >= 0; }

static void replace_nb(int v, int old, int nw) {
    int k = find_idx(v, old);
    adj[(size_t)v * DEG + k] = nw;
}

/* Edges (a,b),(c,e) with a,c in A and b,e in B become (a,e),(c,b). Requires (a,e),(c,b) absent. */
static void do_switch(int a, int b, int c, int e) {
    replace_nb(a, b, e);
    replace_nb(b, a, c);
    replace_nb(c, e, b);
    replace_nb(e, c, a);
}

/* Number of ordered pairs of active vertices at distance > DIAM. */
static long long eval_bad(void) {
    int n2 = 2 * N;
    for (int k = 0; k < n2; k++) {
        int v = slot(k);
        uint64_t *r = Rcur + (size_t)v * W;
        memset(r, 0, sizeof(uint64_t) * (size_t)W);
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int k = 0; k < n2; k++) {
            int v = slot(k);
            uint64_t *dst = Rnxt + (size_t)v * W;
            memcpy(dst, Rcur + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            const int *av = adj + (size_t)v * DEG;
            for (int e = 0; e < DEG; e++) {
                const uint64_t *su = Rcur + (size_t)av[e] * W;
                for (int w = 0; w < W; w++) dst[w] |= su[w];
            }
        }
        uint64_t *t = Rcur; Rcur = Rnxt; Rnxt = t;
    }
    long long bad = 0;
    for (int k = 0; k < n2; k++) {
        int v = slot(k);
        const uint64_t *r = Rcur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(r[w]);
        bad += n2 - c;
    }
    return bad;
}

/* Remove DEG disjoint edges (x_i, y_i) and attach them to a new A-vertex N and a new B-vertex N. */
static int grow_once(void) {
    if (N >= NCAP || DEG > N) return 0;
    int *xs = malloc(sizeof(int) * (size_t)DEG);
    int *ys = malloc(sizeof(int) * (size_t)DEG);
    int ok = 0;
    for (int tr = 0; tr < 300 && !ok; tr++) {
        ok = 1;
        for (int i = 0; i < DEG && ok; i++) {
            int x, dupx;
            do {
                x = rnd_int(N);
                dupx = 0;
                for (int j = 0; j < i; j++)
                    if (xs[j] == x) dupx = 1;
            } while (dupx);
            int y = adj[(size_t)x * DEG + rnd_int(DEG)];
            for (int j = 0; j < i; j++)
                if (ys[j] == y) ok = 0;
            xs[i] = x;
            ys[i] = y;
        }
    }
    if (ok) {
        int a = N, b = NCAP + N;
        for (int i = 0; i < DEG; i++) {
            replace_nb(xs[i], ys[i], b);
            replace_nb(ys[i], xs[i], a);
            adj[(size_t)a * DEG + i] = ys[i];
            adj[(size_t)b * DEG + i] = xs[i];
        }
        N++;
    }
    free(xs);
    free(ys);
    return ok;
}

/* Simulated annealing over 2-switches on the bad-pair count. Returns 1 if cost reaches 0. */
static int sa(int maxit, long long cur) {
    for (int it = 0; it < maxit && cur > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) return 0;
        int x1 = rnd_int(N), x2 = rnd_int(N);
        if (x1 == x2) continue;
        int y1 = adj[(size_t)x1 * DEG + rnd_int(DEG)];
        int y2 = adj[(size_t)x2 * DEG + rnd_int(DEG)];
        if (has_edge(x1, y2) || has_edge(x2, y1)) continue;
        do_switch(x1, y1, x2, y2);
        long long nb = eval_bad();
        long long delta = nb - cur;
        double frac = (double)it / (double)maxit;
        double temp = (0.2 + 0.02 * (double)cur) * (1.0 - frac) + 0.02;
        if (delta <= 0 || rnd_unit() < exp(-(double)delta / temp)) {
            cur = nb;
        } else {
            do_switch(x1, y2, x2, y1);
        }
    }
    return cur == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed time_limit cap\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int cap_req = atoi(argv[5]);
    uint64_t sm = sd * 2654435761ULL + 99991ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int n0 = 0, m0 = 0;
    if (DEG < 1 || DIAM < 1 || scanf("%d %d", &n0, &m0) != 2 || n0 < 2 || (n0 & 1) ||
        m0 != (n0 / 2) * DEG) {
        printf("0 0\n");
        return 0;
    }
    int N0 = n0 / 2;
    NCAP = cap_req > N0 ? cap_req : N0;
    N = N0;
    W = (2 * NCAP + 63) / 64;
    ADJSZ = (size_t)2 * NCAP * DEG;
    adj = calloc(ADJSZ, sizeof(int));
    saved_adj = calloc(ADJSZ, sizeof(int));
    int *cnt = calloc((size_t)2 * NCAP, sizeof(int));
    Rcur = malloc(sizeof(uint64_t) * (size_t)2 * NCAP * W);
    Rnxt = malloc(sizeof(uint64_t) * (size_t)2 * NCAP * W);

    int bad_input = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { bad_input = 1; break; }
        if (u > v) { int t = u; u = v; v = t; }
        if (!(u >= 0 && u < N0 && v >= N0 && v < n0)) { bad_input = 1; break; }
        int j = v - N0;
        if (cnt[u] >= DEG || cnt[NCAP + j] >= DEG) { bad_input = 1; break; }
        for (int k = 0; k < cnt[u]; k++)
            if (adj[(size_t)u * DEG + k] == NCAP + j) bad_input = 1;
        if (bad_input) break;
        adj[(size_t)u * DEG + cnt[u]++] = NCAP + j;
        adj[(size_t)(NCAP + j) * DEG + cnt[NCAP + j]++] = u;
    }
    for (int k = 0; k < N0 && !bad_input; k++)
        if (cnt[k] != DEG || cnt[NCAP + k] != DEG) bad_input = 1;
    if (bad_input) {
        printf("0 0\n");
        return 0;
    }

    int valid = (eval_bad() == 0) ? 1 : sa(2 * ATT_IT, eval_bad());
    if (!valid) {
        printf("0 0\n");
        return 0;
    }
    memcpy(saved_adj, adj, sizeof(int) * ADJSZ);
    saved_N = N;

    while (elapsed() < DEADLINE && N < NCAP) {
        if (!grow_once()) continue;
        long long b2 = eval_bad();
        int ok = (b2 == 0) ? 1 : sa(ATT_IT, b2);
        if (ok) {
            memcpy(saved_adj, adj, sizeof(int) * ADJSZ);
            saved_N = N;
        } else {
            memcpy(adj, saved_adj, sizeof(int) * ADJSZ);
            N = saved_N;
        }
    }

    memcpy(adj, saved_adj, sizeof(int) * ADJSZ);
    N = saved_N;
    printf("%d %d\n", 2 * N, N * DEG);
    for (int a = 0; a < N; a++)
        for (int k = 0; k < DEG; k++) {
            int b = adj[(size_t)a * DEG + k] - NCAP;
            printf("%d %d\n", a, N + b);
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


def _regular_sides(n, edges, d):
    """If (n, edges) is d-regular bipartite with equal sides, relabel it for the grow engine:
    A-vertices 0..N-1, B-vertices N..2N-1, with every edge joining A to B. Otherwise None."""
    adj = lib.adjacency(n, edges)
    if any(len(a) != d for a in adj):
        return None
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    A = [v for v in range(n) if color[v] == 0]
    B = [v for v in range(n) if color[v] == 1]
    if not A or len(A) != len(B):
        return None
    N = len(A)
    ia = {v: i for i, v in enumerate(A)}
    ib = {v: i for i, v in enumerate(B)}
    out = []
    for u, v in edges:
        if color[u] == 0:
            out.append((ia[u], N + ib[v]))
        else:
            out.append((ia[v], N + ib[u]))
    return 2 * N, out


# ----------------------------------------------------------------------------
# Driver: baselines, then engine A (lift search) for half the budget, then
# engine B (grow + repair) started from the best graph found so far.
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

    # Engine A: lift search, half of the usable budget.
    total = 0.92 * time_limit - (time.monotonic() - start) - 1.5
    if total >= 1.0:
        budget_a = 0.5 * total
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget_a:.2f}", best_n],
                            timeout=budget_a + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Engine B: grow the best regular bipartite graph by one A/B pair at a time.
    budget_b = 0.92 * time_limit - (time.monotonic() - start) - 2.0
    if d >= 3 and budget_b >= 2.0:
        sides = _regular_sides(best[0], best[1], d)
        if sides is not None:
            cap = sides[0] // 2 + 40
            try:
                out = lib.run_c(GROW_C, [d, D, seed + 1, f"{budget_b:.2f}", cap],
                                stdin_graph=sides, timeout=budget_b + 8.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
