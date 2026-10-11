import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Strategy (high-risk variant).
#
# Stage 0: cheap algebraic baselines (PG(2,q) incidence, K_{d,d}, and W(q) only
#          for D = 4). Nothing here is ever discarded; it is the fallback.
# Stage 1: the voltage-lift annealer over semidirect products (the parent's
#          engine, unchanged). It supplies the strong structured start, e.g.
#          the 684 record for d=6, D=5. It gets about half of the search budget.
# Stage 2: a substantially different search, in C. It works directly on
#          unstructured d-regular bipartite graphs, with no group structure.
#          The state is a set of edges between sides A and B, and every move
#          is a degree-preserving 2-switch. The cost is the number of ordered
#          vertex pairs at distance > D, computed with bitset BFS. The search
#          is simulated annealing with reheats from the best state. It is a
#          growing ladder: after reaching zero cost at size n, it inserts a
#          new vertex pair (removing a random matching of d edges and
#          reconnecting it through the new pair, which keeps the graph
#          d-regular and bipartite), then anneals again. The start graph is
#          the best structured graph from Stage 1, when it is regular and
#          balanced. Otherwise the search starts from a random regular graph.
#
# Every returned graph is checked with lib.is_valid. On any failure, the
# best algebraic graph is returned.
# ----------------------------------------------------------------------------

# ----------------------------------------------------------------------------
# Stage 1 engine: voltage lifts of semidirect products (parent engine).
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
# Stage 2 engine: unstructured d-regular bipartite graphs, 2-switch annealing,
# bitset distance cost, and a growing ladder of vertex-pair insertions.
# ----------------------------------------------------------------------------

C_SOURCE2 = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 32
#define MAXA 2048
#define MAXE (MAXA * MAXD)
#define MAXN (2 * MAXA)
#define WMAX ((MAXN + 63) / 64)
#define CYC 8000
#define TSTART 20.0
#define TEND 0.5

static int DG, DIAM, NA, NB, M;
static int eu[MAXE], ev[MAXE];
static int beu[MAXE], bev[MAXE];
static int veu[MAXE], vev[MAXE];
static int vNA = 0, vM = 0, have_valid = 0;
static int adjA[MAXA * MAXD], adjB[MAXA * MAXD];
static int gadj[MAXN * MAXD];
static uint64_t RA[MAXN * WMAX], RB[MAXN * WMAX];
static int cntA[MAXA], cntB[MAXA];
static int usedA[MAXA], usedB[MAXA];
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

static int has_edge(int a, int b) {
    const int *p = adjA + (size_t)a * DG;
    for (int k = 0; k < DG; k++)
        if (p[k] == b) return 1;
    return 0;
}

static void repl(int *p, int from, int to) {
    for (int k = 0; k < DG; k++)
        if (p[k] == from) { p[k] = to; return; }
}

/* Edges i=(a1,b1), j=(a2,b2) become (a1,b2), (a2,b1). Applying it twice undoes it. */
static void do_switch(int i, int j) {
    int a1 = eu[i], b1 = ev[i], a2 = eu[j], b2 = ev[j];
    repl(adjA + (size_t)a1 * DG, b1, b2);
    repl(adjA + (size_t)a2 * DG, b2, b1);
    repl(adjB + (size_t)b1 * DG, a1, a2);
    repl(adjB + (size_t)b2 * DG, a2, a1);
    eu[i] = a1; ev[i] = b2;
    eu[j] = a2; ev[j] = b1;
}

static int rebuild(void) {
    if (NA != NB || NA < 1 || NA > MAXA || M != NA * DG) return 0;
    memset(cntA, 0, sizeof(int) * (size_t)NA);
    memset(cntB, 0, sizeof(int) * (size_t)NB);
    for (int e = 0; e < M; e++) {
        int a = eu[e], b = ev[e];
        if (a < 0 || a >= NA || b < 0 || b >= NB) return 0;
        if (cntA[a] >= DG || cntB[b] >= DG) return 0;
        adjA[a * DG + cntA[a]++] = b;
        adjB[b * DG + cntB[b]++] = a;
    }
    for (int a = 0; a < NA; a++) {
        if (cntA[a] != DG) return 0;
        for (int k = 0; k < DG; k++)
            for (int l = 0; l < k; l++)
                if (adjA[a * DG + k] == adjA[a * DG + l]) return 0;
    }
    for (int b = 0; b < NB; b++) {
        if (cntB[b] != DG) return 0;
        for (int k = 0; k < DG; k++)
            for (int l = 0; l < k; l++)
                if (adjB[b * DG + k] == adjB[b * DG + l]) return 0;
    }
    return 1;
}

/* Ordered count of (v, w) with dist(v, w) > DIAM. Zero iff the graph is valid. */
static long long eval_cost(void) {
    int n = 2 * NA;
    int W = (n + 63) >> 6;
    for (int a = 0; a < NA; a++)
        for (int k = 0; k < DG; k++)
            gadj[a * DG + k] = NA + adjA[a * DG + k];
    for (int b = 0; b < NB; b++)
        for (int k = 0; k < DG; k++)
            gadj[(NA + b) * DG + k] = adjB[b * DG + k];
    memset(RA, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++)
        RA[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    uint64_t *cur = RA, *nxt = RB;
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < DG; k++) {
                const uint64_t *s2 = cur + (size_t)gadj[v * DG + k] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long total = 0;
    for (int v = 0; v < n; v++) {
        int pc = 0;
        const uint64_t *src = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) pc += __builtin_popcountll(src[w]);
        total += n - pc;
    }
    return total;
}

static void save_best(void) {
    memcpy(beu, eu, sizeof(int) * (size_t)M);
    memcpy(bev, ev, sizeof(int) * (size_t)M);
}

static void restore_best(void) {
    memcpy(eu, beu, sizeof(int) * (size_t)M);
    memcpy(ev, bev, sizeof(int) * (size_t)M);
    rebuild();
}

static void save_valid(void) {
    memcpy(veu, eu, sizeof(int) * (size_t)M);
    memcpy(vev, ev, sizeof(int) * (size_t)M);
    vNA = NA;
    vM = M;
    have_valid = 1;
}

/* Circulant d-regular bipartite graph on 2*na vertices, then random 2-switches. */
static int random_start(int target) {
    int n = target - (target % 2);
    int na = n / 2;
    if (na < DG + 1 || na > MAXA) return 0;
    NA = na; NB = na; M = na * DG;
    for (int l = 0; l < DG; l++)
        for (int i = 0; i < na; i++) {
            int e = l * na + i;
            eu[e] = i;
            ev[e] = (i + l) % na;
        }
    if (!rebuild()) return 0;
    long long want = 40LL * M, done = 0, tries = 0, maxtries = 400LL * M;
    while (done < want && tries < maxtries) {
        tries++;
        int i = rnd_int(M), j = rnd_int(M);
        if (i == j) continue;
        int a1 = eu[i], b1 = ev[i], a2 = eu[j], b2 = ev[j];
        if (a1 == a2 || b1 == b2) continue;
        if (has_edge(a1, b2) || has_edge(a2, b1)) continue;
        do_switch(i, j);
        done++;
    }
    return 1;
}

/* Insert a new vertex pair (a', b'). Remove a random matching of DG edges (x_k, y_k),
   then add (x_k, b') and (a', y_k). Degrees stay DG everywhere. */
static int grow(void) {
    if (NA + 1 > MAXA) return 0;
    memset(usedA, 0, sizeof(int) * (size_t)NA);
    memset(usedB, 0, sizeof(int) * (size_t)NB);
    int chosen[MAXD], cnt = 0;
    for (long long tr = 0; tr < 2000000 && cnt < DG; tr++) {
        int e = rnd_int(M);
        int a = eu[e], b = ev[e];
        if (usedA[a] || usedB[b]) continue;
        usedA[a] = 1;
        usedB[b] = 1;
        chosen[cnt++] = e;
    }
    if (cnt < DG) return 0;
    int ys[MAXD];
    for (int k = 0; k < DG; k++) ys[k] = ev[chosen[k]];
    int newA = NA, newB = NB;
    for (int k = 0; k < DG; k++) {
        ev[chosen[k]] = newB;
        eu[M + k] = newA;
        ev[M + k] = ys[k];
    }
    NA++;
    NB++;
    M += DG;
    return rebuild();
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [target_n]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int target = argc > 5 ? atoi(argv[5]) : 0;
    if (DG < 1 || DG > MAXD || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 999ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int n_in = 0, m_in = 0;
    if (scanf("%d %d", &n_in, &m_in) != 2) { n_in = 0; m_in = 0; }
    int have_in = 0;
    if (n_in > 0 && m_in > 0 && n_in % 2 == 0 && n_in / 2 <= MAXA && m_in <= MAXE) {
        int half = n_in / 2, ok = 1;
        for (int e = 0; e < m_in; e++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
            if (u < half && v >= half && v < n_in) { eu[e] = u; ev[e] = v - half; }
            else if (v < half && u >= half && u < n_in) { eu[e] = v; ev[e] = u - half; }
            else { ok = 0; break; }
        }
        if (ok) {
            NA = half;
            NB = half;
            M = m_in;
            have_in = rebuild();
        }
    }
    if (!have_in) {
        if (!random_start(target)) {
            printf("0 0\n");
            return 0;
        }
    }

    long long cur = eval_cost();
    long long bestc = cur;
    save_best();

    while (elapsed() < DEADLINE) {
        if (cur == 0) {
            save_valid();
            if (!grow()) break;
            cur = eval_cost();
            bestc = cur;
            save_best();
            continue;
        }
        for (int it = 0; it < CYC && cur > 0; it++) {
            if ((it & 127) == 0 && elapsed() > DEADLINE) break;
            int i = rnd_int(M), j = rnd_int(M);
            if (i == j) continue;
            int a1 = eu[i], b1 = ev[i], a2 = eu[j], b2 = ev[j];
            if (a1 == a2 || b1 == b2) continue;
            if (has_edge(a1, b2) || has_edge(a2, b1)) continue;
            double T = TSTART * pow(TEND / TSTART, (double)it / CYC);
            do_switch(i, j);
            long long nc = eval_cost();
            long long delta = nc - cur;
            if (delta <= 0 || rnd_unit() < exp(-(double)delta / T)) {
                cur = nc;
                if (cur < bestc) {
                    bestc = cur;
                    save_best();
                }
            } else {
                do_switch(i, j);
            }
        }
        restore_best();
        cur = bestc;
    }
    if (cur == 0) save_valid();

    if (!have_valid) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", 2 * vNA, vM);
    for (int e = 0; e < vM; e++)
        printf("%d %d\n", veu[e], vNA + vev[e]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe algebraic baselines.
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


def _regular_balanced(n, edges, d):
    """True if the graph is d-regular with sides {0..n/2-1} and {n/2..n-1}, every edge crossing."""
    if n < 2 or n % 2:
        return False
    half = n // 2
    deg = [0] * n
    for u, v in edges:
        if not (u < half <= v < n or v < half <= u < n):
            return False
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


# ----------------------------------------------------------------------------
# Driver.
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

    if D == 4 and time.monotonic() - start < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best_n >= lib.moore_bound(d, D):
        return best

    usable = 0.92 * time_limit - (time.monotonic() - start) - 3.0
    if usable < 3.0:
        return best

    # Stage 1: the structured voltage-lift annealer (half the budget).
    s1 = 0.5 * usable
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{s1:.2f}", best_n],
                        timeout=s1 + 8.0)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except Exception:
        pass

    # Stage 2: unstructured 2-switch annealing with a growing ladder. It starts
    # from the stage-1 graph when that graph is regular and balanced.
    remaining = 0.92 * time_limit - (time.monotonic() - start) - 2.0
    if remaining >= 2.0:
        start_graph = best if _regular_balanced(best[0], best[1], d) else None
        tgt = best_n + 2
        if tgt % 2:
            tgt += 1
        try:
            out = lib.run_c(C_SOURCE2, [d, D, seed + 1, f"{remaining:.2f}", tgt],
                            stdin_graph=start_graph, timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
