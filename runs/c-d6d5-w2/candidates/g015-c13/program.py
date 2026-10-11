import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine, two phases in one run.
#
# Phase 1 (LIFT_FRAC of the budget): voltage lifts of semidirect products
# Z_m x| Z_k2 over a base of K A-vertices and K B-vertices, searched by
# simulated annealing with breakout weights and an elite pool (ILS). This is
# the same search as the parent program.
#
# Phase 2 (remaining budget, new): take the best lift as a start graph and
# grow it WITHOUT symmetry. Each growth step adds one A vertex x and one B
# vertex y. It picks DEG edges (a_i, b_i) with distinct endpoints, replaces
# each by x-b_i, and adds a_i-y. Every vertex keeps degree <= DEG, the graph
# stays bipartite, and the vertex count rises by 2. Then a plain annealer
# repairs the diameter. Moves are degree-preserving double-edge swaps. The
# cost is the number of ordered vertex pairs at distance > DIAM, computed
# with bit-parallel ball expansion. If repair keeps failing, the search
# returns to the last valid graph and perturbs it.
#
# Vertices of the lift: A_i,g = i*G + g and B_j,h = (K+j)*G + h, so the
# first half of the vertex ids are A and the second half are B.
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
#define LIFT_FRAC 0.4
#define GMAXN 4096
#define GSTEP 6000
#define FAILMAX 4
#define GPERT 30

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

/* ------------------------- Grow phase ------------------------- */

static int *ge = NULL, *gbe = NULL, *abe = NULL, *gmark = NULL;
static int gn = 0, gm = 0, ecap = 0, gbn = 0, gbm = 0, markv = 0;
static int *gadj = NULL, *gdeg = NULL;
static uint64_t *gA = NULL, *gB = NULL;

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void grow_alloc(void) {
    int E2 = 2 * GMAXN * DEG;
    ecap = GMAXN * DEG;
    ge = malloc(sizeof(int) * (size_t)E2);
    gbe = malloc(sizeof(int) * (size_t)E2);
    abe = malloc(sizeof(int) * (size_t)E2);
    gadj = malloc(sizeof(int) * (size_t)GMAXN * DEG);
    gdeg = calloc(GMAXN, sizeof(int));
    gA = calloc((size_t)GMAXN * 64, sizeof(uint64_t));
    gB = calloc((size_t)GMAXN * 64, sizeof(uint64_t));
    gmark = calloc(GMAXN, sizeof(int));
}

static int has_edge(int a, int b) {
    for (int i = 0; i < gm; i++)
        if (ge[2 * i] == a && ge[2 * i + 1] == b) return 1;
    return 0;
}

static void build_adj(void) {
    for (int v = 0; v < gn; v++) gdeg[v] = 0;
    for (int i = 0; i < gm; i++) {
        int a = ge[2 * i], b = ge[2 * i + 1];
        gadj[(size_t)a * DEG + gdeg[a]++] = b;
        gadj[(size_t)b * DEG + gdeg[b]++] = a;
    }
}

/* Number of ordered pairs (u,v) with dist > DIAM (0 means valid). */
static long long gcost(void) {
    int n = gn, W = (n + 63) >> 6;
    build_adj();
    uint64_t *A = gA, *B = gB;
    memset(A, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) A[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int lv = 0; lv < DIAM; lv++) {
        for (int v = 0; v < n; v++) {
            uint64_t *bv = B + (size_t)v * W;
            const uint64_t *av = A + (size_t)v * W;
            for (int k = 0; k < W; k++) bv[k] = av[k];
            for (int e = 0; e < gdeg[v]; e++) {
                const uint64_t *au = A + (size_t)gadj[(size_t)v * DEG + e] * W;
                for (int k = 0; k < W; k++) bv[k] |= au[k];
            }
        }
        uint64_t *tmp = A; A = B; B = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *av = A + (size_t)v * W;
        for (int k = 0; k < W; k++) c += popc64(av[k]);
        bad += n - c;
    }
    return bad;
}

/* Degree-preserving double-edge swaps, applied without cost check. */
static void gperturb(int P) {
    for (int s = 0; s < P; s++) {
        int i = rnd_int(gm), j = rnd_int(gm);
        if (i == j) continue;
        int a1 = ge[2 * i], b1 = ge[2 * i + 1], a2 = ge[2 * j], b2 = ge[2 * j + 1];
        if (a1 == a2 || b1 == b2) continue;
        if (has_edge(a1, b2) || has_edge(a2, b1)) continue;
        ge[2 * i + 1] = b2;
        ge[2 * j + 1] = b1;
    }
}

/* Anneal on the number of bad pairs. Leaves ge in the best state found; returns its cost. */
static long long anneal(long long steps, double T0v, double T1v, long long curc) {
    long long bestc = curc;
    memcpy(abe, ge, sizeof(int) * 2 * (size_t)gm);
    for (long long it = 0; it < steps && bestc > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        double Tm = T0v * pow(T1v / T0v, (double)it / (double)steps);
        int i = rnd_int(gm), j = rnd_int(gm);
        if (i == j) continue;
        int a1 = ge[2 * i], b1 = ge[2 * i + 1], a2 = ge[2 * j], b2 = ge[2 * j + 1];
        if (a1 == a2 || b1 == b2) continue;
        if (has_edge(a1, b2) || has_edge(a2, b1)) continue;
        ge[2 * i + 1] = b2;
        ge[2 * j + 1] = b1;
        long long nc = gcost();
        long long dl = nc - curc;
        if (dl <= 0 || rnd_unit() < exp(-(double)dl / Tm)) {
            curc = nc;
            if (curc < bestc) {
                bestc = curc;
                memcpy(abe, ge, sizeof(int) * 2 * (size_t)gm);
            }
        } else {
            ge[2 * i + 1] = b1;
            ge[2 * j + 1] = b2;
        }
    }
    memcpy(ge, abe, sizeof(int) * 2 * (size_t)gm);
    return bestc;
}

/* Add one A vertex x = gn and one B vertex y = gn+1, each of degree DEG.
   Picks DEG edges (a_i, b_i) with distinct endpoints, replaces each by (x, b_i),
   and appends (a_i, y). Returns 0 and leaves the graph unchanged on failure. */
static int grow_pair(void) {
    int x = gn, y = gn + 1;
    int sel[64];
    int chosen = 0;
    markv++;
    for (int tries = 0; tries < 20000 && chosen < DEG; tries++) {
        int i = rnd_int(gm);
        int a = ge[2 * i], b = ge[2 * i + 1];
        if (gmark[a] == markv || gmark[b] == markv) continue;
        gmark[a] = markv;
        gmark[b] = markv;
        sel[chosen++] = i;
    }
    if (chosen < DEG) return 0;
    gn += 2;
    for (int k = 0; k < DEG; k++) {
        int i = sel[k];
        int a = ge[2 * i], b = ge[2 * i + 1];
        ge[2 * i] = x;
        ge[2 * i + 1] = b;
        ge[2 * gm] = a;
        ge[2 * gm + 1] = y;
        gm++;
    }
    return 1;
}

/* Load best_e into the grow state, then grow and repair until endt.
   Returns 1 if the start graph was valid (gbe then holds the best valid graph). */
static int grow_run(double endt) {
    gn = best_n;
    gm = best_m;
    if (gn > GMAXN - 2 || (gn & 1)) return 0;
    int h = gn / 2;
    for (int v = 0; v < gn; v++) gdeg[v] = 0;
    for (int i = 0; i < gm; i++) {
        int a = best_e[2 * i], b = best_e[2 * i + 1];
        if (a < 0 || b < 0 || a >= gn || b >= gn) return 0;
        if (a < h && b >= h) {
            /* already oriented: A first */
        } else if (a >= h && b < h) {
            int t = a; a = b; b = t;
        } else {
            return 0;
        }
        ge[2 * i] = a;
        ge[2 * i + 1] = b;
        if (++gdeg[a] > DEG || ++gdeg[b] > DEG) return 0;
    }
    gbn = gn;
    gbm = gm;
    memcpy(gbe, ge, sizeof(int) * 2 * (size_t)gm);
    if (gcost() != 0) return 0;

    int fails = 0;
    while (elapsed() < endt) {
        long long c = gcost();
        if (c == 0) {
            gbn = gn;
            gbm = gm;
            memcpy(gbe, ge, sizeof(int) * 2 * (size_t)gm);
            if (gn + 2 > GMAXN || gm + DEG > ecap) break;
            if (!grow_pair()) gperturb(GPERT);
            fails = 0;
            continue;
        }
        long long rc = anneal(GSTEP, 1.2, 0.05, c);
        if (rc == 0) continue;
        if (++fails >= FAILMAX) {
            gn = gbn;
            gm = gbm;
            memcpy(ge, gbe, sizeof(int) * 2 * (size_t)gm);
            gperturb(GPERT);
            fails = 0;
        }
    }
    /* A valid state may have been reached by the last anneal. */
    if (gcost() == 0 && gn > gbn) {
        gbn = gn;
        gbm = gm;
        memcpy(gbe, ge, sizeof(int) * 2 * (size_t)gm);
    }
    return 1;
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
    double total = atof(argv[4]);
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

    /* Phase 1: lift search. */
    DEADLINE = LIFT_FRAC * total;
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

    /* Phase 2: non-symmetric growth from the best lift. */
    DEADLINE = total;
    int grown = 0;
    if (best_m > 0 && DEG <= 64) {
        grow_alloc();
        grown = grow_run(total);
    }

    if (grown) {
        printf("%d %d\n", gbn, gbm);
        for (int i = 0; i < gbm; i++)
            printf("%d %d\n", gbe[2 * i], gbe[2 * i + 1]);
    } else if (best_m > 0) {
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
# Driver: baselines in Python, then the C engine (lift search, then growth).
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

    # The C run gets nearly all of the budget. The reserve covers the one-off
    # compile (outside the C deadline), parsing and validation.
    remaining = 0.90 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 6.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
