import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Engine 1 (lift search, unchanged from the parent): voltage lifts of
# semidirect products Z_m x| Z_k2 over a base of K A-vertices and K B-vertices,
# annealed with breakout weights and an elite pool (ILS).
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
# Engine 2 (new, bold): grow-and-repair. Starts from a VALID bipartite graph,
# adds a pair of vertices (one per side) by rewiring d existing edges, then
# repairs the diameter with simulated annealing over degree-preserving double
# edge swaps (cost = number of ordered pairs farther than D apart). A repair
# that reaches zero cost gives a larger valid graph, which becomes the new
# base. Failed attempts are discarded and retried with new random choices.
# ----------------------------------------------------------------------------

C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC (1LL << 50)

static struct timespec T0;
static double DEADLINE;
static int DEG, DIAM, NMAX, WS, CAPM;
static int M, N;
static int *ea, *eb, *bsa, *bsb;
static int *va, *vb;
static int vM, vN;
static int *adjv, *adjc;
static uint64_t *rc, *rn;
static int *usedA, *usedB, gen = 0;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static uint64_t xr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int n) { return (int)(xr() % (uint64_t)n); }
static double rndu(void) { return (double)(xr() >> 11) * (1.0 / 9007199254740992.0); }

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < M; k++)
        if (ea[k] == a && eb[k] == b) return 1;
    return 0;
}

/* Sum over vertices of the number of vertices NOT within distance DIAM. */
static long long eval_cost(int n) {
    int Wn = (n + 63) / 64;
    if (M < 1) return BIGC;
    for (int v = 0; v < n; v++) adjc[v] = 0;
    for (int i = 0; i < M; i++) {
        int a = ea[i], b = eb[i];
        if (adjc[a] >= DEG || adjc[b] >= DEG) return BIGC;
        adjv[a * DEG + adjc[a]++] = b;
        adjv[b * DEG + adjc[b]++] = a;
    }
    memset(rc, 0, sizeof(uint64_t) * (size_t)n * (size_t)Wn);
    for (int v = 0; v < n; v++) rc[(size_t)v * Wn + (v >> 6)] |= 1ULL << (v & 63);
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = rn + (size_t)v * Wn;
            const uint64_t *src = rc + (size_t)v * Wn;
            for (int w = 0; w < Wn; w++) dst[w] = src[w];
            for (int k = 0; k < adjc[v]; k++) {
                const uint64_t *nb = rc + (size_t)adjv[v * DEG + k] * Wn;
                for (int w = 0; w < Wn; w++) dst[w] |= nb[w];
            }
        }
        uint64_t *t = rc; rc = rn; rn = t;
    }
    long long cost = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *r = rc + (size_t)v * Wn;
        for (int w = 0; w < Wn; w++) c += popc64(r[w]);
        cost += n - c;
    }
    return cost;
}

/* Degree-preserving double edge swaps with annealing. Returns the best cost;
   on zero the state is the valid graph, otherwise the state is arbitrary. */
static long long repair(int n, long long steps) {
    if (M < 2) return BIGC;
    long long cur = eval_cost(n);
    if (cur == 0) return 0;
    double T0t = 0.05 * (double)cur + 1.0;
    double Tend = 0.2;
    long long bestc = cur;
    memcpy(bsa, ea, sizeof(int) * (size_t)M);
    memcpy(bsb, eb, sizeof(int) * (size_t)M);
    for (long long it = 0; it < steps; it++) {
        if ((it & 31) == 0 && now() > DEADLINE) break;
        double Tm = T0t * pow(Tend / T0t, (double)it / (double)steps);
        int i = rndi(M), j = rndi(M);
        if (i == j) continue;
        int a1 = ea[i], b1 = eb[i], a2 = ea[j], b2 = eb[j];
        if (a1 == a2 || b1 == b2) continue;
        if (has_edge(a1, b2) || has_edge(a2, b1)) continue;
        eb[i] = b2;
        eb[j] = b1;
        long long c2 = eval_cost(n);
        if (c2 <= cur || rndu() < exp(-(double)(c2 - cur) / Tm)) {
            cur = c2;
            if (cur < bestc) {
                bestc = cur;
                memcpy(bsa, ea, sizeof(int) * (size_t)M);
                memcpy(bsb, eb, sizeof(int) * (size_t)M);
                if (bestc == 0) break;
            }
        } else {
            eb[i] = b1;
            eb[j] = b2;
        }
    }
    if (bestc == 0) {
        memcpy(ea, bsa, sizeof(int) * (size_t)M);
        memcpy(eb, bsb, sizeof(int) * (size_t)M);
    }
    return bestc;
}

/* Add vertices a = n (side 0) and b = n+1 (side 1). Pick DEG edges (x_k, y_k)
   with distinct x and distinct y; replace each by (a, y_k) and add (x_k, b).
   Returns the new vertex count, -1 for a retryable failure, -2 for capacity. */
static int grow_pair(int n) {
    if (DEG > 64) return -2;
    if (n + 2 > NMAX) return -2;
    if (M + DEG > CAPM) return -2;
    if (M < DEG) return -2;
    int a = n, b = n + 1;
    int chosen[64];
    gen++;
    int cnt = 0, tries = 0;
    while (cnt < DEG && tries < 4000) {
        tries++;
        int e = rndi(M);
        int x = ea[e], y = eb[e];
        if (usedA[x] == gen || usedB[y] == gen) continue;
        usedA[x] = gen;
        usedB[y] = gen;
        chosen[cnt++] = e;
    }
    if (cnt < DEG) return -1;
    for (int k = 0; k < DEG; k++) {
        int e = chosen[k];
        int x = ea[e], y = eb[e];
        ea[e] = a;
        eb[e] = y;
        ea[M] = x;
        eb[M] = b;
        M++;
    }
    return n + 2;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    rs ^= (sd + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;

    int n_in = 0, m_in = 0;
    if (DEG < 2 || DIAM < 1 || scanf("%d %d", &n_in, &m_in) != 2 ||
        n_in <= 0 || m_in <= 0 || n_in > 100000 || m_in > 2000000) {
        printf("0 0\n");
        return 0;
    }
    int *iu = malloc(sizeof(int) * (size_t)m_in);
    int *iv = malloc(sizeof(int) * (size_t)m_in);
    for (int i = 0; i < m_in; i++) {
        if (scanf("%d %d", &iu[i], &iv[i]) != 2 || iu[i] < 0 || iv[i] < 0 ||
            iu[i] >= n_in || iv[i] >= n_in) {
            printf("0 0\n");
            return 0;
        }
    }
    int *deg0 = calloc((size_t)n_in, sizeof(int));
    for (int i = 0; i < m_in; i++) { deg0[iu[i]]++; deg0[iv[i]]++; }
    for (int v = 0; v < n_in; v++)
        if (deg0[v] > DEG) { printf("0 0\n"); return 0; }
    int *off = malloc(sizeof(int) * (size_t)(n_in + 1));
    off[0] = 0;
    for (int v = 0; v < n_in; v++) off[v + 1] = off[v] + deg0[v];
    int *lst = malloc(sizeof(int) * (size_t)(2 * m_in));
    int *fill = calloc((size_t)n_in, sizeof(int));
    for (int i = 0; i < m_in; i++) {
        int u = iu[i], v = iv[i];
        lst[off[u] + fill[u]++] = v;
        lst[off[v] + fill[v]++] = u;
    }
    int *col = malloc(sizeof(int) * (size_t)n_in);
    for (int v = 0; v < n_in; v++) col[v] = -1;
    int *qq = malloc(sizeof(int) * (size_t)n_in);
    int bip = 1;
    for (int s = 0; s < n_in; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        qq[qt++] = s;
        while (qh < qt) {
            int x = qq[qh++];
            for (int k = off[x]; k < off[x + 1]; k++) {
                int y = lst[k];
                if (col[y] == -1) {
                    col[y] = 1 - col[x];
                    qq[qt++] = y;
                } else if (col[y] == col[x]) {
                    bip = 0;
                }
            }
        }
    }
    if (!bip) { printf("0 0\n"); return 0; }

    double mb = 0.0, pw = 1.0;
    for (int i = 0; i < DIAM; i++) { mb += pw; pw *= (double)(DEG - 1); }
    mb *= 2.0;
    double capd = mb + 8.0;
    if (capd > 12000.0) capd = 12000.0;
    NMAX = (int)capd;
    if (NMAX < n_in + 4) NMAX = n_in + 4;
    WS = (NMAX + 63) / 64;
    CAPM = NMAX * DEG + 16;

    ea = malloc(sizeof(int) * (size_t)CAPM);
    eb = malloc(sizeof(int) * (size_t)CAPM);
    bsa = malloc(sizeof(int) * (size_t)CAPM);
    bsb = malloc(sizeof(int) * (size_t)CAPM);
    va = malloc(sizeof(int) * (size_t)CAPM);
    vb = malloc(sizeof(int) * (size_t)CAPM);
    adjv = malloc(sizeof(int) * (size_t)NMAX * DEG);
    adjc = malloc(sizeof(int) * (size_t)NMAX);
    rc = malloc(sizeof(uint64_t) * (size_t)NMAX * WS);
    rn = malloc(sizeof(uint64_t) * (size_t)NMAX * WS);
    usedA = calloc((size_t)NMAX, sizeof(int));
    usedB = calloc((size_t)NMAX, sizeof(int));

    for (int i = 0; i < m_in; i++) {
        if (col[iu[i]] == 0) { ea[i] = iu[i]; eb[i] = iv[i]; }
        else                 { ea[i] = iv[i]; eb[i] = iu[i]; }
    }
    M = m_in;
    N = n_in;

    long long c0 = eval_cost(N);
    if (c0 != 0) c0 = repair(N, 30000);
    if (c0 != 0) {
        printf("0 0\n");
        return 0;
    }
    memcpy(va, ea, sizeof(int) * (size_t)M);
    memcpy(vb, eb, sizeof(int) * (size_t)M);
    vM = M;
    vN = N;

    long long steps = 3000;
    while (now() < DEADLINE) {
        memcpy(ea, va, sizeof(int) * (size_t)vM);
        memcpy(eb, vb, sizeof(int) * (size_t)vM);
        M = vM;
        N = vN;
        int nn = grow_pair(N);
        if (nn == -2) break;
        if (nn < 0) continue;
        N = nn;
        long long c = repair(N, steps);
        if (c == 0) {
            memcpy(va, ea, sizeof(int) * (size_t)M);
            memcpy(vb, eb, sizeof(int) * (size_t)M);
            vM = M;
            vN = N;
        } else if (steps < 200000) {
            steps += steps / 4;
        }
    }

    printf("%d %d\n", vN, vM);
    for (int i = 0; i < vM; i++) printf("%d %d\n", va[i], vb[i]);
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
# Driver: baselines, then lift search (phase 1), then grow-and-repair from the
# best graph found so far (phase 2). Every stage only replaces the best graph
# with a strictly larger one that passes lib.is_valid.
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

    if D >= 4 and time.monotonic() - start < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best_n >= lib.moore_bound(d, D):
        return best

    def budget_left():
        return 0.9 * time_limit - (time.monotonic() - start) - 2.0

    remaining = budget_left()
    if remaining < 2.0 or d < 2:
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    # Phase 1: the lift search from the parent, which can reach the record.
    t1 = 0.45 * remaining
    try:
        out = lib.run_c(C_LIFT, [d, D, seed, f"{t1:.2f}", best_n],
                        timeout=t1 + 8.0)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except Exception:
        pass

    # Phase 2: grow the current best graph by vertex pairs, repairing the
    # diameter by annealing edge swaps. Starts from a valid graph, so a
    # failed or truncated run leaves the best graph unchanged.
    t2 = budget_left()
    if t2 >= 1.0:
        try:
            out = lib.run_c(C_GROW, [d, D, seed + 1, f"{t2:.2f}"],
                            stdin_graph=best, timeout=t2 + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
