import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 (structured): voltage lifts of semidirect products Z_m x| Z_k2 over a
# base of K A-vertices and K B-vertices, searched by simulated annealing with
# breakout weights and an elite pool (ILS). Unchanged from the parent engine.
#
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart t = (i, j, s) joins
# A_i,g to B_j,g*s for all g. Each layer is a permutation, so every vertex
# has degree DEG.
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
# Stage 2 (unstructured, new): start from a valid d-regular bipartite graph and
# grow it by pairs. Each growth step splices a new A-vertex and a new B-vertex
# into d random edges (remove (a,b), add (a,b_new) and (a_new,b)), which keeps
# every degree exact. Then a degree-preserving double-edge-swap annealer
# minimises the number of vertex pairs at distance > D. Distances are computed
# with bitset ball expansion, about 0.1 ms per evaluation at n ~ 700.
# When the cost reaches 0, the graph is saved and another pair is added.
# Output is the largest valid graph found.
# ----------------------------------------------------------------------------

C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXH 1500
#define CYCLE 6.0

static struct timespec T0;
static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static uint64_t rs[2];
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

static int DEG, DIAM, H;
/* adjA[a*DEG+k] = B index b; adjB[b*DEG+k] = A index a. Dense ids: A a -> a, B b -> H+b. */
static int *adjA, *adjB, *bestA, *bestB, bestH;
static int have_best = 0;
static uint64_t *R0, *R1;

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has(const int *list, int len, int x) {
    for (int i = 0; i < len; i++) if (list[i] == x) return 1;
    return 0;
}

static int find_idx(const int *list, int len, int x) {
    for (int i = 0; i < len; i++) if (list[i] == x) return i;
    return -1;
}

/* Number of unordered vertex pairs at distance > DIAM. */
static long long cost_eval(void) {
    int n = 2 * H;
    int W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        uint64_t *r = R0 + (size_t)v * W;
        memset(r, 0, sizeof(uint64_t) * (size_t)W);
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = R1 + (size_t)v * W;
            memcpy(dst, R0 + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < DEG; k++) {
                int u = (v < H) ? H + adjA[(size_t)v * DEG + k] : adjB[(size_t)(v - H) * DEG + k];
                const uint64_t *s = R0 + (size_t)u * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = R0; R0 = R1; R1 = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *r = R0 + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(r[w]);
        bad += n - c;
    }
    return bad / 2;
}

typedef struct { int a1, k1, a2, k2, b1, b2, i1, i2; } Sw;

/* Propose a double-edge swap (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). */
static int propose(Sw *s) {
    s->a1 = rnd_int(H);
    s->a2 = rnd_int(H);
    s->k1 = rnd_int(DEG);
    s->k2 = rnd_int(DEG);
    if (s->a1 == s->a2) return 0;
    s->b1 = adjA[(size_t)s->a1 * DEG + s->k1];
    s->b2 = adjA[(size_t)s->a2 * DEG + s->k2];
    if (s->b1 == s->b2) return 0;
    if (has(adjA + (size_t)s->a1 * DEG, DEG, s->b2)) return 0;
    if (has(adjA + (size_t)s->a2 * DEG, DEG, s->b1)) return 0;
    s->i1 = find_idx(adjB + (size_t)s->b1 * DEG, DEG, s->a1);
    s->i2 = find_idx(adjB + (size_t)s->b2 * DEG, DEG, s->a2);
    return s->i1 >= 0 && s->i2 >= 0;
}

static void apply_sw(const Sw *s, int rev) {
    if (!rev) {
        adjA[(size_t)s->a1 * DEG + s->k1] = s->b2;
        adjA[(size_t)s->a2 * DEG + s->k2] = s->b1;
        adjB[(size_t)s->b1 * DEG + s->i1] = s->a2;
        adjB[(size_t)s->b2 * DEG + s->i2] = s->a1;
    } else {
        adjA[(size_t)s->a1 * DEG + s->k1] = s->b1;
        adjA[(size_t)s->a2 * DEG + s->k2] = s->b2;
        adjB[(size_t)s->b1 * DEG + s->i1] = s->a1;
        adjB[(size_t)s->b2 * DEG + s->i2] = s->a2;
    }
}

/* Add one A-vertex and one B-vertex (both index Ho) by splicing DEG edges. */
static int grow_one(void) {
    if (H + 1 > MAXH) return 0;
    int Ho = H, an = Ho, bn = Ho;
    int dA = 0, dB = 0;
    for (int round = 0; round < DEG; round++) {
        int tries = 0;
        for (;;) {
            if (++tries > 200000) return 0;
            int a = rnd_int(Ho), k = rnd_int(DEG);
            int b = adjA[(size_t)a * DEG + k];
            if (has(adjA + (size_t)an * DEG, dA, b)) continue;
            if (has(adjB + (size_t)bn * DEG, dB, a)) continue;
            /* remove (a,b); add (a,bn) and (an,b). Degrees of a and b are unchanged. */
            adjA[(size_t)a * DEG + k] = bn;
            int ib = find_idx(adjB + (size_t)b * DEG, DEG, a);
            if (ib < 0) return 0;
            adjB[(size_t)b * DEG + ib] = an;
            adjA[(size_t)an * DEG + dA++] = b;
            adjB[(size_t)bn * DEG + dB++] = a;
            break;
        }
    }
    H = Ho + 1;
    return 1;
}

static void save_best(void) {
    memcpy(bestA, adjA, sizeof(int) * (size_t)H * DEG);
    memcpy(bestB, adjB, sizeof(int) * (size_t)H * DEG);
    bestH = H;
    have_best = 1;
}

/* Read "n m" and edges. Accept only a DEG-regular bipartite graph with equal sides. */
static int load_graph(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 2 || n % 2 || n / 2 >= MAXH || m != n / 2 * DEG) return 0;
    int *eu = malloc(sizeof(int) * (size_t)m), *ev = malloc(sizeof(int) * (size_t)m);
    int *deg = calloc((size_t)n, sizeof(int)), *col = malloc(sizeof(int) * (size_t)n);
    int *idx = malloc(sizeof(int) * (size_t)n);
    int ok = 1;
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { ok = 0; break; }
        if (eu[i] < 0 || eu[i] >= n || ev[i] < 0 || ev[i] >= n || eu[i] == ev[i]) { ok = 0; break; }
        deg[eu[i]]++;
        deg[ev[i]]++;
    }
    for (int v = 0; ok && v < n; v++) if (deg[v] != DEG) ok = 0;
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; ok && s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int changed = 1;
        while (changed) {
            changed = 0;
            for (int i = 0; i < m; i++) {
                int u = eu[i], v = ev[i];
                if (col[u] >= 0 && col[v] < 0) { col[v] = 1 - col[u]; changed = 1; }
                else if (col[v] >= 0 && col[u] < 0) { col[u] = 1 - col[v]; changed = 1; }
            }
        }
    }
    for (int i = 0; ok && i < m; i++) if (col[eu[i]] == col[ev[i]]) ok = 0;
    int cA = 0, cB = 0;
    for (int v = 0; ok && v < n; v++) {
        if (col[v] == 0) idx[v] = cA++;
        else idx[v] = cB++;
    }
    if (ok && (cA != cB || cA != n / 2)) ok = 0;
    if (ok) {
        H = cA;
        int *fa = calloc((size_t)H, sizeof(int)), *fb = calloc((size_t)H, sizeof(int));
        for (int i = 0; i < m && ok; i++) {
            int x = (col[eu[i]] == 0) ? eu[i] : ev[i];
            int y = (col[eu[i]] == 0) ? ev[i] : eu[i];
            int a = idx[x], b = idx[y];
            if (fa[a] >= DEG || fb[b] >= DEG) { ok = 0; break; }
            adjA[(size_t)a * DEG + fa[a]++] = b;
            adjB[(size_t)b * DEG + fb[b]++] = a;
        }
        for (int a = 0; ok && a < H; a++)
            for (int i = 0; ok && i < DEG; i++)
                for (int j = i + 1; j < DEG; j++)
                    if (adjA[(size_t)a * DEG + i] == adjA[(size_t)a * DEG + j]) { ok = 0; break; }
        free(fa);
        free(fb);
    }
    free(eu); free(ev); free(deg); free(col); free(idx);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit   (graph on stdin)\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    double deadline = atof(argv[4]);
    if (DEG < 2 || DIAM < 1) { printf("0 0\n"); return 0; }
    rs[0] = sd * 2654435761ULL + 12345ULL;
    rs[1] = rs[0] * 6364136223846793005ULL + 1442695040888963407ULL;
    if (!rs[0]) rs[0] = 1;
    if (!rs[1]) rs[1] = 2;

    adjA = malloc(sizeof(int) * (size_t)MAXH * DEG);
    adjB = malloc(sizeof(int) * (size_t)MAXH * DEG);
    bestA = malloc(sizeof(int) * (size_t)MAXH * DEG);
    bestB = malloc(sizeof(int) * (size_t)MAXH * DEG);
    size_t Wmax = (2 * MAXH + 63) / 64;
    R0 = malloc(sizeof(uint64_t) * 2 * MAXH * Wmax);
    R1 = malloc(sizeof(uint64_t) * 2 * MAXH * Wmax);

    if (!load_graph()) { printf("0 0\n"); return 0; }

    long long cost = cost_eval();
    const double T_BASE = 0.15, T_HOT = 1.2;

    while (elapsed() < deadline) {
        if (cost == 0) {
            save_best();
            if (!grow_one()) break;
            cost = cost_eval();
            continue;
        }
        for (int it = 0; it < 64 && cost > 0; it++) {
            double fr = fmod(elapsed(), CYCLE) / CYCLE;
            double temp = T_BASE + T_HOT * (1.0 - fr);
            Sw s;
            if (!propose(&s)) continue;
            apply_sw(&s, 0);
            long long c2 = cost_eval();
            if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                apply_sw(&s, 1);
            }
        }
    }
    if (cost == 0) save_best();

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    int n = 2 * bestH, m = bestH * DEG;
    printf("%d %d\n", n, m);
    for (int a = 0; a < bestH; a++)
        for (int k = 0; k < DEG; k++)
            printf("%d %d\n", a, bestH + bestA[a * DEG + k]);
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


# ----------------------------------------------------------------------------
# Driver: baselines, then the structured lift stage, then the unstructured
# growth stage started from the best graph so far.
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

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    def left():
        return 0.92 * time_limit - (time.monotonic() - start) - 1.5

    # Stage 1: structured voltage lifts. Give it about half of the remaining budget.
    remaining = left()
    if remaining >= 2.0:
        lift_budget = 0.5 * remaining
        try:
            out = lib.run_c(C_LIFT, [d, D, seed, f"{lift_budget:.2f}", best_n],
                            timeout=lift_budget + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Stage 2: grow the best graph by pairs, with degree-preserving annealing.
    # Only useful when the current graph is a regular bipartite graph with equal sides.
    grow_budget = left()
    if grow_budget >= 2.0 and best_n < lib.moore_bound(d, D):
        try:
            out = lib.run_c(C_GROW, [d, D, seed, f"{grow_budget:.2f}"],
                            stdin_graph=best, timeout=grow_budget + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
