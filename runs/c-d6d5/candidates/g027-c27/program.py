import time

import lib


# ----------------------------------------------------------------------------
# Stage A engine (unchanged parent search): voltage lifts of semidirect products
# Z_m x| Z_k2 over a base of K A-vertices and K B-vertices, found by annealing
# with breakout weights and an elite-pool iterated local search.
# ----------------------------------------------------------------------------

PARENT_SOURCE = r"""
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
# Stage B engine (new, unstructured): start from a d-regular bipartite graph,
# split it into d perfect matchings (layers), and anneal over arbitrary layer
# permutations on the full graph. Whenever a zero-cost graph is found, grow it
# by one vertex pair (subdivision of one edge per layer keeps d-regularity)
# and continue annealing from there. Cost = ordered pairs at distance > D
# plus a penalty for repeated edges, evaluated with bitset BFS.
# ----------------------------------------------------------------------------

GROW_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define DUPW 3
#define STEPS 20000
#define TH 6.0
#define TL 0.2
#define CAPEXTRA 2000

static struct timespec T0;
static double DEADLINE;
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

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int DG, DIAM, N, CAP, WCAP;
static int *sig, *bsig, *vsig, *nb;
static uint64_t *cur, *nxt;
static int valid_N = 0;
static int *Ea_start, *Ea_list, *EB, *used, *mA, *mB, *vis;
static int visstamp = 0;

/* sig[l*CAP + a] = B index matched to A vertex a in layer l. */

static long long eval_cost(void) {
    const int d = DG, n2 = 2 * N;
    for (int a = 0; a < N; a++)
        for (int l = 0; l < d; l++) {
            int b = sig[(size_t)l * CAP + a];
            nb[(size_t)a * d + l] = N + b;
            nb[(size_t)(N + b) * d + l] = a;
        }
    long long dup = 0;
    for (int v = 0; v < n2; v++) {
        const int *x = nb + (size_t)v * d;
        for (int l = 0; l < d; l++)
            for (int k = l + 1; k < d; k++)
                if (x[l] == x[k]) dup++;
    }
    const int W = (n2 + 63) / 64;
    for (int v = 0; v < n2; v++) {
        uint64_t *c = cur + (size_t)v * W;
        memset(c, 0, sizeof(uint64_t) * (size_t)W);
        c[v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < n2; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            for (int l = 0; l < d; l++) {
                const uint64_t *c2 = cur + (size_t)nb[(size_t)v * d + l] * W;
                for (int w = 0; w < W; w++) o[w] |= c2[w];
            }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long unc = 0;
    for (int v = 0; v < n2; v++) {
        const uint64_t *c = cur + (size_t)v * W;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += __builtin_popcountll(c[w]);
        unc += n2 - pc;
    }
    return unc + DUPW * dup;
}

static void copy_sig(int *dst, const int *src, int n) {
    for (int l = 0; l < DG; l++)
        memcpy(dst + (size_t)l * CAP, src + (size_t)l * CAP, sizeof(int) * (size_t)n);
}

static void save_best(void) { copy_sig(bsig, sig, N); }
static void restore_best(void) { copy_sig(sig, bsig, N); }

static long long run_stage(void) {
    long long c = eval_cost();
    long long bestc = c;
    save_best();
    if (c == 0) return 0;
    for (int it = 0; it < STEPS; it++) {
        if ((it & 127) == 0 && elapsed() > DEADLINE) break;
        double T = TH * pow(TL / TH, (double)it / STEPS);
        int l = rnd_int(DG);
        int a1 = rnd_int(N), a2 = rnd_int(N);
        if (a1 == a2) continue;
        int *p = sig + (size_t)l * CAP;
        int tmp = p[a1]; p[a1] = p[a2]; p[a2] = tmp;
        long long nc = eval_cost();
        long long delta = nc - c;
        if (delta <= 0 || rnd_unit() < exp(-(double)delta / T)) {
            c = nc;
            if (c < bestc) {
                bestc = c;
                save_best();
                if (c == 0) break;
            }
        } else {
            tmp = p[a1]; p[a1] = p[a2]; p[a2] = tmp;
        }
    }
    restore_best();
    return bestc;
}

static int kuhn(int a) {
    for (int p = Ea_start[a]; p < Ea_start[a + 1]; p++) {
        int e = Ea_list[p];
        if (used[e]) continue;
        int b = EB[e];
        if (vis[b] == visstamp) continue;
        vis[b] = visstamp;
        if (mB[b] < 0 || kuhn(mB[b])) {
            mB[b] = a;
            mA[a] = e;
            return 1;
        }
    }
    return 0;
}

static int decompose(void) {
    for (int l = 0; l < DG; l++) {
        for (int b = 0; b < N; b++) mB[b] = -1;
        for (int a = 0; a < N; a++) mA[a] = -1;
        for (int a = 0; a < N; a++) {
            visstamp++;
            if (!kuhn(a)) return 0;
        }
        for (int a = 0; a < N; a++) {
            int e = mA[a];
            used[e] = 1;
            sig[(size_t)l * CAP + a] = EB[e];
        }
    }
    return 1;
}

static void record_valid(void) {
    if (N > valid_N) {
        valid_N = N;
        copy_sig(vsig, sig, N);
    }
}

static void subdivide(void) {
    for (int l = 0; l < DG; l++) {
        int *p = sig + (size_t)l * CAP;
        int i = rnd_int(N);
        int j = p[i];
        p[i] = N;
        p[N] = j;
    }
    N++;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);
    if (DG < 1 || DIAM < 1) goto fail;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || m <= 0) goto fail;
    int *eu = malloc(sizeof(int) * (size_t)m);
    int *ev = malloc(sizeof(int) * (size_t)m);
    if (!eu || !ev) goto fail;
    for (int k = 0; k < m; k++) {
        if (scanf("%d %d", &eu[k], &ev[k]) != 2) goto fail;
        if (eu[k] < 0 || eu[k] >= n || ev[k] < 0 || ev[k] >= n || eu[k] == ev[k]) goto fail;
    }
    int *deg = calloc((size_t)n, sizeof(int));
    for (int k = 0; k < m; k++) { deg[eu[k]]++; deg[ev[k]]++; }
    for (int v = 0; v < n; v++)
        if (deg[v] != DG) goto fail;

    int *ast = malloc(sizeof(int) * (size_t)(n + 1));
    ast[0] = 0;
    for (int v = 0; v < n; v++) ast[v + 1] = ast[v] + deg[v];
    int *fp = malloc(sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) fp[v] = ast[v];
    int *adjv = malloc(sizeof(int) * (size_t)(2 * m));
    for (int k = 0; k < m; k++) {
        adjv[fp[eu[k]]++] = ev[k];
        adjv[fp[ev[k]]++] = eu[k];
    }

    int *col = malloc(sizeof(int) * (size_t)n);
    int *q = malloc(sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int u = q[qh++];
            for (int p = ast[u]; p < ast[u + 1]; p++) {
                int w = adjv[p];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    q[qt++] = w;
                } else if (col[w] == col[u]) {
                    goto fail;
                }
            }
        }
    }

    int *idx = malloc(sizeof(int) * (size_t)n);
    int c0 = 0, c1 = 0;
    for (int v = 0; v < n; v++) idx[v] = (col[v] == 0) ? c0++ : c1++;
    if (c0 != c1 || c0 < 1 || (long long)c0 * DG != m) goto fail;
    N = c0;

    CAP = N + CAPEXTRA;
    WCAP = (2 * CAP + 63) / 64;
    sig = calloc((size_t)DG * CAP, sizeof(int));
    bsig = calloc((size_t)DG * CAP, sizeof(int));
    vsig = calloc((size_t)DG * CAP, sizeof(int));
    nb = calloc((size_t)2 * CAP * DG, sizeof(int));
    cur = calloc((size_t)2 * CAP * WCAP, sizeof(uint64_t));
    nxt = calloc((size_t)2 * CAP * WCAP, sizeof(uint64_t));
    mA = malloc(sizeof(int) * (size_t)N);
    mB = malloc(sizeof(int) * (size_t)N);
    vis = calloc((size_t)N, sizeof(int));
    if (!sig || !bsig || !vsig || !nb || !cur || !nxt || !mA || !mB || !vis) goto fail;

    int *EA = malloc(sizeof(int) * (size_t)m);
    EB = malloc(sizeof(int) * (size_t)m);
    used = calloc((size_t)m, sizeof(int));
    Ea_start = calloc((size_t)(N + 1), sizeof(int));
    Ea_list = malloc(sizeof(int) * (size_t)m);
    if (!EA || !EB || !used || !Ea_start || !Ea_list) goto fail;
    for (int k = 0; k < m; k++) {
        int u = eu[k], v = ev[k];
        int a, b;
        if (col[u] == 0) { a = idx[u]; b = idx[v]; }
        else             { a = idx[v]; b = idx[u]; }
        EA[k] = a;
        EB[k] = b;
        Ea_start[a + 1]++;
    }
    for (int a = 0; a < N; a++) Ea_start[a + 1] += Ea_start[a];
    int *fillp = malloc(sizeof(int) * (size_t)N);
    for (int a = 0; a < N; a++) fillp[a] = Ea_start[a];
    for (int k = 0; k < m; k++) Ea_list[fillp[EA[k]]++] = k;

    if (!decompose()) goto fail;

    if (eval_cost() == 0) record_valid();
    while (elapsed() < DEADLINE) {
        long long bc = run_stage();
        if (bc == 0) {
            record_valid();
            if (N + 1 >= CAP) break;
            subdivide();
        }
    }

    if (valid_N > 0) {
        int VN = valid_N;
        printf("%d %d\n", 2 * VN, VN * DG);
        for (int l = 0; l < DG; l++)
            for (int a = 0; a < VN; a++)
                printf("%d %d\n", a, VN + vsig[(size_t)l * CAP + a]);
        return 0;
    }
fail:
    printf("0 0\n");
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
# Driver: exact/structured baselines, then stage A (lift search), then stage B
# (unstructured annealing with vertex-pair growth) seeded from the best graph.
# Every stage's output is validated before it can replace the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(g):
        nonlocal best, best_n
        try:
            n, e = g
        except Exception:
            return
        if n > best_n and lib.is_valid(n, e, d, D):
            best, best_n = (n, e), n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg)

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    total = 0.86 * time_limit - (time.monotonic() - t0) - 2.0
    if total < 3.0:
        return best

    # Stage A: structured voltage-lift search (parent engine), about 40% of the budget.
    budget_a = 0.4 * total
    try:
        out = lib.run_c(PARENT_SOURCE, [d, D, seed, f"{budget_a:.2f}", best_n],
                        timeout=budget_a + 15.0)
        consider(lib.parse_graph_text(out))
    except Exception:
        pass

    # Stage B: grow the best d-regular graph with unstructured annealing.
    budget_b = total - (time.monotonic() - t0)
    if budget_b >= 3.0:
        try:
            out = lib.run_c(GROW_SOURCE, [d, D, seed, f"{budget_b:.2f}"],
                            stdin_graph=best, timeout=budget_b + 15.0)
            consider(lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
