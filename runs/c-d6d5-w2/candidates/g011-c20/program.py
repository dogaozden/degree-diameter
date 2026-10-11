import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Engine A: voltage lifts of semidirect products Z_m x| Z_k2 over a small base
# (K A-vertices, K B-vertices), searched by annealing with breakout weights and
# an elite pool (iterated local search). Proven family; keeps the record line.
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
# Engine B (new, unstructured): bipartite DEG-regular graphs on S + S vertices,
# no group symmetry. Layers are perfect matchings; search moves are edge
# switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), which keep every degree exact
# and keep the graph simple. Cost = number of ordered vertex pairs at distance
# more than D, computed by bit-parallel BFS over all vertices at once.
# Annealing with random restarts; on success the side size grows by one.
# ----------------------------------------------------------------------------

SWITCH_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define SW_ITERS 150000
#define SW_T0 20.0
#define SW_T1 0.3

static uint64_t us[2];
static struct timespec U0;
static double udeadline;

static uint64_t usplit(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t urnd(void) {
    uint64_t s1 = us[0];
    const uint64_t s0 = us[1];
    us[0] = s0;
    s1 ^= s1 << 23;
    us[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return us[1] + s0;
}

static int urint(int n) { return (int)(urnd() % (uint64_t)n); }
static double urunit(void) { return (double)(urnd() >> 11) * (1.0 / 9007199254740992.0); }

static double uelapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - U0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - U0.tv_nsec);
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int SDEG, SDIAM, SS, SN, SW, SE;
static int *sea, *seb, *sadj, *scnt;
static unsigned char *sused;
static uint64_t *sR0, *sR1;

static void setup_size(int S) {
    SS = S;
    SN = 2 * S;
    SW = (SN + 63) / 64;
    SE = SDEG * S;
    sea = malloc(sizeof(int) * (size_t)SE);
    seb = malloc(sizeof(int) * (size_t)SE);
    sadj = malloc(sizeof(int) * (size_t)SN * SDEG);
    scnt = malloc(sizeof(int) * (size_t)SN);
    sused = calloc((size_t)SS * SS, 1);
    sR0 = malloc(sizeof(uint64_t) * (size_t)SN * SW);
    sR1 = malloc(sizeof(uint64_t) * (size_t)SN * SW);
    for (int k = 0; k < SE; k++) sea[k] = k % SS;
}

static void free_size(void) {
    free(sea); free(seb); free(sadj); free(scnt); free(sused); free(sR0); free(sR1);
    sea = seb = sadj = scnt = NULL;
    sused = NULL;
    sR0 = sR1 = NULL;
}

/* Layers are random perfect matchings avoiding all earlier pairs (simple graph). */
static int sw_init(void) {
    memset(sused, 0, (size_t)SS * SS);
    int *p = malloc(sizeof(int) * (size_t)SS);
    for (int l = 0; l < SDEG; l++) {
        int ok = 0;
        for (int tr = 0; tr < 20000 && !ok; tr++) {
            for (int i = 0; i < SS; i++) p[i] = i;
            for (int i = SS - 1; i > 0; i--) {
                int j = urint(i + 1);
                int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
            }
            ok = 1;
            for (int i = 0; i < SS; i++)
                if (sused[(size_t)i * SS + p[i]]) { ok = 0; break; }
        }
        if (!ok) { free(p); return 0; }
        for (int i = 0; i < SS; i++) {
            int k = l * SS + i;
            seb[k] = p[i];
            sused[(size_t)i * SS + p[i]] = 1;
        }
    }
    free(p);
    return 1;
}

/* Number of ordered pairs (v,w) with dist(v,w) > SDIAM. Zero iff valid. */
static long long sw_eval(void) {
    int N = SN, W = SW, E = SE, DEG = SDEG;
    for (int v = 0; v < N; v++) scnt[v] = 0;
    for (int k = 0; k < E; k++) {
        int a = sea[k], b = SS + seb[k];
        sadj[(size_t)a * DEG + scnt[a]++] = b;
        sadj[(size_t)b * DEG + scnt[b]++] = a;
    }
    memset(sR0, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) sR0[(size_t)v * W + (v >> 6)] = 1ULL << (v & 63);
    uint64_t *cur = sR0, *nxt = sR1;
    for (int step = 0; step < SDIAM; step++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            const int *av = sadj + (size_t)v * DEG;
            for (int e = 0; e < DEG; e++) {
                const uint64_t *ru = cur + (size_t)av[e] * W;
                for (int w = 0; w < W; w++) dst[w] |= ru[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long cost = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        const uint64_t *rv = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += popc64(rv[w]);
        cost += N - c;
    }
    return cost;
}

/* Edge-switch annealing. Returns the cost of the final state (0 means valid). */
static long long sw_anneal(long long cost, int iters) {
    double lr = log(SW_T1 / SW_T0);
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 127) == 0 && uelapsed() > udeadline) break;
        int k1 = urint(SE), k2 = urint(SE);
        int a1 = sea[k1], a2 = sea[k2], b1 = seb[k1], b2 = seb[k2];
        if (a1 == a2 || b1 == b2) continue;
        if (sused[(size_t)a1 * SS + b2] || sused[(size_t)a2 * SS + b1]) continue;
        sused[(size_t)a1 * SS + b1] = 0;
        sused[(size_t)a2 * SS + b2] = 0;
        sused[(size_t)a1 * SS + b2] = 1;
        sused[(size_t)a2 * SS + b1] = 1;
        seb[k1] = b2;
        seb[k2] = b1;
        long long nc = sw_eval();
        double T = SW_T0 * exp(lr * (double)it / (double)iters);
        long long dl = nc - cost;
        if (dl <= 0 || urunit() < exp(-(double)dl / T)) {
            cost = nc;
        } else {
            sused[(size_t)a1 * SS + b2] = 0;
            sused[(size_t)a2 * SS + b1] = 0;
            sused[(size_t)a1 * SS + b1] = 1;
            sused[(size_t)a2 * SS + b2] = 1;
            seb[k1] = b1;
            seb[k2] = b2;
        }
    }
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_S]\n");
        return 1;
    }
    timespec_get(&U0, TIME_UTC);
    SDEG = atoi(argv[1]);
    SDIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    udeadline = atof(argv[4]);
    int S = argc > 5 ? atoi(argv[5]) : 2;
    if (SDEG < 2 || SDIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    if (S < SDEG) S = SDEG;
    uint64_t sm = sd * 2654435761ULL + 999ULL;
    us[0] = usplit(&sm);
    us[1] = usplit(&sm);

    int found_S = 0;
    int *found_b = NULL;
    while (uelapsed() < udeadline) {
        setup_size(S);
        if (sw_init()) {
            long long cost = sw_eval();
            cost = sw_anneal(cost, SW_ITERS);
            if (cost == 0) {
                free(found_b);
                found_b = malloc(sizeof(int) * (size_t)SE);
                memcpy(found_b, seb, sizeof(int) * (size_t)SE);
                found_S = S;
                S++;
            }
        }
        free_size();
    }

    if (found_S > 0) {
        int E = SDEG * found_S;
        printf("%d %d\n", 2 * found_S, E);
        for (int k = 0; k < E; k++)
            printf("%d %d\n", k % found_S, found_S + found_b[k]);
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
# Driver: baselines, then engine A (lift search, about half the slice), then
# engine B (unstructured edge-switch search seeded above the best size so far).
# Every engine result is validated; the best valid graph is always returned.
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

    def left():
        # Reserve covers C compiles (outside the C deadline), parsing and validation.
        return 0.9 * time_limit - (time.monotonic() - start) - 1.5

    # Engine A: lift search, about half of the remaining budget.
    rem = left()
    if rem >= 1.0:
        budget = 0.5 * rem if (d >= 3 and D >= 3) else rem
        try:
            out = lib.run_c(LIFT_SOURCE, [d, D, seed, f"{budget:.2f}", best_n],
                            timeout=budget + 6.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Engine B: unstructured edge-switch search for side size above the current best.
    if d >= 3 and D >= 3:
        rem = left()
        if rem >= 1.0:
            start_S = best_n // 2 + 1
            try:
                out = lib.run_c(SWITCH_SOURCE, [d, D, seed, f"{rem:.2f}", start_S],
                                timeout=rem + 6.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
