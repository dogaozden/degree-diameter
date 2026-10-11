import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Stage A: voltage-lift search over semidirect products Z_m x| Z_k2 with a
# K+K base, simulated annealing with breakout weights and an elite pool.
# (Unchanged engine: it produced the current 684-vertex start graph.)
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
# Stage B (new, high-risk): growth by repair.
#
# Instead of group lifts, keep a regular bipartite graph and grow it by two
# vertices (one A-side, one B-side). Degree is restored by re-routing d edges
# through the new pair. Then simulated annealing with double-edge switches
# (which preserve degrees and bipartiteness) tries to drive the number of
# ordered pairs at distance > D to zero. Successful steps are kept; failed
# steps roll back to the last valid graph. The output is always a valid
# graph (or "0 0" if the input was not usable).
#
# Diameter check: bitset BFS from every vertex, D rounds of OR over neighbours.
# ----------------------------------------------------------------------------

REP_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXV 4096
#define MAXD 8
#define MAXE (MAXV * MAXD / 2 + 64)
#define MAXW 64
#define SLICE 1.2

static int DG, DM, N, NE;
static int eu[MAXE], ev[MAXE];
static int adjn[MAXV * MAXD];
static int seu[MAXE], sev[MAXE], sadj[MAXV * MAXD];
static int sN, sNE;
static uint64_t BUF1[MAXV][MAXW], BUF2[MAXV][MAXW];
static uint64_t rs;
static double DEADLINE;

static uint64_t rnext(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rint_(int n) { return (int)(rnext() % (uint64_t)n); }
static double runit(void) { return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long eval_cost(void) {
    int w = (N + 63) / 64;
    uint64_t (*P)[MAXW] = BUF1, (*Q)[MAXW] = BUF2;
    for (int v = 0; v < N; v++) {
        for (int j = 0; j < w; j++) P[v][j] = 0;
        P[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int lvl = 0; lvl < DM; lvl++) {
        for (int v = 0; v < N; v++) {
            for (int j = 0; j < w; j++) Q[v][j] = P[v][j];
            const int *nb = adjn + v * DG;
            for (int k = 0; k < DG; k++) {
                const uint64_t *src = P[nb[k]];
                for (int j = 0; j < w; j++) Q[v][j] |= src[j];
            }
        }
        uint64_t (*tmp)[MAXW] = P;
        P = Q;
        Q = tmp;
    }
    long long cost = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int j = 0; j < w; j++) c += pc64(P[v][j]);
        cost += N - c;
    }
    return cost;
}

static void replace_nb(int v, int old, int nw) {
    int *p = adjn + v * DG;
    for (int k = 0; k < DG; k++)
        if (p[k] == old) { p[k] = nw; return; }
}

static int has_nb(int v, int u) {
    const int *p = adjn + v * DG;
    for (int k = 0; k < DG; k++)
        if (p[k] == u) return 1;
    return 0;
}

/* Edge k1 = (a1,b1), k2 = (a2,b2) become (a1,b2), (a2,b1). Applying twice undoes it. */
static void do_switch(int k1, int k2) {
    int a1 = eu[k1], b1 = ev[k1], a2 = eu[k2], b2 = ev[k2];
    ev[k1] = b2;
    ev[k2] = b1;
    replace_nb(a1, b1, b2);
    replace_nb(b1, a1, a2);
    replace_nb(a2, b2, b1);
    replace_nb(b2, a2, a1);
}

static int switch_ok(int k1, int k2) {
    int a1 = eu[k1], b1 = ev[k1], a2 = eu[k2], b2 = ev[k2];
    return a1 != a2 && b1 != b2 && !has_nb(a1, b2) && !has_nb(a2, b1);
}

static int sa_attempt(double tend) {
    long long cur = eval_cost();
    if (cur == 0) return 1;
    double t0 = now();
    double dur = tend - t0;
    if (dur <= 0) return 0;
    double frac = 0.0;
    for (long long it = 0;; it++) {
        if ((it & 7) == 0) {
            double t = now();
            if (t >= tend) break;
            frac = (t - t0) / dur;
        }
        double temp = 3.0 * (1.0 - frac) + 0.05;
        int k1 = rint_(NE), k2 = rint_(NE);
        if (k1 == k2 || !switch_ok(k1, k2)) continue;
        do_switch(k1, k2);
        long long c = eval_cost();
        if (c <= cur || runit() < exp(-(double)(c - cur) / temp)) {
            cur = c;
            if (cur == 0) return 1;
        } else {
            do_switch(k1, k2);
        }
    }
    return 0;
}

static void save_state(void) {
    sN = N;
    sNE = NE;
    memcpy(seu, eu, sizeof(int) * (size_t)NE);
    memcpy(sev, ev, sizeof(int) * (size_t)NE);
    memcpy(sadj, adjn, sizeof(int) * (size_t)N * DG);
}

static void load_state(void) {
    N = sN;
    NE = sNE;
    memcpy(eu, seu, sizeof(int) * (size_t)NE);
    memcpy(ev, sev, sizeof(int) * (size_t)NE);
    memcpy(adjn, sadj, sizeof(int) * (size_t)N * DG);
}

/* Add vertices as = N (A side) and bs = N+1 (B side). Pick DG edges (x_i, y_i) with
   distinct x and distinct y; turn each into (x_i, bs) and append (as, y_i).
   Every degree is kept at DG. */
static int grow(void) {
    if (N + 2 > MAXV || NE + DG > MAXE) return 0;
    int as = N, bs = N + 1;
    int ch[MAXD], nc = 0;
    for (int tries = 0; tries < 4000 && nc < DG; tries++) {
        int k = rint_(NE);
        int ok = 1;
        for (int i = 0; i < nc; i++) {
            if (ch[i] == k || eu[ch[i]] == eu[k] || ev[ch[i]] == ev[k]) { ok = 0; break; }
        }
        if (ok) ch[nc++] = k;
    }
    if (nc < DG) return 0;
    for (int i = 0; i < DG; i++) {
        int k = ch[i], x = eu[k], y = ev[k];
        ev[k] = bs;
        replace_nb(x, y, bs);
        replace_nb(y, x, as);
        eu[NE + i] = as;
        ev[NE + i] = y;
        adjn[as * DG + i] = y;
        adjn[bs * DG + i] = x;
    }
    NE += DG;
    N += 2;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    DG = atoi(argv[1]);
    DM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    double t0 = now();
    DEADLINE = t0 + budget;
    rs = sd * 2654435761ULL + 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnext();
    if (DG < 1 || DG > MAXD || DM < 1) {
        printf("0 0\n");
        return 0;
    }

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXV || m < 0 || m > MAXE) {
        printf("0 0\n");
        return 0;
    }
    int *ju = malloc(sizeof(int) * (size_t)(m + 1));
    int *jv = malloc(sizeof(int) * (size_t)(m + 1));
    int fill[MAXV];
    memset(fill, 0, sizeof fill);
    int bad = 0;
    for (int i = 0; i < m && !bad; i++) {
        if (scanf("%d %d", &ju[i], &jv[i]) != 2) { bad = 1; break; }
        int u = ju[i], v = jv[i];
        if (u < 0 || u >= n || v < 0 || v >= n || u == v) { bad = 1; break; }
        if (fill[u] >= DG || fill[v] >= DG) { bad = 1; break; }
        adjn[u * DG + fill[u]++] = v;
        adjn[v * DG + fill[v]++] = u;
    }
    for (int v = 0; v < n && !bad; v++)
        if (fill[v] != DG) bad = 1;

    int col[MAXV], qu[MAXV];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n && !bad; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        qu[qt++] = s;
        while (qh < qt && !bad) {
            int u = qu[qh++];
            for (int k = 0; k < DG; k++) {
                int v = adjn[u * DG + k];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    qu[qt++] = v;
                } else if (col[v] == col[u]) {
                    bad = 1;
                    break;
                }
            }
        }
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    N = n;
    NE = m;
    for (int i = 0; i < m; i++) {
        if (col[ju[i]] == 0) { eu[i] = ju[i]; ev[i] = jv[i]; }
        else { eu[i] = jv[i]; ev[i] = ju[i]; }
    }
    free(ju);
    free(jv);

    int ok = (eval_cost() == 0);
    if (!ok) ok = sa_attempt(t0 + 0.5 * budget);
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    save_state();

    while (now() < DEADLINE) {
        if (!grow()) break;
        double tend = now() + SLICE;
        if (tend > DEADLINE) tend = DEADLINE;
        if (sa_attempt(tend)) save_state();
        else load_state();
    }

    printf("%d %d\n", sN, sNE);
    for (int i = 0; i < sNE; i++)
        printf("%d %d\n", seu[i], sev[i]);
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
# Driver: baselines, then lift search (stage A), then growth repair (stage B).
# Every stage output is validated; the largest valid graph is returned.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    def left():
        return 0.93 * time_limit - (time.monotonic() - start)

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

    total = left() - 3.0
    if total < 2.0:
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    # Stage A: lift search gets the larger share of the time.
    lift_budget = 0.55 * total
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{lift_budget:.2f}", 0],
                        timeout=lift_budget + 10.0)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except Exception:
        pass

    # Stage B: grow the best valid graph by repair (new construction family).
    rep_budget = left() - 1.5
    if rep_budget >= 1.0:
        try:
            out = lib.run_c(REP_SOURCE, [d, D, seed, f"{rep_budget:.2f}"],
                            stdin_graph=best, timeout=rep_budget + 10.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
