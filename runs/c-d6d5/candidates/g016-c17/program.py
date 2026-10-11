import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 (C_LIFT): voltage lifts of semidirect products Z_m x| Z_k2 over a base
# of K A-vertices and K B-vertices, searched by simulated annealing with breakout
# weights and an elite pool (iterated local search). Unchanged from the parent.
#
# Stage 2 (C_GROW): a different construction. It takes a valid bipartite graph
# and grows it by two vertices x (side A) and y (side B) with a degree-preserving
# switch. Pick DEG-1 pairwise vertex-disjoint base edges (a_i, b_i), delete them,
# and add x-b_i, y-a_i for all i, plus the edge x-y. Degrees stay exactly DEG.
# The choice of removed edges is annealed to minimise uncovered ordered pairs at
# distance > DIAM. A zero-cost state is a valid graph two vertices larger.
# Growth repeats while time remains, starting from the best stage-1 graph.
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


C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 3000
#define ECAP (NMAX * 8)
#define DMAX 16
#define ITERS 1200

static uint64_t rs[2];
static struct timespec T0;
static double DL;

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

static int DEG, DIAM, N, M0;
static int eu[ECAP], ev[ECAP], tu[ECAP], tv[ECAP];
static unsigned char isrem[ECAP];
static int col[NMAX];
static int adj[NMAX * DMAX];
static int cnt[NMAX];
static int stamp[NMAX];
static int cur = 0;
static int fr[NMAX], nx[NMAX];
static int usedv[NMAX];

static void add_adj(int u, int v) {
    adj[(size_t)u * DMAX + cnt[u]++] = v;
}

/* Cost = ordered pairs at distance > DIAM in the graph with DEG-1 base edges removed
   and new vertices x = N (side A) and y = N+1 (side B) attached by the switch. */
static long long eval_removed(const int *R, int nr) {
    int NN = N + 2, x = N, y = N + 1;
    for (int v = 0; v < NN; v++) cnt[v] = 0;
    for (int i = 0; i < nr; i++) isrem[R[i]] = 1;
    for (int i = 0; i < M0; i++)
        if (!isrem[i]) {
            add_adj(eu[i], ev[i]);
            add_adj(ev[i], eu[i]);
        }
    for (int i = 0; i < nr; i++) isrem[R[i]] = 0;
    for (int i = 0; i < nr; i++) {
        int u = eu[R[i]], v = ev[R[i]];
        int a = (col[u] == 0) ? u : v;
        int b = (a == u) ? v : u;
        add_adj(x, b); add_adj(b, x);
        add_adj(y, a); add_adj(a, y);
    }
    add_adj(x, y); add_adj(y, x);

    long long total = 0;
    for (int s = 0; s < NN; s++) {
        cur++;
        int fsz = 1, reached = 1;
        fr[0] = s;
        stamp[s] = cur;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                int f = fr[q];
                const int *au = adj + (size_t)f * DMAX;
                for (int e = 0; e < cnt[f]; e++) {
                    int w = au[e];
                    if (stamp[w] != cur) {
                        stamp[w] = cur;
                        nx[nsz++] = w;
                    }
                }
            }
            reached += nsz;
            memcpy(fr, nx, sizeof(int) * (size_t)nsz);
            fsz = nsz;
        }
        total += NN - reached;
    }
    return total;
}

static int compatible(const int *R, int nr, int j, int e) {
    int u = eu[e], v = ev[e];
    for (int i = 0; i < nr; i++) {
        if (i == j) continue;
        int f = R[i];
        if (eu[f] == u || eu[f] == v || ev[f] == u || ev[f] == v) return 0;
    }
    return 1;
}

static int random_matching(int *R, int nr) {
    for (int v = 0; v < N; v++) usedv[v] = 0;
    int k = 0;
    for (long tries = 0; tries < 400000 && k < nr; tries++) {
        int e = rnd_int(M0);
        int u = eu[e], v = ev[e];
        if (usedv[u] || usedv[v]) continue;
        usedv[u] = 1;
        usedv[v] = 1;
        R[k++] = e;
    }
    for (int i = 0; i < k; i++) {
        usedv[eu[R[i]]] = 0;
        usedv[ev[R[i]]] = 0;
    }
    return k == nr;
}

static void commit(const int *R, int nr) {
    for (int i = 0; i < nr; i++) isrem[R[i]] = 1;
    int nm = 0;
    for (int i = 0; i < M0; i++)
        if (!isrem[i]) {
            tu[nm] = eu[i];
            tv[nm] = ev[i];
            nm++;
        }
    for (int i = 0; i < nr; i++) isrem[R[i]] = 0;
    int x = N, y = N + 1;
    col[x] = 0;
    col[y] = 1;
    for (int i = 0; i < nr; i++) {
        int u = eu[R[i]], v = ev[R[i]];
        int a = (col[u] == 0) ? u : v;
        int b = (a == u) ? v : u;
        tu[nm] = x; tv[nm] = b; nm++;
        tu[nm] = y; tv[nm] = a; nm++;
    }
    tu[nm] = x;
    tv[nm] = y;
    nm++;
    memcpy(eu, tu, sizeof(int) * (size_t)nm);
    memcpy(ev, tv, sizeof(int) * (size_t)nm);
    M0 = nm;
    N += 2;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DL = atof(argv[4]);
    uint64_t sm = sd * 2654435761ULL + 999ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int n = 0, m = 0;
    if (DEG < 2 || DEG > DMAX || DIAM < 1 ||
        scanf("%d %d", &n, &m) != 2 || n < 1 || n > NMAX - 4 || m < 0 || m > ECAP) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    M0 = m;
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2 ||
            eu[i] < 0 || eu[i] >= n || ev[i] < 0 || ev[i] >= n || eu[i] == ev[i]) {
            printf("0 0\n");
            return 0;
        }
    }
    /* Degree check, then bipartition by BFS. */
    for (int v = 0; v < n; v++) cnt[v] = 0;
    for (int i = 0; i < m; i++) {
        cnt[eu[i]]++;
        cnt[ev[i]]++;
    }
    for (int v = 0; v < n; v++)
        if (cnt[v] > DEG) {
            printf("0 0\n");
            return 0;
        }
    for (int v = 0; v < n; v++) cnt[v] = 0;
    for (int i = 0; i < m; i++) {
        add_adj(eu[i], ev[i]);
        add_adj(ev[i], eu[i]);
    }
    for (int v = 0; v < n; v++) col[v] = -1;
    int ok = 1;
    for (int s = 0; s < n && ok; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int top = 0;
        fr[top++] = s;
        while (top > 0 && ok) {
            int u = fr[--top];
            for (int e = 0; e < cnt[u]; e++) {
                int w = adj[(size_t)u * DMAX + e];
                if (col[w] == -1) {
                    col[w] = 1 - col[u];
                    fr[top++] = w;
                } else if (col[w] == col[u]) {
                    ok = 0;
                }
            }
        }
    }
    int nr = DEG - 1;
    if (!ok || M0 < nr) {
        printf("0 0\n");
        return 0;
    }

    int R[DMAX], bestR[DMAX];
    while (elapsed() < DL && N + 2 <= NMAX - 4) {
        if (!random_matching(R, nr)) break;
        long long cost = eval_removed(R, nr);
        long long best = cost;
        memcpy(bestR, R, sizeof(int) * (size_t)nr);
        for (int it = 0; it < ITERS && cost > 0; it++) {
            if ((it & 15) == 0 && elapsed() > DL) break;
            int j = rnd_int(nr);
            int e = rnd_int(M0);
            if (e == R[j] || !compatible(R, nr, j, e)) continue;
            int old = R[j];
            R[j] = e;
            long long c2 = eval_removed(R, nr);
            double temp = 2.0 + 40.0 * (1.0 - (double)it / ITERS);
            if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < best) {
                    best = cost;
                    memcpy(bestR, R, sizeof(int) * (size_t)nr);
                }
            } else {
                R[j] = old;
            }
        }
        if (best == 0) {
            commit(bestR, nr);
        } else if (elapsed() > DL) {
            break;
        }
    }

    printf("%d %d\n", N, M0);
    for (int i = 0; i < M0; i++) printf("%d %d\n", eu[i], ev[i]);
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
# Driver: baselines, then the stage-1 lift annealer, then the stage-2 grower
# that starts from the best valid graph found so far.
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

    total = 0.93 * time_limit - (time.monotonic() - start) - 1.0
    if total < 2.0:
        return best if lib.is_valid(best[0], best[1], d, D) else lib.haar_graph(d, range(d))

    # Stage 1: lift annealer gets about half of the usable time.
    lift_budget = 0.5 * total
    try:
        out = lib.run_c(C_LIFT, [d, D, seed, f"{lift_budget:.2f}", best_n],
                        timeout=lift_budget + 5.0)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except Exception:
        pass

    # Stage 2: grow the best valid graph by degree-preserving two-vertex switches.
    grow_budget = 0.93 * time_limit - (time.monotonic() - start) - 1.5
    if grow_budget >= 2.0:
        try:
            out = lib.run_c(C_GROW, [d, D, seed, f"{grow_budget:.2f}"],
                            stdin_graph=best, timeout=grow_budget + 5.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
