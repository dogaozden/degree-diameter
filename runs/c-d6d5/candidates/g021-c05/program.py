import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: a second, unstructured search family.
#
# Phase 1 runs the previous voltage-lift annealer (PARENT_C) on part of the
# budget. Phase 2 runs GROW_C, which works on arbitrary d-regular bipartite
# graphs instead of group lifts:
#   * state: two sides A, B of size N, every vertex of degree exactly d;
#   * move: a degree-preserving edge switch (a1,b1),(a2,b2) -> (a1,b2),(a2,b1);
#   * cost: number of ordered vertex pairs at distance > D (bitset BFS);
#   * when cost reaches 0 the graph is valid and is snapshotted, then grown by
#     one vertex on each side: d disjoint edges (a_i,b_i) are replaced by
#     a*-b_i and b*-a_i, which keeps every degree at d, and annealing repairs
#     the new pairs.
# GROW_C starts from the best graph found so far when that graph is regular
# with equal sides, so it extends structured records; otherwise it starts from
# a circulant. Every output is re-checked with lib.is_valid, and the best valid
# graph seen so far is always kept as the fallback.
# ----------------------------------------------------------------------------

GROW_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define CAPN 2048
#define CAPV (2 * CAPN)
#define CAPW (CAPV / 64)
#define TEMP_CYCLE 30000
#define MAXD 64

static int d, D, N;
static int *nbA, *nbB;          /* nbA[a*d+k] = b in [0,N); nbB[b*d+k] = a in [0,N) */
static unsigned char *Mx;       /* Mx[a*CAPN+b] = 1 iff a-b is an edge */
static uint64_t *cur, *nxt;
static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

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

/* Number of ordered pairs (v,u) with dist(v,u) > D. */
static long long eval_cost(void) {
    int V = 2 * N;
    int W = (V + 63) / 64;
    for (int v = 0; v < V; v++) {
        uint64_t *row = cur + (size_t)v * W;
        memset(row, 0, sizeof(uint64_t) * (size_t)W);
        row[v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < V; v++) {
            uint64_t *out = nxt + (size_t)v * W;
            const uint64_t *in = cur + (size_t)v * W;
            memcpy(out, in, sizeof(uint64_t) * (size_t)W);
            if (v < N) {
                const int *nb = nbA + (size_t)v * d;
                for (int k = 0; k < d; k++) {
                    const uint64_t *ur = cur + (size_t)(N + nb[k]) * W;
                    for (int w = 0; w < W; w++) out[w] |= ur[w];
                }
            } else {
                const int *nb = nbB + (size_t)(v - N) * d;
                for (int k = 0; k < d; k++) {
                    const uint64_t *ur = cur + (size_t)nb[k] * W;
                    for (int w = 0; w < W; w++) out[w] |= ur[w];
                }
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long unc = 0;
    for (int v = 0; v < V; v++) {
        const uint64_t *row = cur + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += popc64(row[w]);
        unc += V - cnt;
    }
    return unc;
}

/* Edge switch: a1-b1, a2-b2 become a1-b2, a2-b1. Caller ensures validity.
   Applying the same call again undoes it. */
static void apply_swap(int a1, int k1, int a2, int k2) {
    int b1 = nbA[a1 * d + k1];
    int b2 = nbA[a2 * d + k2];
    nbA[a1 * d + k1] = b2;
    nbA[a2 * d + k2] = b1;
    for (int k = 0; k < d; k++)
        if (nbB[b1 * d + k] == a1) { nbB[b1 * d + k] = a2; break; }
    for (int k = 0; k < d; k++)
        if (nbB[b2 * d + k] == a2) { nbB[b2 * d + k] = a1; break; }
    Mx[a1 * CAPN + b1] = 0;
    Mx[a2 * CAPN + b2] = 0;
    Mx[a1 * CAPN + b2] = 1;
    Mx[a2 * CAPN + b1] = 1;
}

static void snapshot(void) {
    best_n = 2 * N;
    best_m = N * d;
    for (int a = 0; a < N; a++)
        for (int k = 0; k < d; k++) {
            int idx = a * d + k;
            best_e[2 * idx] = a;
            best_e[2 * idx + 1] = N + nbA[idx];
        }
}

/* Add one vertex per side. Pick d edges with distinct endpoints (a_i,b_i) and
   replace them by a*-b_i and b*-a_i. Every degree stays d. */
static int grow(void) {
    int ia[MAXD], ib[MAXD], ka[MAXD];
    if (N + 1 > CAPN) return 0;
    for (int i = 0; i < d; i++) {
        int ok = 0;
        for (int tries = 0; tries < 2000 && !ok; tries++) {
            int a = rnd_int(N), k = rnd_int(d);
            int b = nbA[a * d + k];
            int dup = 0;
            for (int j = 0; j < i; j++)
                if (ia[j] == a || ib[j] == b) { dup = 1; break; }
            if (dup) continue;
            ia[i] = a; ib[i] = b; ka[i] = k; ok = 1;
        }
        if (!ok) return 0;
    }
    int Na = N;
    for (int i = 0; i < d; i++) {
        int a = ia[i], b = ib[i], k = ka[i];
        nbA[a * d + k] = Na;                     /* a was adjacent to b, now to B* */
        for (int j = 0; j < d; j++)
            if (nbB[b * d + j] == a) { nbB[b * d + j] = Na; break; }   /* b now to A* */
        nbA[Na * d + i] = b;                     /* A* adjacent to b */
        nbB[Na * d + i] = a;                     /* B* adjacent to a */
        Mx[a * CAPN + b] = 0;
        Mx[a * CAPN + Na] = 1;
        Mx[Na * CAPN + b] = 1;
    }
    N = Na + 1;
    return 1;
}

static void init_circulant(int n0) {
    N = n0;
    memset(Mx, 0, (size_t)CAPN * CAPN);
    for (int a = 0; a < N; a++)
        for (int k = 0; k < d; k++) {
            int b = (a + k) % N;
            nbA[a * d + k] = b;
            Mx[a * CAPN + b] = 1;
        }
    for (int b = 0; b < N; b++)
        for (int k = 0; k < d; k++)
            nbB[b * d + k] = ((b - k) % N + N) % N;
}

/* Read an optional start graph from stdin. Returns 1 if it is d-regular,
   bipartite with equal sides, simple, and loaded into the state. */
static int load_start(void) {
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 2 || m <= 0 || n > CAPV || m > CAPV * MAXD) return 0;
    int *eu = malloc(sizeof(int) * (size_t)m);
    int *ev = malloc(sizeof(int) * (size_t)m);
    int *deg = calloc((size_t)n, sizeof(int));
    int *start = malloc(sizeof(int) * (size_t)(n + 1));
    int *fill = calloc((size_t)n, sizeof(int));
    int *adj = malloc(sizeof(int) * (size_t)(2 * m));
    int *col = malloc(sizeof(int) * (size_t)n);
    int *queue = malloc(sizeof(int) * (size_t)n);
    int *idx = malloc(sizeof(int) * (size_t)n);
    int *fa = NULL, *fb = NULL;
    int ok = 1;

    for (int i = 0; i < m && ok; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { ok = 0; break; }
        if (eu[i] < 0 || eu[i] >= n || ev[i] < 0 || ev[i] >= n || eu[i] == ev[i]) { ok = 0; break; }
        deg[eu[i]]++;
        deg[ev[i]]++;
    }
    for (int v = 0; v < n && ok; v++)
        if (deg[v] != d) ok = 0;
    if (ok) {
        start[0] = 0;
        for (int v = 0; v < n; v++) start[v + 1] = start[v] + deg[v];
        for (int i = 0; i < m; i++) {
            int u = eu[i], v = ev[i];
            adj[start[u] + fill[u]++] = v;
            adj[start[v] + fill[v]++] = u;
        }
        for (int v = 0; v < n; v++) col[v] = -1;
        for (int s = 0; s < n && ok; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int qh = 0, qt = 0;
            queue[qt++] = s;
            while (qh < qt) {
                int u = queue[qh++];
                for (int j = start[u]; j < start[u + 1]; j++) {
                    int v = adj[j];
                    if (col[v] < 0) { col[v] = 1 - col[u]; queue[qt++] = v; }
                    else if (col[v] == col[u]) { ok = 0; break; }
                }
                if (!ok) break;
            }
        }
    }
    if (ok) {
        int c0 = 0, c1 = 0;
        for (int v = 0; v < n; v++) {
            if (col[v] == 0) idx[v] = c0++;
            else idx[v] = c1++;
        }
        if (c0 != c1 || c0 > CAPN || c0 < 1) ok = 0;
        else {
            N = c0;
            memset(Mx, 0, (size_t)CAPN * CAPN);
            fa = calloc((size_t)N, sizeof(int));
            fb = calloc((size_t)N, sizeof(int));
            for (int i = 0; i < m && ok; i++) {
                int x = eu[i], y = ev[i];
                if (col[x] == 1) { int t = x; x = y; y = t; }
                int a = idx[x], b = idx[y];
                if (Mx[a * CAPN + b]) { ok = 0; break; }
                Mx[a * CAPN + b] = 1;
                if (fa[a] >= d || fb[b] >= d) { ok = 0; break; }
                nbA[a * d + fa[a]++] = b;
                nbB[b * d + fb[b]++] = a;
            }
        }
    }
    free(eu); free(ev); free(deg); free(start); free(fill); free(adj);
    free(col); free(queue); free(idx); free(fa); free(fb);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [min_n]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int min_n = argc > 5 ? atoi(argv[5]) : 0;
    if (d < 2 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    nbA = malloc(sizeof(int) * (size_t)CAPN * d);
    nbB = malloc(sizeof(int) * (size_t)CAPN * d);
    Mx = calloc((size_t)CAPN * CAPN, 1);
    cur = malloc(sizeof(uint64_t) * (size_t)CAPV * CAPW);
    nxt = malloc(sizeof(uint64_t) * (size_t)CAPV * CAPW);
    best_e = malloc(sizeof(int) * 2 * (size_t)CAPN * d);
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    if (!load_start()) {
        int n0 = min_n / 2 + 1;
        if (n0 < d) n0 = d;
        if (n0 > CAPN - 1) {
            printf("0 0\n");
            return 0;
        }
        init_circulant(n0);
    }

    long long cost = eval_cost();
    int cyc = 0;
    while (elapsed() < DEADLINE) {
        if (cost == 0) {
            if (2 * N > best_n) snapshot();
            if (grow()) {
                cost = eval_cost();
                cyc = 0;
                continue;
            }
        }
        int a1 = rnd_int(N), a2 = rnd_int(N);
        if (a1 == a2) continue;
        int k1 = rnd_int(d), k2 = rnd_int(d);
        int b1 = nbA[a1 * d + k1], b2 = nbA[a2 * d + k2];
        if (b1 == b2 || Mx[a1 * CAPN + b2] || Mx[a2 * CAPN + b1]) continue;
        apply_swap(a1, k1, a2, k2);
        long long c2 = eval_cost();
        double temp = 0.25 + 2.5 * pow(0.9995, (double)cyc);
        cyc = (cyc + 1) % TEMP_CYCLE;
        if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
        } else {
            apply_swap(a1, k1, a2, k2);
        }
    }

    if (best_n > 0) {
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
# Previous engine (voltage lifts of semidirect products, annealing with
# breakout weights and an elite-pool ILS). Kept as phase 1 so the record
# family stays covered.
# ----------------------------------------------------------------------------

PARENT_C = r"""
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
# Python constructions and glue.
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


def _is_regular(n, edges, d):
    """True if the graph has an even order and every vertex has degree exactly d."""
    if n < 2 or n % 2:
        return False
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


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
        # Keep 2 s of slack per engine run for compilation, parsing and validation.
        return 0.92 * time_limit - (time.monotonic() - start) - 2.0

    # Phase 1: voltage-lift annealer (previous best family).
    b1 = 0.6 * left()
    if b1 >= 1.0:
        try:
            out = lib.run_c(PARENT_C, [d, D, seed, f"{b1:.2f}", best_n],
                            timeout=b1 + 10.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Phase 2: grow the best regular graph found so far with the unstructured engine.
    b2 = left()
    if b2 >= 1.0:
        seed_graph = best if _is_regular(best[0], best[1], d) else None
        try:
            out = lib.run_c(GROW_C, [d, D, seed + 1, f"{b2:.2f}", best_n],
                            stdin_graph=seed_graph, timeout=b2 + 10.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
