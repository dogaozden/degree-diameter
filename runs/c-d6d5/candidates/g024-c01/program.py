import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Two-stage search for d-regular-ish bipartite graphs of diameter D.
#
# Stage 1 (C_LIFT): the voltage-lift annealer over semidirect products, as before.
#   It supplies a large structured start graph, typically the 684-vertex lift
#   for d=6, D=5.
#
# Stage 2 (C_GROW), the new and deliberately different idea: abandon the group
#   symmetry and work on the bare graph. The engine keeps a VALID graph, adds
#   one A-vertex and one B-vertex, and then repairs the graph without any group
#   structure. Moves are degree-preserving edge swaps, endpoint rewires onto
#   deficient vertices, and additions of edges between deficient vertices. The
#   cost is the number of ordered vertex pairs at distance > D, computed by
#   bitset BFS from every vertex. When the cost reaches 0, the state is saved
#   and grown again. If a growth attempt stalls for one cycle, the engine
#   restores the last valid snapshot and tries again with fresh moves.
#
# Vertices are labelled 0..n-1; side A is marked explicitly (isA), not by index,
# so growth can append vertices freely. Bipartiteness holds by construction
# because every edge joins an A vertex to a B vertex. Degrees never exceed DEG,
# and duplicate edges are rejected through an adjacency matrix. Python validates
# everything with lib.is_valid and keeps a valid fallback.
# ----------------------------------------------------------------------------

C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define GMAXN 1400
#define GMAXW ((GMAXN + 63) / 64)
#define GMAXE (GMAXN * 16)
#define T_HI 6.0
#define T_LO 0.3

static int DEG, DIAM, N, NE;
static double DEADLINE, CYC;
static struct timespec T0;
static uint64_t rs[2];

static int eA[GMAXE], eB[GMAXE];
static int deg[GMAXN];
static unsigned char adjm[GMAXN][GMAXN];
static unsigned char isA[GMAXN];
static uint64_t RB0[GMAXN * GMAXW], RB1[GMAXN * GMAXW];
static int defA[GMAXN], defB[GMAXN], nDA, nDB;

static int sN = 0, sNE = 0;
static int sEA[GMAXE], sEB[GMAXE];
static unsigned char sisA[GMAXN];

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

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Sum over vertices v of (number of vertices NOT within distance DIAM of v). */
static long long eval_cost(void) {
    int W = (N + 63) / 64;
    uint64_t *cur = RB0, *nxt = RB1;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++)
        cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int lv = 0; lv < DIAM; lv++) {
        memcpy(nxt, cur, sizeof(uint64_t) * (size_t)N * (size_t)W);
        for (int e = 0; e < NE; e++) {
            uint64_t *na = nxt + (size_t)eA[e] * W, *nb = nxt + (size_t)eB[e] * W;
            const uint64_t *ca = cur + (size_t)eA[e] * W, *cb = cur + (size_t)eB[e] * W;
            for (int w = 0; w < W; w++) {
                na[w] |= cb[w];
                nb[w] |= ca[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long cost = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[(size_t)v * W + w]);
        cost += N - c;
    }
    return cost;
}

static void add_edge(int a, int b) {
    eA[NE] = a;
    eB[NE] = b;
    NE++;
    adjm[a][b] = 1;
    deg[a]++;
    deg[b]++;
}

static void pop_edge(void) {
    NE--;
    int a = eA[NE], b = eB[NE];
    adjm[a][b] = 0;
    deg[a]--;
    deg[b]--;
}

/* Move edge e from its current B endpoint to nb (nb must not be adjacent to its A endpoint). */
static void retarget(int e, int nb) {
    int a = eA[e], ob = eB[e];
    adjm[a][ob] = 0;
    deg[ob]--;
    adjm[a][nb] = 1;
    deg[nb]++;
    eB[e] = nb;
}

static void build_def(void) {
    nDA = nDB = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < DEG) {
            if (isA[v]) defA[nDA++] = v;
            else defB[nDB++] = v;
        }
    }
}

static int accept(long long c2, long long c, double T) {
    if (c2 <= c) return 1;
    return rnd_unit() < exp(-(double)(c2 - c) / T);
}

static void try_swap(long long *cost, double T) {
    if (NE < 2) return;
    int e1 = rnd_int(NE), e2 = rnd_int(NE);
    if (e1 == e2) return;
    int a1 = eA[e1], b1 = eB[e1], a2 = eA[e2], b2 = eB[e2];
    if (a1 == a2 || b1 == b2 || adjm[a1][b2] || adjm[a2][b1]) return;
    retarget(e1, b2);
    retarget(e2, b1);
    long long c2 = eval_cost();
    if (accept(c2, *cost, T)) { *cost = c2; return; }
    retarget(e2, b2);
    retarget(e1, b1);
}

static void try_rewire(long long *cost, double T) {
    if (NE < 1 || nDB < 1) return;
    int e = rnd_int(NE);
    int nb = defB[rnd_int(nDB)];
    int a = eA[e], ob = eB[e];
    if (nb == ob || adjm[a][nb]) return;
    retarget(e, nb);
    long long c2 = eval_cost();
    if (accept(c2, *cost, T)) { *cost = c2; return; }
    retarget(e, ob);
}

static void try_add(long long *cost, double T) {
    if (nDA < 1 || nDB < 1 || NE >= GMAXE) return;
    int a = defA[rnd_int(nDA)], b = defB[rnd_int(nDB)];
    if (adjm[a][b]) return;
    add_edge(a, b);
    long long c2 = eval_cost();
    if (accept(c2, *cost, T)) { *cost = c2; return; }
    pop_edge();
}

static void save_snapshot(void) {
    sN = N;
    sNE = NE;
    memcpy(sEA, eA, sizeof(int) * (size_t)NE);
    memcpy(sEB, eB, sizeof(int) * (size_t)NE);
    memcpy(sisA, isA, (size_t)N);
}

static void load_snapshot(void) {
    N = sN;
    NE = 0;
    memset(adjm, 0, sizeof adjm);
    memset(deg, 0, sizeof deg);
    for (int i = 0; i < sNE; i++) add_edge(sEA[i], sEB[i]);
    memcpy(isA, sisA, (size_t)N);
}

/* Append one new A vertex and one new B vertex (both isolated). */
static int grow(void) {
    if (N + 2 > GMAXN) return 0;
    isA[N] = 1;
    deg[N] = 0;
    isA[N + 1] = 0;
    deg[N + 1] = 0;
    N += 2;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed time_limit nA < graph\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int nA = atoi(argv[5]);
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int n, m;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    if (DEG < 1 || DEG > 16 || DIAM < 1 || n < 0 || n > GMAXN - 2 ||
        m < 0 || m > GMAXE || nA < 0 || nA > n) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    NE = 0;
    memset(adjm, 0, sizeof adjm);
    memset(deg, 0, sizeof deg);
    for (int v = 0; v < N; v++) isA[v] = (unsigned char)(v < nA);
    int ok = 1;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= N || v >= N) { ok = 0; continue; }
        int a, b;
        if (u < nA && v >= nA) { a = u; b = v; }
        else if (v < nA && u >= nA) { a = v; b = u; }
        else { ok = 0; continue; }
        if (adjm[a][b] || deg[a] >= DEG || deg[b] >= DEG) { ok = 0; continue; }
        add_edge(a, b);
    }
    if (!ok) { printf("0 0\n"); return 0; }

    long long cost = eval_cost();
    int have = 0;
    if (cost == 0) {
        save_snapshot();
        have = 1;
    }
    CYC = DEADLINE / 4.0;
    if (CYC < 1.0) CYC = 1.0;
    double cyc_start = elapsed();

    while (elapsed() < DEADLINE) {
        if (cost == 0) {
            save_snapshot();
            have = 1;
            if (!grow()) break;
            cost = eval_cost();
            cyc_start = elapsed();
            continue;
        }
        if (elapsed() - cyc_start > CYC) {
            if (have) {
                load_snapshot();
                if (!grow()) break;
            }
            cost = eval_cost();
            cyc_start = elapsed();
            continue;
        }
        double frac = (elapsed() - cyc_start) / CYC;
        if (frac > 1.0) frac = 1.0;
        double Tt = T_HI * pow(T_LO / T_HI, frac);
        build_def();
        double u = rnd_unit();
        if (u < 0.4) try_swap(&cost, Tt);
        else if (u < 0.85) try_rewire(&cost, Tt);
        else try_add(&cost, Tt);
    }

    if (!have) {
        printf("0 0\n");
    } else {
        printf("%d %d\n", sN, sNE);
        for (int i = 0; i < sNE; i++) printf("%d %d\n", sEA[i], sEB[i]);
    }
    return 0;
}
"""


# Stage 1: voltage-lift annealer over semidirect products (unchanged from the parent).
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
# Driver: baselines, then lift search (stage 1), then unstructured grow (stage 2).
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    def left():
        return 0.92 * time_limit - (time.monotonic() - start) - 1.5

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

    total = left()
    if total < 2.0:
        return best

    # Stage 1: structured lift search for a large start graph.
    t1 = 0.5 * total
    try:
        out = lib.run_c(C_LIFT, [d, D, seed, f"{t1:.2f}", best_n], timeout=t1 + 5.0)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except Exception:
        pass

    # Stage 2: unstructured add-two-vertices-and-repair search from the best valid graph.
    # Every baseline and lift is bipartite with side A = first half of the labels.
    t2 = left()
    if t2 >= 2.0 and 4 <= best_n <= 1390:
        try:
            nA = best_n // 2
            out = lib.run_c(C_GROW, [d, D, seed, f"{t2:.2f}", nA],
                            stdin_graph=best, timeout=t2 + 5.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
