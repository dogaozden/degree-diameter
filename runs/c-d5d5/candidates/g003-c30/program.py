"""Bi-Cayley voltage lifts, then repair-based growth with a bitset diameter cost.

Two phases inside one C run:
1. Phase 1 (40% of the C budget): simulated annealing over voltage lifts of layered
   base graphs with metacyclic groups Z_m x| Z_k2, as in the parent.
2. Phase 2 (the rest): start from the best lift (or K_{d,d}) and grow the bipartite
   graph one vertex pair at a time. The state is a simple bipartite graph with max
   degree d. Moves are double-edge swaps, endpoint rewires and edge add/remove. Cost is
   the number of ordered vertex pairs at distance > D, computed exactly with bitset
   BFS. Each step is a full evaluation, about tens of microseconds for n near 350.
   Whenever cost reaches 0, the graph is recorded and one more pair of vertices is
   added.
"""
import itertools
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 8
#define MAXK2 64
#define MAXD 32
#define MAXT 1024
#define MAXN (2 * MAXT)
#define MAXW (MAXN / 64)
#define CHUNK 30000

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu_now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* ---------------- metacyclic group Z_m x| Z_k2, element (a,b) coded as a*k2+b ---------------- */

typedef struct {
    int G, m, k2;
    long long r;
    long long pw[MAXK2];
} Group;

static long long lmod(long long a, long long m) {
    a %= m;
    return a < 0 ? a + m : a;
}

static long long gcdll(long long a, long long b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b = lmod(b, m);
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static void make_group(Group *g, int G, int k2, int m, long long r) {
    g->G = G;
    g->m = m;
    g->k2 = k2;
    g->r = r;
    g->pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) g->pw[b] = (g->pw[b - 1] * r) % m;
}

/* (a,b)*(c,e) = (a + r^b c, b + e) */
static int gmul(const Group *g, int x, int y) {
    int a = x / g->k2, b = x % g->k2, c = y / g->k2, e = y % g->k2;
    long long na = lmod((long long)a + g->pw[b] * (long long)c, g->m);
    int nb = (b + e) % g->k2;
    return (int)(na * g->k2 + nb);
}

/* (a,b)^-1 = (-r^(-b) a, -b) */
static int ginv(const Group *g, int x) {
    int a = x / g->k2, b = x % g->k2;
    int nb = (g->k2 - b) % g->k2;
    long long na = lmod(-g->pw[nb] * (long long)a, g->m);
    return (int)(na * g->k2 + nb);
}

static void random_group(Group *g, int G) {
    int cand[256];
    int nc = 0;
    for (int k2 = 1; k2 <= MAXK2 && k2 <= G; k2++)
        if (G % k2 == 0 && G / k2 >= 2) cand[nc++] = k2;
    int k2 = cand[rndint(nc)];
    int m = G / k2;
    long long r = 1 % m;
    if (k2 > 1) {
        for (int t = 0; t < 300; t++) {
            long long c = 1 + rndint(m - 1);
            if (gcdll(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                r = c;
                break;
            }
        }
    }
    make_group(g, G, k2, m, r);
}

/* ---------------- layered bi-Cayley lift (phase 1) ---------------- */

typedef struct {
    int k, d, G, N, stamp;
    Group grp;
    int *dj, *ds, *dsi;
    int *adj, *vis, *queue;
} Lift;

static void lift_alloc(Lift *L, int k, int d, int G) {
    L->k = k;
    L->d = d;
    L->G = G;
    L->N = 2 * k * G;
    L->stamp = 0;
    L->dj = malloc(sizeof(int) * (size_t)(k * d));
    L->ds = malloc(sizeof(int) * (size_t)(k * d));
    L->dsi = malloc(sizeof(int) * (size_t)(k * d));
    L->adj = malloc(sizeof(int) * (size_t)L->N * (size_t)d);
    L->vis = calloc((size_t)L->N, sizeof(int));
    L->queue = malloc(sizeof(int) * (size_t)L->N);
}

static void lift_free(Lift *L) {
    free(L->dj);
    free(L->ds);
    free(L->dsi);
    free(L->adj);
    free(L->vis);
    free(L->queue);
}

static void random_init(Lift *L) {
    int k = L->k, d = L->d;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < k; i++) {
            int idx = l * k + i;
            L->dj[idx] = perm[i];
            L->ds[idx] = rndint(L->G);
            L->dsi[idx] = ginv(&L->grp, L->ds[idx]);
        }
    }
}

static void build_adj(Lift *L) {
    int k = L->k, d = L->d, G = L->G;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) {
            int idx = l * k + i;
            int j = L->dj[idx], s = L->ds[idx], si = L->dsi[idx];
            for (int x = 0; x < G; x++) {
                int a = i * G + x;
                L->adj[(size_t)a * d + l] = (k + j) * G + gmul(&L->grp, x, s);
                int b = (k + j) * G + x;
                L->adj[(size_t)b * d + l] = i * G + gmul(&L->grp, x, si);
            }
        }
    }
}

static int count_dups(const Lift *L) {
    int c = 0;
    for (int i = 0; i < L->k; i++)
        for (int l = 0; l < L->d; l++)
            for (int l2 = l + 1; l2 < L->d; l2++) {
                int a = l * L->k + i, b = l2 * L->k + i;
                if (L->dj[a] == L->dj[b] && L->ds[a] == L->ds[b]) c++;
            }
    return c;
}

static long long eval_cost(Lift *L, int D) {
    int k = L->k, d = L->d, G = L->G, N = L->N;
    long long cost = (long long)count_dups(L) * (long long)N;
    build_adj(L);
    for (int rep = 0; rep < 2 * k; rep++) {
        int src = rep * G;
        if (++L->stamp >= 0x7ffffff0) {
            memset(L->vis, 0, sizeof(int) * (size_t)N);
            L->stamp = 1;
        }
        int head = 0, tail = 0;
        L->queue[tail++] = src;
        L->vis[src] = L->stamp;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int u = L->queue[head++];
                const int *au = L->adj + (size_t)u * d;
                for (int t = 0; t < d; t++) {
                    int v = au[t];
                    if (L->vis[v] != L->stamp) {
                        L->vis[v] = L->stamp;
                        L->queue[tail++] = v;
                    }
                }
            }
        }
        cost += N - tail;
    }
    return cost;
}

static int anneal(Lift *L, int D, long long iters, double T0, double T1, double tend) {
    int k = L->k, d = L->d, G = L->G;
    long long cost = eval_cost(L, D);
    if (cost == 0) return 1;
    for (long long it = 0; it < iters; it++) {
        if ((it & 127) == 0 && cpu_now() > tend) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        long long c2;
        if (k >= 2 && rnd01() < 0.4) {
            int l = rndint(d);
            int i1 = rndint(k);
            int i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int a = l * k + i1, b = l * k + i2;
            int t = L->dj[a];
            L->dj[a] = L->dj[b];
            L->dj[b] = t;
            c2 = eval_cost(L, D);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                t = L->dj[a];
                L->dj[a] = L->dj[b];
                L->dj[b] = t;
            }
        } else {
            int idx = rndint(d * k);
            int os = L->ds[idx], osi = L->dsi[idx];
            int ns = rndint(G);
            if (ns == os) continue;
            L->ds[idx] = ns;
            L->dsi[idx] = ginv(&L->grp, ns);
            c2 = eval_cost(L, D);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                L->ds[idx] = os;
                L->dsi[idx] = osi;
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* Phase 1: ladder of lift searches. Returns best total order; edges in *oe (A index first). */
static int phase1(int d, int D, double tend, int **oe, int *om) {
    int best_n = 0, best_m = 0;
    int *best_e = NULL;
    while (cpu_now() < tend) {
        int k = 1 + rndint(4);
        int Gmin = best_n / (2 * k) + 1;
        if (Gmin < 2) Gmin = 2;
        int spread = Gmin / 12 + 2;
        int G = Gmin + rndint(spread);

        Lift L;
        lift_alloc(&L, k, d, G);
        random_group(&L.grp, G);
        random_init(&L);
        int ok = anneal(&L, D, 100000, 3.0, 0.15, tend);
        if (ok) {
            build_adj(&L);
            int cnt = k * G * d;
            int *e = malloc(sizeof(int) * 2 * (size_t)cnt);
            int m = 0;
            for (int i = 0; i < k; i++)
                for (int x = 0; x < G; x++)
                    for (int l = 0; l < d; l++) {
                        int a = i * G + x;
                        e[2 * m] = a;
                        e[2 * m + 1] = L.adj[(size_t)a * d + l];
                        m++;
                    }
            if (L.N > best_n) {
                free(best_e);
                best_e = e;
                best_n = L.N;
                best_m = m;
            } else {
                free(e);
            }
        }
        lift_free(&L);
    }
    *oe = best_e;
    *om = best_m;
    return best_n;
}

/* ---------------- phase 2: bipartite state with repair-based growth ---------------- */
/* A vertices are indices 0..T-1, B vertices are 0..T-1 on the other side.
   Global ids: A a -> a, B b -> T + b. */

typedef struct {
    int T, d;
    int degA[MAXT], degB[MAXT];
    int nbA[MAXT][MAXD];
    int nbB[MAXT][MAXD];
} State;

static State GS;
static uint64_t curR[MAXN * MAXW];
static uint64_t nxtR[MAXN * MAXW];
static int adjid[MAXN * MAXD];
static int dgid[MAXN];

static int has_edge(const State *S, int a, int b) {
    for (int s = 0; s < S->degA[a]; s++)
        if (S->nbA[a][s] == b) return 1;
    return 0;
}

static void op_add(State *S, int a, int b) {
    S->nbA[a][S->degA[a]++] = b;
    S->nbB[b][S->degB[b]++] = a;
}

static void op_remove(State *S, int a, int b) {
    for (int s = 0; s < S->degA[a]; s++)
        if (S->nbA[a][s] == b) {
            S->nbA[a][s] = S->nbA[a][S->degA[a] - 1];
            S->degA[a]--;
            break;
        }
    for (int s = 0; s < S->degB[b]; s++)
        if (S->nbB[b][s] == a) {
            S->nbB[b][s] = S->nbB[b][S->degB[b] - 1];
            S->degB[b]--;
            break;
        }
}

/* Cost = number of ordered pairs (v,w) with dist > D (unreached within D rounds). 0 means valid. */
static long long eval_state(const State *S, int D) {
    int T = S->T, d = S->d, N = 2 * T, W = (N + 63) >> 6;
    for (int a = 0; a < T; a++) {
        dgid[a] = S->degA[a];
        for (int s = 0; s < S->degA[a]; s++) adjid[a * d + s] = T + S->nbA[a][s];
    }
    for (int b = 0; b < T; b++) {
        int v = T + b;
        dgid[v] = S->degB[b];
        for (int s = 0; s < S->degB[b]; s++) adjid[v * d + s] = S->nbB[b][s];
    }
    memset(curR, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++) curR[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *nx = nxtR + (size_t)v * W;
            const uint64_t *cv = curR + (size_t)v * W;
            for (int w = 0; w < W; w++) nx[w] = cv[w];
            for (int s = 0; s < dgid[v]; s++) {
                const uint64_t *cu = curR + (size_t)adjid[v * d + s] * W;
                for (int w = 0; w < W; w++) nx[w] |= cu[w];
            }
        }
        memcpy(curR, nxtR, sizeof(uint64_t) * (size_t)N * (size_t)W);
    }
    long long cost = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(curR[(size_t)v * W + w]);
        cost += N - c;
    }
    return cost;
}

typedef struct { int type, a, b; } Op;   /* type 0 = add edge, 1 = remove edge */

static void apply_op(State *S, Op *lg, int *nl, int type, int a, int b) {
    if (type == 0) op_add(S, a, b);
    else op_remove(S, a, b);
    lg[*nl].type = type;
    lg[*nl].a = a;
    lg[*nl].b = b;
    (*nl)++;
}

static void undo_ops(State *S, const Op *lg, int nl) {
    for (int i = nl - 1; i >= 0; i--) {
        if (lg[i].type == 0) op_remove(S, lg[i].a, lg[i].b);
        else op_add(S, lg[i].a, lg[i].b);
    }
}

static int pick_edge(const State *S, int *pa, int *pb) {
    int T = S->T, st = rndint(T);
    for (int t = 0; t < T; t++) {
        int a = (st + t) % T;
        if (S->degA[a] > 0) {
            *pa = a;
            *pb = S->nbA[a][rndint(S->degA[a])];
            return 1;
        }
    }
    return 0;
}

static int pick_free_a(const State *S, int *pa) {
    int T = S->T, st = rndint(T);
    for (int t = 0; t < T; t++) {
        int a = (st + t) % T;
        if (S->degA[a] < S->d) {
            *pa = a;
            return 1;
        }
    }
    return 0;
}

static int pick_free_b(const State *S, int *pb) {
    int T = S->T, st = rndint(T);
    for (int t = 0; t < T; t++) {
        int b = (st + t) % T;
        if (S->degB[b] < S->d) {
            *pb = b;
            return 1;
        }
    }
    return 0;
}

/* Propose a move; returns the number of logged ops, 0 if the move was rejected as invalid. */
static int propose(State *S, Op *lg) {
    int nl = 0, a1 = 0, b1 = 0, a2 = 0, b2 = 0;
    double u = rnd01();
    if (u < 0.35) {
        /* double-edge swap: keeps all degrees */
        if (!pick_edge(S, &a1, &b1) || !pick_edge(S, &a2, &b2)) return 0;
        if (a1 == a2 || b1 == b2) return 0;
        if (has_edge(S, a1, b2) || has_edge(S, a2, b1)) return 0;
        apply_op(S, lg, &nl, 1, a1, b1);
        apply_op(S, lg, &nl, 1, a2, b2);
        apply_op(S, lg, &nl, 0, a1, b2);
        apply_op(S, lg, &nl, 0, a2, b1);
        return nl;
    }
    if (u < 0.55) {
        /* move the B endpoint of an edge to a free B vertex */
        if (!pick_edge(S, &a1, &b1) || !pick_free_b(S, &b2)) return 0;
        if (b2 == b1 || has_edge(S, a1, b2)) return 0;
        apply_op(S, lg, &nl, 1, a1, b1);
        apply_op(S, lg, &nl, 0, a1, b2);
        return nl;
    }
    if (u < 0.75) {
        /* move the A endpoint of an edge to a free A vertex */
        if (!pick_edge(S, &a1, &b1) || !pick_free_a(S, &a2)) return 0;
        if (a2 == a1 || has_edge(S, a2, b1)) return 0;
        apply_op(S, lg, &nl, 1, a1, b1);
        apply_op(S, lg, &nl, 0, a2, b1);
        return nl;
    }
    if (u < 0.97) {
        /* add an edge between two free vertices */
        if (!pick_free_a(S, &a1) || !pick_free_b(S, &b1)) return 0;
        if (has_edge(S, a1, b1)) return 0;
        apply_op(S, lg, &nl, 0, a1, b1);
        return nl;
    }
    /* remove a random edge */
    if (!pick_edge(S, &a1, &b1)) return 0;
    apply_op(S, lg, &nl, 1, a1, b1);
    return nl;
}

static int anneal_state(State *S, int D, long long iters, double T0, double T1,
                        double tend, long long *costp) {
    long long cost = *costp;
    Op lg[4];
    for (long long it = 0; it < iters && cost != 0; it++) {
        if ((it & 127) == 0 && cpu_now() > tend) break;
        double temp = T0 * pow(T1 / T0, (double)it / (double)iters);
        int nl = propose(S, lg);
        if (nl == 0) continue;
        long long c2 = eval_state(S, D);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
        } else {
            undo_ops(S, lg, nl);
        }
    }
    *costp = cost;
    return cost == 0;
}

static void save_state(const State *S, int **pe, int *pm) {
    int T = S->T, cnt = 0;
    for (int a = 0; a < T; a++) cnt += S->degA[a];
    int *e = malloc(sizeof(int) * 2 * (size_t)(cnt + 1));
    int m = 0;
    for (int a = 0; a < T; a++)
        for (int s = 0; s < S->degA[a]; s++) {
            e[2 * m] = a;
            e[2 * m + 1] = T + S->nbA[a][s];
            m++;
        }
    free(*pe);
    *pe = e;
    *pm = m;
}

static void reset_kdd(State *S, int d) {
    memset(S->degA, 0, sizeof(S->degA));
    memset(S->degB, 0, sizeof(S->degB));
    S->d = d;
    S->T = d;
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) op_add(S, a, b);
}

static void phase2(int d, int D, double tend, int have_lift, int T0,
                   const int *le, int lm, int *best_n, int **best_e, int *best_m) {
    State *S = &GS;
    *best_n = 0;
    *best_e = NULL;
    *best_m = 0;
    S->d = d;
    int ok = 0;
    if (have_lift) {
        memset(S->degA, 0, sizeof(S->degA));
        memset(S->degB, 0, sizeof(S->degB));
        S->T = T0;
        for (int i = 0; i < lm; i++) {
            int a = le[2 * i], b = le[2 * i + 1] - T0;
            if (a < 0 || a >= T0 || b < 0 || b >= T0) continue;
            if (S->degA[a] < d && S->degB[b] < d && !has_edge(S, a, b)) op_add(S, a, b);
        }
        ok = (eval_state(S, D) == 0);
    }
    if (!ok) reset_kdd(S, d);

    long long cost = eval_state(S, D);
    double moore = 0.0, p = 1.0;
    for (int i = 0; i < D; i++) {
        moore += p;
        p *= (double)(d - 1);
    }
    moore *= 2.0;

    for (;;) {
        if (cost == 0) {
            save_state(S, best_e, best_m);
            *best_n = 2 * S->T;
            if (S->T + 1 > MAXT - 1 || 2.0 * (S->T + 1) > moore + 0.5) break;
            int nt = S->T + 1;
            S->T = nt;
            S->degA[nt - 1] = 0;
            S->degB[nt - 1] = 0;
            cost = eval_state(S, D);
            continue;
        }
        if (cpu_now() >= tend) break;
        double temps[3] = {1.5, 4.0, 10.0};
        anneal_state(S, D, CHUNK, temps[rndint(3)], 0.3, tend, &cost);
    }
}

static void print_graph(int n, int m, const int *e) {
    printf("%d %d\n", n, m);
    for (int t = 0; t < m; t++) printf("%d %d\n", e[2 * t], e[2 * t + 1]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed budget\n");
        return 1;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 20; w++) rnd64();
    int ch;
    while ((ch = getchar()) != EOF) {
    }

    if (d < 2 || D < 2) {
        printf("0 0\n");
        return 0;
    }

    double start = cpu_now();
    int *e1 = NULL;
    int m1 = 0;
    int n1 = phase1(d, D, start + 0.4 * budget, &e1, &m1);
    int have_lift = (n1 > 0);

    int *be = NULL;
    int bm = 0, bn = 0;
    if (d <= MAXD && (!have_lift || n1 / 2 < MAXT - 2)) {
        phase2(d, D, start + budget, have_lift, n1 / 2, e1, m1, &bn, &be, &bm);
    }

    if (be != NULL && bn >= n1) print_graph(bn, bm, be);
    else if (have_lift) print_graph(n1, m1, e1);
    else printf("0 0\n");
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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

    # Already at the Moore bound: nothing to search for (e.g. d = 3, D = 3).
    if best_n >= lib.moore_bound(d, D):
        return best

    if D >= 4 and time.monotonic() - t0 < 0.1 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search in C: lift phase, then repair-based growth. Leave margin for compile and glue.
    budget = 0.8 * time_limit - (time.monotonic() - t0) - 1.5
    if d >= 2 and budget > 0.5:
        try:
            timeout = max(1.0, 0.93 * time_limit - (time.monotonic() - t0))
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                             stdin_graph=None, timeout=timeout)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
