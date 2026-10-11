"""Combined program: semidirect voltage-lift annealing with an elite pool (iterated local
search), followed by bad-pair-annealed growth by two vertices on the best valid graph.

Pipeline (C engine):
  1. Read an optional valid start graph from stdin.
  2. Lift phase: voltage lifts of Z_m x| Z_k2 over K + K base vertices per side, annealed on
     the number of (block representative, vertex) pairs beyond distance D. Left multiplication
     is an automorphism, so 2K BFS runs from block representatives decide the diameter.
     Elite configurations are kept in a pool and re-annealed (ILS) at lower temperature.
  3. Grow phase: insert one vertex per side into the best graph, rewire to restore degree,
     then anneal degree-preserving swaps until all bad pairs are gone. Each success adds 2 vertices.
  Every accepted graph is re-validated (simple, bipartite, degree <= d, diameter <= D).

Python: known constructions (projective plane / Araujo-Pardo-Lopez) for D = 3, K_{d,d}
fallback, and final validation with lib.is_valid.
"""
import time

import lib

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define BIGC 1000000000LL
#define ITERS 6000
#define ILS_ITERS 2500
#define POOLMAX 48
#define POOLP 0.6
#define MAXK 3
#define MAXDEG 64

/* ------------------------------------------------------------ utilities */

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int DEG, DIAM;
static double END_T, LIFT_T;

/* ------------------------------------------------------------ general graph */

typedef struct {
    int n, cap;
    int *deg, *adj;          /* adj[v*cap + i] */
    unsigned char *side;     /* 0 = A, 1 = B */
} Gr;

static Gr best; /* best.n == 0 means no graph yet */

static void gr_alloc(Gr *g, int n, int cap) {
    g->n = n;
    g->cap = cap;
    g->deg = calloc((size_t)n + 1, sizeof(int));
    g->adj = malloc(sizeof(int) * ((size_t)n * cap + 1));
    g->side = calloc((size_t)n + 1, 1);
}

static void gr_free(Gr *g) {
    free(g->deg);
    free(g->adj);
    free(g->side);
    g->deg = NULL;
    g->adj = NULL;
    g->side = NULL;
    g->n = 0;
}

static int gr_has(const Gr *g, int u, int v) {
    const int *a = g->adj + (size_t)u * g->cap;
    for (int i = 0; i < g->deg[u]; i++)
        if (a[i] == v) return 1;
    return 0;
}

static int gr_add(Gr *g, int u, int v) {
    if (g->deg[u] >= g->cap || g->deg[v] >= g->cap) return 0;
    g->adj[(size_t)u * g->cap + g->deg[u]++] = v;
    g->adj[(size_t)v * g->cap + g->deg[v]++] = u;
    return 1;
}

static void gr_del_half(Gr *g, int u, int v) {
    int *a = g->adj + (size_t)u * g->cap;
    for (int i = 0; i < g->deg[u]; i++)
        if (a[i] == v) {
            a[i] = a[--g->deg[u]];
            return;
        }
}

static void gr_del(Gr *g, int u, int v) {
    gr_del_half(g, u, v);
    gr_del_half(g, v, u);
}

static long moore_bound(void) {
    if (DIAM <= 0 || DEG <= 0) return 1;
    if (DEG == 1) return 2;
    if (DEG == 2) return 2L * DIAM;
    long s = 0, p = 1;
    for (int i = 0; i < DIAM; i++) {
        s += p;
        p *= (DEG - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* Number of unordered pairs at distance > DIAM; fills badv[v] (may be NULL). */
static long gr_bad(const Gr *g, int *badv) {
    int n = g->n;
    if (n <= 0) return 0;
    int W = (n + 63) / 64;
    size_t sz = (size_t)n * W;
    uint64_t *cur = calloc(sz, sizeof(uint64_t));
    uint64_t *nxt = calloc(sz, sizeof(uint64_t));
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[(size_t)v * g->cap + i];
                const uint64_t *s = cur + (size_t)u * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        if (badv) badv[v] = n - c;
        total += n - c;
    }
    free(cur);
    free(nxt);
    return total / 2;
}

/* Full validity: degree <= DEG, simple, bipartite by side labels, diameter <= DIAM. */
static int gr_valid(const Gr *g) {
    int n = g->n;
    if (n <= 0) return 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] > DEG || g->deg[v] > g->cap) return 0;
        const int *a = g->adj + (size_t)v * g->cap;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = a[i];
            if (u < 0 || u >= n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (a[j] == u) return 0;
        }
    }
    return gr_bad(g, NULL) == 0;
}

static void build_complete(Gr *g) {
    gr_alloc(g, 2 * DEG, DEG);
    for (int v = 0; v < 2 * DEG; v++) g->side[v] = (unsigned char)(v >= DEG);
    for (int a = 0; a < DEG; a++)
        for (int b = 0; b < DEG; b++) gr_add(g, a, DEG + b);
}

static void print_gr(const Gr *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[(size_t)u * g->cap + i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++) {
            int v = g->adj[(size_t)u * g->cap + i];
            if (u < v) printf("%d %d\n", u, v);
        }
}

/* ------------------------------------------------------------ semidirect lifts */

/* Z_M x|_R Z_K2; element a*K2 + b, (a,b)(c,e) = (a + R^b c, b + e). G = M*K2. */
static int K, K2, M, G, R, T, MAXT;
static int *Rpow;
static int *dI, *dJ, *dS, *bestJ, *bestS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int curstamp;

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
    curstamp = 0;
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
}

static void free_config(void) {
    free(dI); free(dJ); free(dS); free(bestJ); free(bestS);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx); free(Rpow);
    dI = dJ = dS = bestJ = bestS = perm = adj = cnt = stamp = fr = nx = NULL;
    Rpow = NULL;
}

static void setup_group(int k, int c2, int m, int r) {
    K = k;
    K2 = c2;
    M = m;
    R = r;
    G = m * c2;
    alloc_config();
    for (int t = 0; t < T; t++) dI[t] = t % K;
}

/* Cost = sum over the 2K block representatives of vertices beyond distance DIAM.
 * BIGC marks configurations with duplicate darts (multi-edges). */
static long long eval_cost(void) {
    int N = 2 * K * G;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2])
                return BIGC;
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
            int *tmp = f;
            f = h;
            h = tmp;
            fsz = nsz;
        }
        total += N - count;
    }
    return total;
}

static void random_init(void) {
    int p[MAXK];
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
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && now() > LIFT_T) break;
        double temp = tscale * (3.0 * (1.0 - (double)it / iters) + 0.05);
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long long c2 = eval_cost();
            if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
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
            if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
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

/* Build the lift graph of the current configuration. */
static void emit_current(Gr *out) {
    int N = 2 * K * G;
    gr_alloc(out, N, DEG);
    for (int v = K * G; v < N; v++) out->side[v] = 1;
    for (int t = 0; t < T; t++)
        for (int g = 0; g < G; g++) {
            int a = dI[t] * G + g;
            int b = (K + dJ[t]) * G + perm[(size_t)t * G + g];
            gr_add(out, a, b);
        }
}

/* A zero-cost run is a valid lift: load it and keep it if it beats the best graph. */
static void finish_run(long long bc) {
    if (bc != 0) return;
    memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
    memcpy(dS, bestS, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) build_perm(t);
    if (2LL * K * G > (long long)best.n) {
        Gr c;
        emit_current(&c);
        if (gr_valid(&c)) {
            gr_free(&best);
            best = c;
        } else {
            gr_free(&c);
        }
    }
}

/* ------------------------------------------------------------ elite pool */

typedef struct {
    int K, K2, M, R;
    long long cost;
    int *J, *S;
} Cfg;

static Cfg pool[POOLMAX];
static int npool = 0;

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
    c->K = K;
    c->K2 = K2;
    c->M = M;
    c->R = R;
    c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)T);
    memcpy(c->S, S, sizeof(int) * (size_t)T);
}

/* Pick an eligible entry (group order must still beat the best graph), best of 3 samples. */
static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++) {
        long long nn = 2LL * pool[i].K * pool[i].K2 * pool[i].M;
        if (nn > (long long)best.n) cand[nc++] = i;
    }
    if (nc == 0) return -1;
    int bi = cand[rnd_int(nc)];
    for (int s = 0; s < 2; s++) {
        int c = cand[rnd_int(nc)];
        if (pool[c].cost < pool[bi].cost) bi = c;
    }
    return bi;
}

/* ------------------------------------------------------------ lift phase */

static void lift_search(double until) {
    static const int kc[5] = {1, 1, 2, 2, 3};
    LIFT_T = until;
    while (now() < until) {
        int pi = -1;
        if (rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            /* Iterated local search: perturb an elite configuration and re-anneal. */
            int kk = pool[pi].K, kk2 = pool[pi].K2, mm = pool[pi].M, rr = pool[pi].R;
            setup_group(kk, kk2, mm, rr);
            memcpy(dJ, pool[pi].J, sizeof(int) * (size_t)T);
            memcpy(dS, pool[pi].S, sizeof(int) * (size_t)T);
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

        /* Fresh random lift with group order just above the current best. */
        int k = kc[rnd_int(5)];
        int gmin = best.n / (2 * k) + 1;
        int spread = gmin / 6 + 2;
        int g = gmin + rnd_int(spread);
        if (g < 2) g = 2;
        int opts[12], no = 0;
        for (int c = 1; c <= 12; c++)
            if (g % c == 0 && g / c >= 2) opts[no++] = c;
        if (no == 0) {
            opts[no++] = 1;
        }
        int c2 = opts[rnd_int(no)];
        int m = g / c2, r = 1;
        if (c2 > 1) {
            int found = 0;
            for (int tr = 0; tr < 200 && !found; tr++) {
                int cand = 1 + rnd_int(m - 1);
                if (gcd_i(cand, m) == 1 && powmod_l(cand, c2, m) == 1 % m) {
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
}

/* ------------------------------------------------------------ grow phase */

/* Add two vertices (x on side A, y on side B) to a copy of best, rewire to restore degree,
 * then anneal degree-preserving swaps until no bad pairs remain. On success best grows by 2. */
static int grow_once(double until) {
    int n = best.n;
    if (n <= 0 || (long)(n + 2) > moore_bound()) return 0;
    int N = n + 2;
    Gr w;
    gr_alloc(&w, N, DEG);
    for (int v = 0; v < n; v++) {
        w.deg[v] = best.deg[v];
        w.side[v] = best.side[v];
        memcpy(w.adj + (size_t)v * DEG, best.adj + (size_t)v * best.cap, sizeof(int) * best.deg[v]);
    }
    int x = n, y = n + 1;
    w.side[x] = 0;
    w.side[y] = 1;
    gr_add(&w, x, y);

    int *used = calloc((size_t)N, sizeof(int));
    used[x] = 1;
    used[y] = 1;
    int k = 0;
    for (int tries = 0; k < DEG - 1 && tries < 100000; tries++) {
        int a = rnd_int(n);
        if (w.side[a] != 0 || used[a] || w.deg[a] == 0) continue;
        int b = w.adj[(size_t)a * DEG + rnd_int(w.deg[a])];
        if (b >= n || used[b]) continue;
        gr_del(&w, a, b);
        gr_add(&w, x, b);
        gr_add(&w, y, a);
        used[a] = 1;
        used[b] = 1;
        k++;
    }

    int *badv = malloc(sizeof(int) * (size_t)N);
    long bad = gr_bad(&w, badv);
    double Tm = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) break;
        int v = rnd_int(N);
        for (int tr = 0; tr < 30 && badv[v] == 0; tr++) v = rnd_int(N);
        if (w.deg[v] == 0) continue;
        int u = w.adj[(size_t)v * DEG + rnd_int(w.deg[v])];
        int s = rnd_int(N);
        if (s == v || w.side[s] != w.side[v] || w.deg[s] == 0) continue;
        int t = w.adj[(size_t)s * DEG + rnd_int(w.deg[s])];
        if (t == u || gr_has(&w, v, t) || gr_has(&w, s, u)) continue;
        gr_del(&w, v, u);
        gr_del(&w, s, t);
        gr_add(&w, v, t);
        gr_add(&w, s, u);
        long nb = gr_bad(&w, badv);
        if (nb <= bad || rnd_unit() < exp((double)(bad - nb) / Tm)) {
            bad = nb;
        } else {
            gr_del(&w, v, t);
            gr_del(&w, s, u);
            gr_add(&w, v, u);
            gr_add(&w, s, t);
        }
        Tm *= 0.9995;
        if (Tm < 0.05) Tm = 1.0;
    }

    int ok = (bad == 0) && gr_valid(&w);
    free(used);
    free(badv);
    if (ok) {
        gr_free(&best);
        best = w;
    } else {
        gr_free(&w);
    }
    return ok;
}

static void grow_phase(double until) {
    while (now() < until) {
        if (best.n <= 0 || (long)(best.n + 2) > moore_bound()) break;
        double left = until - now();
        double slice = left < 3.0 ? left : (left / 4 > 3.0 ? left / 4 : 3.0);
        grow_once(now() + slice);
    }
}

/* ------------------------------------------------------------ input */

static void read_start(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return;
    if (n <= 0 || m < 0) return;
    int *eu = malloc(sizeof(int) * ((size_t)m + 1));
    int *ev = malloc(sizeof(int) * ((size_t)m + 1));
    int ok = 1;
    for (int e = 0; e < m && ok; e++) {
        if (scanf("%d %d", &eu[e], &ev[e]) != 2) ok = 0;
        else if (eu[e] < 0 || ev[e] < 0 || eu[e] >= n || ev[e] >= n || eu[e] == ev[e]) ok = 0;
    }
    Gr g;
    gr_alloc(&g, n, DEG);
    for (int e = 0; e < m && ok; e++)
        if (!gr_add(&g, eu[e], ev[e])) ok = 0;

    int *col = malloc(sizeof(int) * (size_t)n);
    int *q = malloc(sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n && ok; s++) {
        if (col[s] >= 0) continue;
        int head = 0, tail = 0;
        col[s] = 0;
        q[tail++] = s;
        while (head < tail && ok) {
            int v = q[head++];
            for (int i = 0; i < g.deg[v]; i++) {
                int u = g.adj[(size_t)v * g.cap + i];
                if (col[u] < 0) {
                    col[u] = 1 - col[v];
                    q[tail++] = u;
                } else if (col[u] == col[v]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    if (ok)
        for (int v = 0; v < n; v++) g.side[v] = (unsigned char)col[v];
    if (ok && gr_valid(&g)) {
        gr_free(&best);
        best = g;
    } else {
        gr_free(&g);
    }
    free(col);
    free(q);
    free(eu);
    free(ev);
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    END_T = t0 + limit * 0.9;
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    MAXT = DEG * MAXK;
    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].S = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].cost = BIGC;
    }

    read_start();

    if (DIAM >= 2 && DEG >= 2) {
        double span = END_T - t0;
        double lift_end = t0 + span * (best.n > 0 ? 0.6 : 0.7);
        lift_search(lift_end);
        grow_phase(END_T);
    }

    if (best.n <= 0) build_complete(&best);
    if (!gr_valid(&best)) {
        gr_free(&best);
        build_complete(&best);
        if (!gr_valid(&best)) {
            printf("0 0\n");
            return 0;
        }
    }
    print_gr(&best);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: known constructions and fallback.
# ----------------------------------------------------------------------------

def _known_start(d, D):
    """Best construction Python builds directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    start = _known_start(d, D)
    if start is not None and not lib.is_valid(start[0], start[1], d, D):
        start = None
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}, valid for D >= 2
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget >= 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                             stdin_graph=start, timeout=budget + 8.0)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass   # keep the valid fallback

    return best
