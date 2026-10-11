"""Combined program: semidirect voltage-lift annealing with an elite pool (ILS), then
bad-pair-annealed growth by two vertices on the best valid graph. Lift and grow phases
alternate, so growth works on the newest best graph and lifts can then aim above it.

New in this version:
  * best-of-R rewiring: when a vertex pair is inserted, several random rewirings are tried
    and the one with the fewest bad pairs seeds the annealing.
  * slack filling: after a successful growth step, any remaining opposite-side pair of
    vertices with spare degree and no edge between them is joined (never hurts diameter).

C engine pipeline:
  1. Optional valid start graph on stdin (used only for D = 3 known constructions).
  2. Lift phase: voltage lifts of Z_m x| Z_k2 over K + K base vertices per side. Simulated
     annealing minimises the number of (block representative, vertex) pairs beyond distance D.
  3. Grow phase: insert one vertex per side, rewire (best of several tries), then anneal
     degree-preserving swaps until no bad pairs remain. Each success adds 2 vertices.
  4. Alternation between grow and lift phases; every kept graph is re-validated.

Python: known constructions (projective plane / Araujo-Pardo-Lopez for D = 3, generalized
quadrangle W(q) for D >= 4), K_{d,d} fallback, and final validation with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r"""
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define BIGC 1000000000LL
#define ITERS 6000
#define ILS_ITERS 3000
#define POOLMAX 48
#define POOLP 0.6
#define MAXK 3
#define MAXDEG 64
#define REWIRE_TRIES 8

/* ------------------------------------------------------------ utilities */

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE, LIFT_T;
static int DEG, DIAM, MAXT;

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

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

static int powmod_i(long long b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* ------------------------------------------------------------ general graph */

typedef struct {
    int n, cap;
    int *deg, *adj;       /* adj[v*cap + i] */
    unsigned char *side;  /* 0 = A, 1 = B */
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

static void gr_copy(Gr *dst, const Gr *src) {
    gr_alloc(dst, src->n, src->cap);
    memcpy(dst->deg, src->deg, sizeof(int) * ((size_t)src->n + 1));
    memcpy(dst->adj, src->adj, sizeof(int) * ((size_t)src->n * src->cap + 1));
    memcpy(dst->side, src->side, (size_t)src->n + 1);
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

/* Number of unordered pairs at distance > DIAM; fills badv[v] if non-NULL. */
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
static int K, K2, M, G, R, T;
static int *Rpow;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx, *bestJ, *bestS;
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
 * BIGC marks configurations with duplicate darts. */
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

/* Random kicks: voltage changes and within-layer target swaps (layers stay permutations). */
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
        if ((it & 63) == 0 && elapsed() > LIFT_T) break;
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

static void emit_current(Gr *out) {
    int N = 2 * K * G;
    gr_alloc(out, N, DEG);
    for (int v = K * G; v < N; v++) out->side[v] = 1;
    for (int t = 0; t < T; t++)
        for (int g = 0; g < G; g++)
            gr_add(out, dI[t] * G + g, (K + dJ[t]) * G + perm[(size_t)t * G + g]);
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
    while (elapsed() < until) {
        int pi = -1;
        if (rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            /* Iterated local search: perturb an elite configuration and re-anneal. */
            Cfg *c = &pool[pi];
            setup_group(c->K, c->K2, c->M, c->R);
            memcpy(dJ, c->J, sizeof(int) * (size_t)T);
            memcpy(dS, c->S, sizeof(int) * (size_t)T);
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
        if (no == 0) opts[no++] = 1;
        int c2 = opts[rnd_int(no)];
        int m = g / c2, r = 1;
        if (c2 > 1) {
            int found = 0;
            for (int tr = 0; tr < 200 && !found; tr++) {
                int cand = 1 + rnd_int(m - 1);
                if (gcd_i(cand, m) == 1 && powmod_i(cand, c2, m) == 1 % m) {
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

/* Helper: given w with new vertices x (side A) and y (side B) joined by an edge, and all
 * other vertices of w being old, move edges so that x and y reach degree DEG-1 + 1.
 * Each move removes an old A-B edge (a,b) and adds (x,b) and (y,a). */
static void attach_pair(Gr *w, int x, int y) {
    int n = x; /* old vertices are 0..n-1 */
    int *used = calloc((size_t)w->n, sizeof(int));
    used[x] = 1;
    used[y] = 1;
    int k = 0;
    for (int tries = 0; k < DEG - 1 && tries < 100000; tries++) {
        int a = rnd_int(n);
        if (w->side[a] != 0 || used[a] || w->deg[a] == 0) continue;
        int b = w->adj[(size_t)a * DEG + rnd_int(w->deg[a])];
        if (b >= n || used[b]) continue;
        gr_del(w, a, b);
        gr_add(w, x, b);
        gr_add(w, y, a);
        used[a] = 1;
        used[b] = 1;
        k++;
    }
    free(used);
}

/* Fill spare degree: join opposite-side vertices that both have spare degree.
 * Adding edges never increases the diameter, so this is always safe. */
static void slack_fill(Gr *g) {
    int n = g->n;
    for (int pass = 0; pass < 4; pass++) {
        int changed = 0;
        for (int a = 0; a < n; a++) {
            if (g->side[a] != 0 || g->deg[a] >= DEG) continue;
            for (int b = 0; b < n && g->deg[a] < DEG; b++) {
                if (g->side[b] != 1 || g->deg[b] >= DEG || gr_has(g, a, b)) continue;
                gr_add(g, a, b);
                changed = 1;
            }
        }
        if (!changed) break;
    }
}

/* Add two vertices (x on side A, y on side B) to a copy of best, rewire to restore degree
 * (best of REWIRE_TRIES random rewirings), then anneal degree-preserving swaps until no bad
 * pairs remain. On success best grows by 2 and spare degree is filled. */
static int grow_once(double until) {
    int n = best.n;
    if (n <= 0 || (long)(n + 2) > moore_bound()) return 0;
    int N = n + 2;
    Gr w0;
    gr_alloc(&w0, N, DEG);
    for (int v = 0; v < n; v++) {
        w0.deg[v] = best.deg[v];
        w0.side[v] = best.side[v];
        memcpy(w0.adj + (size_t)v * DEG, best.adj + (size_t)v * best.cap, sizeof(int) * best.deg[v]);
    }
    int x = n, y = n + 1;
    w0.side[x] = 0;
    w0.side[y] = 1;
    gr_add(&w0, x, y);

    /* Best-of-R rewiring: keep the attachment with the fewest bad pairs. */
    Gr w;
    int have = 0;
    long bestbad = 0;
    for (int r = 0; r < REWIRE_TRIES; r++) {
        Gr t;
        gr_copy(&t, &w0);
        attach_pair(&t, x, y);
        long nb = gr_bad(&t, NULL);
        if (!have || nb < bestbad) {
            if (have) gr_free(&w);
            w = t;
            bestbad = nb;
            have = 1;
        } else {
            gr_free(&t);
        }
        if (bestbad == 0) break;
    }
    gr_free(&w0);

    int *badv = malloc(sizeof(int) * (size_t)N);
    long bad = gr_bad(&w, badv);
    double Tm = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && elapsed() > until) break;
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

    int ok = 0;
    if (bad == 0) {
        slack_fill(&w);
        ok = gr_valid(&w);
    }
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
    while (elapsed() < until) {
        if (best.n <= 0 || (long)(best.n + 2) > moore_bound()) break;
        double left = until - elapsed();
        double slice = left < 3.0 ? left : (left / 4 > 3.0 ? left / 4 : 3.0);
        grow_once(elapsed() + slice);
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
        fprintf(stderr, "usage: prog d D seed time_limit < start_graph\n");
        return 2;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    MAXT = DEG * MAXK;
    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].S = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].cost = BIGC;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    read_start();

    if (DIAM >= 2) {
        double t_now = elapsed();
        double span = DEADLINE - t_now;
        if (span > 0) {
            /* Initial lift search, then alternate: grow the current best, and when growth
             * stalls return to lifts (which must now beat the grown graph). */
            lift_search(t_now + span * 0.3);
            if (best.n <= 0) lift_search(DEADLINE);
            while (best.n > 0 && elapsed() < DEADLINE) {
                double left = DEADLINE - elapsed();
                grow_phase(elapsed() + left * 0.5);
                if (elapsed() >= DEADLINE) break;
                left = DEADLINE - elapsed();
                lift_search(elapsed() + left * 0.3);
            }
        }
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
# Python glue: known constructions and fallbacks.
# ----------------------------------------------------------------------------

def _pg(d):
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
    """W(q) for the largest prime power q <= min(d - 1, 9)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _known_start(d, D):
    """Best construction Python builds directly for D = 3, or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Known D = 3 constructions: also handed to C as the start graph.
    start = None
    known = _known_start(d, D)
    if known is not None and lib.is_valid(known[0], known[1], d, D):
        start = known
        if known[0] > best[0]:
            best = known

    # D >= 4: generalized quadrangle baseline (cheap, guarded by time).
    if D >= 4 and time.monotonic() - t0 < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None and gq[0] > best[0] and lib.is_valid(gq[0], gq[1], d, D):
            best = gq

    if best[0] >= lib.moore_bound(d, D):
        return best

    remaining = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
    if remaining >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                            stdin_graph=start, timeout=remaining + 10.0)
            n, e = lib.parse_graph_text(out)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass   # keep the valid fallback

    return best
