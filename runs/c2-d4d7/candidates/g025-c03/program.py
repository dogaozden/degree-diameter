"""Bi-Cayley group search for the weakest target (d=4, D=7), with the parent's grow-by-two as the second phase.

Change from the parent: the explicit voltage-lift search is replaced by a different construction.
Each candidate is a bi-Cayley graph over a non-abelian group G of order N: vertices A_x and B_x for x in G,
with A_x adjacent to B_{x s} for s in a connection set S of size d. Degree is d, the graph is bipartite,
and it has 2N vertices. Groups are direct products built from a menu of factors: cyclic groups,
dihedral groups, A4, S4, A5, S5, PSL(2,7), PSL(2,11). The product is kept only if it is non-abelian.

The diameter check is exact. Left multiplication is an automorphism, so the graph has diameter <= D iff
BFS from A_e and from B_e both reach all 2N vertices within D steps. The hill climb swaps one element of S
at a time, and the window of group orders starts just above the current best, so the search climbs upward.

Phase 1 (60% of the C budget) runs the group search. Phase 2 runs grow-by-two annealing on the best graph.
Python keeps the algebraic starts (projective plane, W(q), H(3)) and returns the best valid graph.
"""
import time

import itertools

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXG 1000
#define MAXPT 12
#define MAXF 3
#define MAXFAC 80
#define MAXSPEC 40000
#define HS 8192
#define CLIMB_STEPS 20000
#define RESTARTS 3
#define WIN 40

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void del_half(Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][--g->deg[u]];
            return;
        }
}

static void del_edge(Graph *g, int u, int v) {
    del_half(g, u, v);
    del_half(g, v, u);
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D (bitset all-pairs). */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur + (size_t)g->adj[v][i] * W;
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
        badv[v] = n - c;
        total += n - c;
    }
    return total / 2;
}

static int is_valid(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) { g->side[u] = 1 - g->side[v]; queue[tail++] = u; }
                else if (g->side[u] == g->side[v]) { g->n = 0; return; }
            }
        }
    }
    if (!is_valid(g)) g->n = 0;
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ---------------------------------------------------------------- permutation groups */
typedef struct { unsigned char p[MAXPT]; } Perm;
typedef struct { int ord; int *tab; } Factor;

static Factor FAC[MAXFAC];
static int nfac = 0, ncyc = 0;
static Perm EL[MAXG];
static uint64_t hkey[HS];
static int hval[HS];

static uint64_t pkey(const unsigned char *p, int s) {
    uint64_t k = 0;
    for (int i = 0; i < s; i++) k |= (uint64_t)p[i] << (4 * i);
    return k;
}

static unsigned hslot(uint64_t key) {
    return (unsigned)((key * 0x9E3779B97F4A7C15ULL) >> 51);
}

static int hfind(uint64_t key) {
    unsigned h = hslot(key);
    while (hval[h]) {
        if (hkey[h] == key) return hval[h] - 1;
        h = (h + 1) & (HS - 1);
    }
    return -1;
}

static void hput(uint64_t key, int idx) {
    unsigned h = hslot(key);
    while (hval[h]) h = (h + 1) & (HS - 1);
    hkey[h] = key;
    hval[h] = idx + 1;
}

/* Closure of generators acting on s points. EL[0] is the identity. Returns the order or -1. */
static int closure(const Perm *gen, int ng, int s) {
    memset(hval, 0, sizeof hval);
    memset(&EL[0], 0, sizeof(Perm));
    for (int x = 0; x < s; x++) EL[0].p[x] = (unsigned char)x;
    hput(pkey(EL[0].p, s), 0);
    int n = 1;
    for (int qi = 0; qi < n; qi++)
        for (int k = 0; k < ng; k++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = EL[qi].p[gen[k].p[x]];
            uint64_t key = pkey(h.p, s);
            if (hfind(key) < 0) {
                if (n >= MAXG) return -1;
                EL[n] = h;
                hput(key, n);
                n++;
            }
        }
    return n;
}

static void set_perm(Perm *p, int s, const int *img) {
    memset(p, 0, sizeof *p);
    for (int x = 0; x < s; x++) p->p[x] = (unsigned char)img[x];
}

static int add_perm_factor(const Perm *gen, int ng, int s) {
    if (nfac >= MAXFAC) return 0;
    int n = closure(gen, ng, s);
    if (n <= 0) return 0;
    int *tab = malloc(sizeof(int) * (size_t)n * (size_t)n);
    if (!tab) return 0;
    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = EL[i].p[EL[j].p[x]];
            int idx = hfind(pkey(h.p, s));
            tab[(size_t)i * n + j] = idx < 0 ? 0 : idx;
        }
    FAC[nfac].ord = n;
    FAC[nfac].tab = tab;
    nfac++;
    return 1;
}

static int add_cyclic(int k) {
    if (nfac >= MAXFAC) return 0;
    int *tab = malloc(sizeof(int) * (size_t)k * (size_t)k);
    if (!tab) return 0;
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++) tab[(size_t)i * k + j] = (i + j) % k;
    FAC[nfac].ord = k;
    FAC[nfac].tab = tab;
    nfac++;
    return 1;
}

/* PSL(2,p) acting on P^1(F_p) = {0..p-1, inf = p}. */
static void add_psl(int p) {
    int inf = p, s = p + 1;
    int t[MAXPT], u[MAXPT];
    for (int x = 0; x <= p; x++) t[x] = (x == inf) ? inf : (x + 1) % p;
    for (int x = 0; x <= p; x++) {
        int v;
        if (x == inf) v = 0;
        else if (x == 0) v = inf;
        else v = (int)((p - powmod(x, p - 2, p)) % p);
        u[x] = v;
    }
    Perm g[2];
    set_perm(&g[0], s, t);
    set_perm(&g[1], s, u);
    add_perm_factor(g, 2, s);
}

static void build_menu(void) {
    nfac = 0;
    for (int k = 2; k <= 40; k++) add_cyclic(k);
    ncyc = nfac;
    for (int k = 3; k <= 12; k++) {
        int rot[MAXPT], refl[MAXPT];
        Perm g[2];
        for (int x = 0; x < k; x++) {
            rot[x] = (x + 1) % k;
            refl[x] = (k - x) % k;
        }
        set_perm(&g[0], k, rot);
        set_perm(&g[1], k, refl);
        add_perm_factor(g, 2, k);
    }
    {
        Perm g[2];
        int a1[4] = {1, 2, 0, 3}, a2[4] = {1, 0, 3, 2};
        set_perm(&g[0], 4, a1);
        set_perm(&g[1], 4, a2);
        add_perm_factor(g, 2, 4);             /* A4 */
        int s1[4] = {1, 0, 2, 3}, s2[4] = {1, 2, 3, 0};
        set_perm(&g[0], 4, s1);
        set_perm(&g[1], 4, s2);
        add_perm_factor(g, 2, 4);             /* S4 */
        int b1[5] = {1, 2, 0, 3, 4}, b2[5] = {1, 2, 3, 4, 0}, c1[5] = {1, 0, 2, 3, 4};
        set_perm(&g[0], 5, b1);
        set_perm(&g[1], 5, b2);
        add_perm_factor(g, 2, 5);             /* A5 */
        set_perm(&g[0], 5, c1);
        set_perm(&g[1], 5, b2);
        add_perm_factor(g, 2, 5);             /* S5 */
    }
    add_psl(7);                               /* order 168 */
    add_psl(11);                              /* order 660 */
}

/* ---------------------------------------------------------------- group specs */
typedef struct { int f[MAXF]; int nf; int N; } Spec;
static Spec SPEC[MAXSPEC];
static int nspec = 0;
static int spec_dmin = 1;
static long moore_lim = 0;

static void add_spec(const int *f, int nf) {
    long N = 1;
    int allcyc = 1;
    for (int i = 0; i < nf; i++) {
        N *= FAC[f[i]].ord;
        if (N > MAXG) return;
        if (f[i] >= ncyc) allcyc = 0;
    }
    if (allcyc) return;                 /* abelian groups do not give diameter-D graphs at these sizes */
    if (N < spec_dmin || 2 * N > moore_lim) return;
    if (nspec >= MAXSPEC) return;
    for (int i = 0; i < nf; i++) SPEC[nspec].f[i] = f[i];
    SPEC[nspec].nf = nf;
    SPEC[nspec].N = (int)N;
    nspec++;
}

static int cmp_spec(const void *a, const void *b) {
    int x = ((const Spec *)a)->N, y = ((const Spec *)b)->N;
    return (x > y) - (x < y);
}

static void gen_specs(void) {
    int f[MAXF];
    nspec = 0;
    for (int i = 0; i < nfac; i++) { f[0] = i; add_spec(f, 1); }
    for (int i = 0; i < nfac; i++)
        for (int j = i; j < nfac; j++) { f[0] = i; f[1] = j; add_spec(f, 2); }
    for (int i = 0; i < nfac; i++)
        for (int j = i; j < nfac; j++)
            for (int k = j; k < nfac; k++) { f[0] = i; f[1] = j; f[2] = k; add_spec(f, 3); }
    qsort(SPEC, (size_t)nspec, sizeof(Spec), cmp_spec);
}

static void decode(int x, const int *o, int nf, int *c) {
    for (int i = nf - 1; i >= 0; i--) {
        c[i] = x % o[i];
        x /= o[i];
    }
}

static int encode(const int *c, const int *o, int nf) {
    int x = 0;
    for (int i = 0; i < nf; i++) x = x * o[i] + c[i];
    return x;
}

/* ---------------------------------------------------------------- bi-Cayley search state */
static int GT[MAXG * MAXG];
static int INVG[MAXG];
static int NG = 0;
static int S[MAXD], Si[MAXD];
static int vis[2 * MAXG], dl[2 * MAXG], dq[2 * MAXG];
static int vst = 0;

static void build_product(const int *f, int nf) {
    int o[MAXF], c1[MAXF], c2[MAXF], c3[MAXF];
    int N = 1;
    for (int i = 0; i < nf; i++) {
        o[i] = FAC[f[i]].ord;
        N *= o[i];
    }
    NG = N;
    for (int x = 0; x < N; x++) {
        decode(x, o, nf, c1);
        for (int y = 0; y < N; y++) {
            decode(y, o, nf, c2);
            for (int i = 0; i < nf; i++)
                c3[i] = FAC[f[i]].tab[(size_t)c1[i] * o[i] + c2[i]];
            GT[x * N + y] = encode(c3, o, nf);
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (GT[x * N + y] == 0) { INVG[x] = y; break; }
}

/* BFS from src in the bi-Cayley graph on 2N vertices (A_x = x, B_y = N + y).
 * Returns the number of vertices within distance D of src. */
static int bfs_reach(int src, int N, int K) {
    vst++;
    int head = 0, tail = 0;
    vis[src] = vst;
    dl[src] = 0;
    dq[tail++] = src;
    while (head < tail) {
        int v = dq[head++];
        if (dl[v] >= D) continue;
        if (v < N) {
            const int *row = GT + (size_t)v * N;
            for (int k = 0; k < K; k++) {
                int u = N + row[S[k]];
                if (vis[u] != vst) {
                    vis[u] = vst;
                    dl[u] = dl[v] + 1;
                    dq[tail++] = u;
                }
            }
        } else {
            const int *row = GT + (size_t)(v - N) * N;
            for (int k = 0; k < K; k++) {
                int u = row[Si[k]];
                if (vis[u] != vst) {
                    vis[u] = vst;
                    dl[u] = dl[v] + 1;
                    dq[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* Objective: unreached (vertex, source) pairs from A_e and B_e. Zero iff diameter <= D. */
static long eval_S(void) {
    for (int k = 0; k < d; k++) Si[k] = INVG[S[k]];
    long N2 = 2L * NG;
    long a = bfs_reach(0, NG, d);
    long b = bfs_reach(NG, NG, d);
    return (N2 - a) + (N2 - b);
}

static int fresh_elem(int k) {
    int c, ok;
    do {
        c = rndint(NG);
        ok = 1;
        for (int j = 0; j < d; j++)
            if (j != k && S[j] == c) { ok = 0; break; }
    } while (!ok);
    return c;
}

static int climb(double until) {
    for (int k = 0; k < d; k++) S[k] = fresh_elem(k);
    long cur = eval_S();
    for (int s = 0; s < CLIMB_STEPS && cur > 0; s++) {
        if ((s & 255) == 0 && now() > until) break;
        int k = rndint(d);
        int old = S[k];
        S[k] = fresh_elem(k);
        long f = eval_S();
        if (f <= cur || rnd01() < 0.01) cur = f;
        else S[k] = old;
    }
    if (cur == 0) {
        eval_S();
        return 1;
    }
    return 0;
}

static void build_bicayley(Graph *g) {
    int N = NG;
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= N;
    }
    for (int x = 0; x < N; x++)
        for (int k = 0; k < d; k++)
            add_edge(g, x, N + GT[(size_t)x * N + S[k]]);
}

static void group_phase(Graph *best, double until) {
    static Graph cand;
    while (now() < until && nspec > 0) {
        long lo = best->n / 2 + 1;
        int s0 = 0;
        while (s0 < nspec && SPEC[s0].N < lo) s0++;
        if (s0 >= nspec) break;
        int s1 = s0;
        while (s1 < nspec && SPEC[s1].N <= lo + WIN) s1++;
        int pick = (s1 > s0) ? s0 + rndint(s1 - s0) : s0 + rndint(nspec - s0);
        build_product(SPEC[pick].f, SPEC[pick].nf);
        for (int r = 0; r < RESTARTS && now() < until; r++) {
            if (climb(until)) {
                build_bicayley(&cand);
                if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
                break;
            }
        }
    }
}

/* ---------------------------------------------------------------- grow by two */
static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
    long bad = bad_pairs(work);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (work->side[s] != work->side[v] || s == v || work->deg[s] == 0) continue;
        int t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
        long nb = bad_pairs(work);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(work, v, t);
            del_edge(work, s, u);
            add_edge(work, v, u);
            add_edge(work, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

static void grow_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) {
        complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && d >= 2 && best.n < moore_bound()) {
        build_menu();
        moore_lim = moore_bound();
        long lo = best.n / 2 + 1;
        spec_dmin = (int)((lo > d + 1) ? lo : d + 1);
        gen_specs();
        group_phase(&best, t0 + (t_end - t0) * 0.6);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _gh_h3():
    """Incidence graph of the split Cayley hexagon H(3): 364 + 364 vertices, degree 4, diameter 6.

    Returns None if no sign convention verifies with lib.is_valid.
    """
    q = 3

    def norm(v):
        c = next(x for x in v if x)
        inv = 1 if c == 1 else 2
        return tuple((x * inv) % q for x in v)

    vecs = itertools.product(range(q), repeat=7)
    pts = sorted({norm(v) for v in vecs if any(v) and
                  (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % q == 0})
    P = len(pts)
    index = {p: i for i, p in enumerate(pts)}

    def bil(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] +
                x[2] * y[6] + x[6] * y[2] + x[3] * y[3]) % q

    def pl(x, y, i, j):
        return (x[i] * y[j] - x[j] * y[i]) % q

    conds = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)),
             ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]
    combos = ((1, 0), (0, 1), (1, 1), (1, 2))
    for s in (1, -1):
        lines = set()
        for i in range(P):
            x = pts[i]
            for j in range(i + 1, P):
                y = pts[j]
                if bil(x, y):
                    continue
                if any((pl(x, y, *a) - s * pl(x, y, *b)) % q for a, b in conds):
                    continue
                L = frozenset(index[norm(tuple((a * x[k] + b * y[k]) % q for k in range(7)))]
                              for a, b in combos)
                lines.add(L)
        if len(lines) != P or any(len(L) != 4 for L in lines):
            continue
        ordered = sorted(lines, key=sorted)
        edges = [(p, P + j) for j, L in enumerate(ordered) for p in L]
        n = P + len(ordered)
        if lib.is_valid(n, edges, 4, 6):
            return n, edges
    return None


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    if d == 4 and D >= 6:
        try:
            gh = _gh_h3()
        except Exception:
            gh = None
        if gh is not None:
            out.append(gh)
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.2:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 6)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
