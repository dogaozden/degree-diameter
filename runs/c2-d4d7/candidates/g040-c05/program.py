"""Bi-Cayley and voltage lifts over nonabelian groups, with a fast orbit-reduced search (d=4, D=7 focus).

Change from the parent: the main search is no longer a random walk over metacyclic lifts. It samples
regular voltage lifts with 1-3 fibres per side over nonabelian groups: PSL(2,p), PGL(2,p) (p = 5, 7, 11),
S_4, S_6, their direct products with Z_k, and nonabelian metacyclic groups Z_m x| Z_k. Each candidate is
annealed on the number of vertices that are farther than D from a fibre identity. Only 2P BFS runs are
needed per evaluation, so the search does tens of thousands of evaluations per second. Any solution is
re-checked on the explicit graph with the full all-pairs test. Grow-by-two annealing then uses the last
part of the budget. Python keeps the algebraic starts and falls back to the best valid graph.
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
#define MAXG 2048
#define MAXP 3
#define MAXDART (MAXD * MAXP)
#define HS 8192
#define MAXOPT 4096
#define NBASE 8

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

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

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

/* Full all-pairs check by bitsets: number of unordered pairs at distance > D. */
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

/* ---------------------------------------------------------------- groups
 * GT[x*GN+y] = x*y with identity 0, GINV[x] = x^{-1}. Groups are built from
 * permutation closures (PSL/PGL(2,p), S_n) and metacyclic formulas. */
static int GN;
static unsigned short GT[MAXG * MAXG];
static int GINV[MAXG];
static int RP[MAXG];

typedef struct { unsigned char p[16]; } Perm;
static Perm PE[MAXG];
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

static int perm_closure(const Perm *gen, int ng, int s, int *ordp) {
    memset(hval, 0, sizeof hval);
    memset(&PE[0], 0, sizeof(Perm));
    for (int x = 0; x < s; x++) PE[0].p[x] = (unsigned char)x;
    hput(pkey(PE[0].p, s), 0);
    int n = 1;
    for (int qi = 0; qi < n; qi++) {
        for (int k = 0; k < ng; k++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = PE[qi].p[gen[k].p[x]];
            uint64_t key = pkey(h.p, s);
            if (hfind(key) < 0) {
                if (n >= MAXG) return 0;
                PE[n] = h;
                hput(key, n);
                n++;
            }
        }
    }
    *ordp = n;
    return 1;
}

static int prim_root(int p) {
    for (int c = 2; c < p; c++) {
        int ok = 1;
        for (int e = 1; e < p - 1 && ok; e++)
            if (powmod(c, e, p) == 1) ok = 0;
        if (ok) return c;
    }
    return 1;
}

/* type 0: PSL(2,p), type 1: PGL(2,p), type 2: S_n. Returns the order (0 on failure). */
static int build_base(int type, int param, unsigned short **tabp) {
    int s = 0, ng = 0;
    Perm gen[3];
    memset(gen, 0, sizeof gen);
    if (type == 2) {
        int n = param;
        s = n;
        for (int x = 0; x < n; x++) gen[0].p[x] = (unsigned char)x;
        gen[0].p[0] = 1;
        gen[0].p[1] = 0;
        for (int x = 0; x < n; x++) gen[1].p[x] = (unsigned char)((x + 1) % n);
        ng = 2;
    } else {
        int p = param, inf = p;
        s = p + 1;
        int prim = prim_root(p);
        for (int x = 0; x <= p; x++)
            gen[0].p[x] = (unsigned char)((x == inf) ? inf : (x + 1) % p);
        for (int x = 0; x <= p; x++) {
            int v;
            if (x == inf) v = 0;
            else if (x == 0) v = inf;
            else v = (int)((p - powmod(x, p - 2, p)) % p);
            gen[1].p[x] = (unsigned char)v;
        }
        ng = 2;
        if (type == 1) {
            for (int x = 0; x <= p; x++)
                gen[2].p[x] = (unsigned char)((x == inf) ? inf : (x * prim) % p);
            ng = 3;
        }
    }
    int ord = 0;
    if (!perm_closure(gen, ng, s, &ord)) return 0;
    unsigned short *tab = malloc(sizeof(unsigned short) * (size_t)ord * (size_t)ord);
    if (!tab) return 0;
    for (int i = 0; i < ord; i++)
        for (int j = 0; j < ord; j++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = PE[i].p[PE[j].p[x]];
            int idx = hfind(pkey(h.p, s));
            tab[(size_t)i * ord + j] = (unsigned short)(idx < 0 ? 0 : idx);
        }
    *tabp = tab;
    return ord;
}

static unsigned short *BTAB[NBASE];
static int BORD[NBASE];

static void init_bases(void) {
    static const int BT[NBASE] = {0, 1, 0, 1, 0, 1, 2, 2};
    static const int BP[NBASE] = {5, 5, 7, 7, 11, 11, 4, 6};
    for (int b = 0; b < NBASE; b++) {
        BTAB[b] = NULL;
        BORD[b] = build_base(BT[b], BP[b], &BTAB[b]);
        if (!BTAB[b]) BORD[b] = 0;
    }
}

typedef struct { int kind, b, k, m, r; } Opt;   /* kind 0: base x Z_k, kind 1: Z_m x| Z_k */
static Opt OPT[MAXOPT];
static int NBAS_OPT;

/* Options of order N. Abelian groups are excluded, since abelian Haar-type graphs grow too slowly. */
static int collect_opts(int N) {
    int cnt = 0;
    for (int b = 0; b < NBASE; b++) {
        int o = BORD[b];
        if (o > 0 && N % o == 0 && cnt < MAXOPT) {
            OPT[cnt].kind = 0; OPT[cnt].b = b; OPT[cnt].k = N / o;
            OPT[cnt].m = 0; OPT[cnt].r = 0;
            cnt++;
        }
    }
    NBAS_OPT = cnt;
    for (int m = 2; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (k < 2) continue;
        for (int r = 2; r < m && cnt < MAXOPT; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            OPT[cnt].kind = 1; OPT[cnt].b = 0; OPT[cnt].k = k;
            OPT[cnt].m = m; OPT[cnt].r = r;
            cnt++;
        }
    }
    return cnt;
}

static void build_group(const Opt *o) {
    if (o->kind == 0) {
        int ob = BORD[o->b], k = o->k, N = ob * k;
        const unsigned short *bt = BTAB[o->b];
        GN = N;
        for (int x = 0; x < ob; x++)
            for (int c = 0; c < k; c++)
                for (int y = 0; y < ob; y++)
                    for (int e = 0; e < k; e++) {
                        int xi = x * k + c, yi = y * k + e;
                        GT[xi * N + yi] = (unsigned short)(bt[x * ob + y] * k + (c + e) % k);
                    }
    } else {
        int m = o->m, k = o->k, N = m * k, r = o->r;
        GN = N;
        RP[0] = 1 % m;
        for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
        for (int x = 0; x < N; x++) {
            int a = x / k, b = x % k;
            for (int y = 0; y < N; y++) {
                int c = y / k, e = y % k;
                int za = (int)((a + (long)RP[b] * c) % m);
                GT[x * N + y] = (unsigned short)(za * k + (b + e) % k);
            }
        }
    }
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++)
            if (GT[x * GN + y] == 0) { GINV[x] = y; break; }
}

/* ---------------------------------------------------------------- bi-Cayley / voltage lifts
 * Base: P A-fibres and P B-fibres, d darts out of each A-fibre and into each B-fibre (ND = P*d).
 * Dart t joins A-fibre DA[t] to B-fibre DB[t] with voltage DG[t]. Vertex (a,x) is a*N+x for A and
 * (P+b)*N+y for B. Edges: (a,x) ~ (P+b, x*g) for each dart (a,b,g). Left multiplication by G is an
 * automorphism, so the diameter test needs one BFS from each fibre identity (2P BFS in total). */
static int P;
static int ND;
static int DA[MAXDART], DB[MAXDART], DG[MAXDART];
static int ADART[MAXP][MAXD], BDART[MAXP][MAXD];

static int uf_find(int *par, int x) {
    while (par[x] != x) { par[x] = par[par[x]]; x = par[x]; }
    return x;
}

static int fresh_volt(int t) {
    for (;;) {
        int g = rndint(GN), clash = 0;
        for (int u = 0; u < ND && !clash; u++)
            if (u != t && DA[u] == DA[t] && DB[u] == DB[t] && DG[u] == g) clash = 1;
        if (!clash) return g;
    }
}

static int random_base(void) {
    ND = P * d;
    int ok = 0;
    for (int tries = 0; tries < 2000 && !ok; tries++) {
        int t = 0;
        for (int pi = 0; pi < d; pi++) {
            int perm[MAXP];
            for (int i = 0; i < P; i++) perm[i] = i;
            for (int i = P - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int a = 0; a < P; a++) { DA[t] = a; DB[t] = perm[a]; t++; }
        }
        int par[2 * MAXP];
        for (int i = 0; i < 2 * P; i++) par[i] = i;
        for (int u = 0; u < ND; u++) {
            int x = uf_find(par, DA[u]), y = uf_find(par, P + DB[u]);
            par[x] = y;
        }
        int root = uf_find(par, 0);
        ok = 1;
        for (int i = 1; i < 2 * P && ok; i++)
            if (uf_find(par, i) != root) ok = 0;
    }
    if (!ok) return 0;
    int ca[MAXP] = {0}, cb[MAXP] = {0};
    for (int t = 0; t < ND; t++) {
        ADART[DA[t]][ca[DA[t]]++] = t;
        BDART[DB[t]][cb[DB[t]]++] = t;
    }
    for (int t = 0; t < ND; t++) DG[t] = -1;
    for (int t = 0; t < ND; t++) DG[t] = fresh_volt(t);
    return 1;
}

static int vis[MAXN];
static int vstamp = 0;
static int qb[MAXN];

/* Sum over the 2P fibre identities of the number of vertices farther than D. Zero iff the lift
 * has diameter <= D. */
static long orbit_bad(void) {
    int N = GN, PN = P * N, V = 2 * PN;
    long total = 0;
    if (vstamp > 2000000000) { memset(vis, 0, sizeof vis); vstamp = 0; }
    for (int s = 0; s < 2 * P; s++) {
        int src = s * N;
        int head = 0, tail = 0;
        vstamp++;
        qb[tail++] = src;
        vis[src] = vstamp;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int v = qb[head++];
                if (v < PN) {
                    int a = v / N, x = v - a * N;
                    for (int j = 0; j < d; j++) {
                        int t = ADART[a][j];
                        int u = (P + DB[t]) * N + GT[x * N + DG[t]];
                        if (vis[u] != vstamp) { vis[u] = vstamp; qb[tail++] = u; }
                    }
                } else {
                    int w = v - PN, b = w / N, y = w - b * N;
                    for (int j = 0; j < d; j++) {
                        int t = BDART[b][j];
                        int u = DA[t] * N + GT[y * N + GINV[DG[t]]];
                        if (vis[u] != vstamp) { vis[u] = vstamp; qb[tail++] = u; }
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

static void build_explicit(Graph *g) {
    int N = GN, PN = P * N;
    g->n = 2 * PN;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= PN; }
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, DA[t] * N + x, (P + DB[t]) * N + GT[x * N + DG[t]]);
}

/* Simulated annealing on the voltages of the current base and group. Returns 1 if bad == 0. */
static int run_sa(long steps, double until) {
    long bad = orbit_bad(), bestbad = bad;
    int bestDG[MAXDART];
    memcpy(bestDG, DG, sizeof(int) * ND);
    const double T0 = 1.5, T1 = 0.05;
    for (long s = 0; s < steps && bestbad > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        double T = T0 * pow(T1 / T0, (double)s / (double)steps);
        int t = rndint(ND);
        int old = DG[t];
        DG[t] = fresh_volt(t);
        long nb = orbit_bad();
        if (nb <= bad || rnd01() < exp(-(double)(nb - bad) / T)) bad = nb;
        else DG[t] = old;
        if (bad < bestbad) {
            bestbad = bad;
            memcpy(bestDG, DG, sizeof(int) * ND);
        }
    }
    memcpy(DG, bestDG, sizeof(int) * ND);
    return bestbad == 0;
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    while (now() < until) {
        int r = rndint(10);
        int Pc = r < 3 ? 1 : (r < 7 ? 2 : 3);
        long Nmin = best->n / (2L * Pc) + 1;
        if (Nmin < d + 1) Nmin = d + 1;
        long N = Nmin + rndint(4 + (int)(Nmin / 25));
        if (2L * Pc * N > moore || 2L * Pc * N > MAXN || N > MAXG) continue;
        int cnt = collect_opts((int)N);
        if (cnt == 0) continue;
        int pick;
        if (NBAS_OPT > 0 && (NBAS_OPT == cnt || rndint(2) == 0))
            pick = rndint(NBAS_OPT);
        else
            pick = NBAS_OPT + rndint(cnt - NBAS_OPT);
        build_group(&OPT[pick]);
        P = Pc;
        if (!random_base()) continue;
        long steps = 60000L / (Pc * Pc);
        if (run_sa(steps, until)) {
            build_explicit(&cand);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
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
    while (now() < until && best->n + 2 <= moore_bound() && best->n + 2 <= MAXN) {
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
        printf("1 0\n");
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && best.n < moore_bound()) {
        init_bases();
        lift_search(&best, t0 + (t_end - t0) * 0.8);
        if (best.n < moore_bound()) grow_search(&best, t_end);
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

    Several sign conventions are tried, and a candidate is kept only if it passes lib.is_valid
    with diameter 6. Returns None if nothing verifies.
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
