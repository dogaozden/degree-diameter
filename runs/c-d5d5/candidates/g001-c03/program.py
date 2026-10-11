"""Degree-diameter search: group lifts over permutation groups PSL/PGL(2,p) and metacyclic groups,
evaluated with an orbit-reduced distance check, followed by grow-by-two annealing.

Python builds the trivial start and glues the C engine together. The C engine does the search.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core (v2).
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a known-valid starting graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * New in v2:
 *   - Orbit-reduced distance check for group lifts. A lift of a d-regular base multigraph
 *     (p vertices per side) over a group G of order N is invariant under left multiplication
 *     by G on every fibre, so all vertices of a fibre have the same distance profile. The
 *     number of bad pairs is therefore N * (sum over 2p representatives of their bad counts) / 2,
 *     which costs 2p BFS runs instead of a full all-pairs bitset check.
 *   - Arbitrary finite groups as multiplication tables: permutation groups PSL(2,p) and
 *     PGL(2,p) on the projective line (closure of 3 generators, hashed), and metacyclic
 *     groups Z_m x| Z_k.
 *   - Lift search: random base multigraph, hill-climb of voltages on the orbit-reduced count,
 *     explicit build + full validity check on success.
 *   - Grow by two (annealed edge swaps) for the remaining time.
 */
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
#define MAXP 4
#define MAXG 1400
#define MAXPT 16
#define HS 8192

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN]; /* 0 = part A, 1 = part B */
} Graph;

static int d, D;
static double t_end;

/* ------------------------------------------------------------------ utilities */

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
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Largest possible order of a bipartite graph with max degree d and diameter D. */
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

/* ------------------------------------------------------------------ graph basics */

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

/* ------------------------------------------------------------------ full distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D (0 means diameter <= D). Bitset reachability. */
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

/* Full validity check: simple, bipartite (by side labels), degree <= d, diameter <= D. */
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

/* ------------------------------------------------------------------ input / output */

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

/* K_{d,d}: always valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ finite groups as tables */

/* Group G = {0..GN-1}, identity 0, product gm[x*GN+y] = x*y, inverse ginv[x]. */
static int GN;
static int gm[MAXG * MAXG];
static int ginv[MAXG];
#define MT(x, y) gm[(x) * GN + (y)]

static void finish_inverses(void) {
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++)
            if (MT(x, y) == 0) { ginv[x] = y; break; }
}

/* Metacyclic group Z_m x|_r Z_k: element (a,b) = a*k+b, (a,b)(c,e) = (a + r^b c, b+e). */
static void build_semidirect(int m, int k, int r) {
    static int rp[MAXG];
    int N = m * k;
    GN = N;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            int aa = (int)((a + (long)rp[b] * c) % m);
            MT(x, y) = aa * k + (b + e) % k;
        }
    }
    finish_inverses();
}

/* Uniform random (m, k, r) with m*k = N, gcd(r, m) = 1 and r^k = 1 mod m. */
static int random_meta(int N, int *pm, int *pk, int *pr) {
    long cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 1;
        for (int r = 0; r < rmax; r++) {
            if (m > 1 && (gcd(r, m) != 1 || powmod(r, k, m) != 1)) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { *pm = m; *pk = k; *pr = r; }
        }
    }
    return cnt > 0;
}

/* Permutation groups: elements are permutations of P points, packed 4 bits per point. */
static unsigned char pel[MAXG][MAXPT];
static uint64_t hkey[HS];
static int hval[HS];

static uint64_t pkey(const unsigned char *q, int P) {
    uint64_t k = 0;
    for (int i = 0; i < P; i++) k |= (uint64_t)q[i] << (4 * i);
    return k;
}
static unsigned hslot(uint64_t k) { return (unsigned)((k * 0x9E3779B97F4A7C15ULL) >> 51); }
static int hfind(uint64_t k) {
    unsigned h = hslot(k);
    while (hval[h] >= 0) {
        if (hkey[h] == k) return hval[h];
        h = (h + 1) & (HS - 1);
    }
    return -1;
}
static void hput(uint64_t k, int idx) {
    unsigned h = hslot(k);
    while (hval[h] >= 0) h = (h + 1) & (HS - 1);
    hkey[h] = k;
    hval[h] = idx;
}
/* z = a then b. */
static void pcompose(const unsigned char *a, const unsigned char *b, unsigned char *z, int P) {
    for (int i = 0; i < P; i++) z[i] = b[a[i]];
}

/* Closure of the generated permutation group, then its full multiplication table.
 * Returns 0 if the group exceeds MAXG. */
static int build_perm_group(int P, int ng, unsigned char gens[][MAXPT]) {
    unsigned char z[MAXPT];
    for (int h = 0; h < HS; h++) hval[h] = -1;
    for (int i = 0; i < P; i++) pel[0][i] = (unsigned char)i;
    hput(pkey(pel[0], P), 0);
    int cnt = 1;
    for (int idx = 0; idx < cnt; idx++)
        for (int s = 0; s < ng; s++) {
            pcompose(pel[idx], gens[s], z, P);
            uint64_t k = pkey(z, P);
            if (hfind(k) < 0) {
                if (cnt >= MAXG) return 0;
                memcpy(pel[cnt], z, P);
                hput(k, cnt++);
            }
        }
    GN = cnt;
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++) {
            pcompose(pel[x], pel[y], z, P);
            int r = hfind(pkey(z, P));
            if (r < 0) return 0;
            MT(x, y) = r;
        }
    finish_inverses();
    return 1;
}

static int modinv_p(int a, int p) { return (int)powmod(a, p - 2, p); }

static int primroot(int p) {
    for (int g = 2; g < p; g++) {
        int x = 1, ord = 0;
        do { x = x * g % p; ord++; } while (x != 1);
        if (ord == p - 1) return g;
    }
    return 1;
}

/* Generators of PSL(2,p) (psl = 1) or PGL(2,p) acting on P^1(F_p) = {0..p-1, p = infinity}. */
static int make_gens(int p, int psl, unsigned char g[][MAXPT]) {
    int P = p + 1;
    for (int i = 0; i < P; i++) g[0][i] = (unsigned char)(i < p ? (i + 1) % p : p);   /* x -> x+1 */
    for (int i = 0; i < P; i++) {                                                    /* x -> -1/x */
        int v;
        if (i == p) v = 0;
        else if (i == 0) v = p;
        else v = (p - modinv_p(i, p)) % p;
        g[1][i] = (unsigned char)v;
    }
    int a = primroot(p);
    if (psl) a = a * a % p;
    for (int i = 0; i < P; i++) g[2][i] = (unsigned char)(i < p ? (a * i) % p : p);  /* x -> a x */
    return 3;
}

/* ------------------------------------------------------------------ orbit-reduced lifts */

typedef struct { int i, j, g; } Dart; /* base A-vertex i -> base B-vertex j, voltage g */

/* Current lift: P_ base vertices per side, fibre size N_ (= GN), darts dt_. */
static int P_, N_, nd_;
static Dart dt_[MAXP * MAXD];
static int Aout[MAXP][MAXD], Bin[MAXP][MAXD];
static int degA_[MAXP], degB_[MAXP];

/* Random d-regular bipartite base multigraph with p vertices per side, connected. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) { int j = rndint(i + 1); int s = perm[i]; perm[i] = perm[j]; perm[j] = s; }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, nseen = 1;
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) { seen[u] = 1; nseen++; stack[top++] = u; }
            }
        }
        if (nseen == 2 * p) return;
    }
}

/* A voltage not used by another dart between the same pair of base vertices. */
static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Random base and random voltages over the loaded group (N_ = GN). */
static void setup_base(int p, int N) {
    int M[MAXP][MAXP];
    make_base(p, M);
    P_ = p;
    N_ = N;
    nd_ = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt_[nd_].i = i;
                dt_[nd_].j = j;
                dt_[nd_].g = fresh_voltage(dt_, nd_, -1, i, j, N);
                nd_++;
            }
    for (int i = 0; i < p; i++) { degA_[i] = 0; degB_[i] = 0; }
    for (int t = 0; t < nd_; t++) {
        int i = dt_[t].i, j = dt_[t].j;
        Aout[i][degA_[i]++] = t;
        Bin[j][degB_[j]++] = t;
    }
}

static int distv[MAXN], markv[MAXN], qv[MAXN];
static int markc = 0;

/* Number of vertices within distance D of src (src included). */
static int reach_count(int src) {
    markc++;
    int head = 0, tail = 0, base_b = P_ * N_;
    qv[tail++] = src;
    markv[src] = markc;
    distv[src] = 0;
    while (head < tail) {
        int v = qv[head++];
        int dv = distv[v];
        if (dv >= D) continue;
        if (v < base_b) {
            int i = v / N_, x = v % N_;
            for (int k = 0; k < d; k++) {
                const Dart *e = &dt_[Aout[i][k]];
                int u = base_b + e->j * N_ + MT(x, e->g);
                if (markv[u] != markc) { markv[u] = markc; distv[u] = dv + 1; qv[tail++] = u; }
            }
        } else {
            int w = v - base_b, j = w / N_, z = w % N_;
            for (int k = 0; k < d; k++) {
                const Dart *e = &dt_[Bin[j][k]];
                int u = e->i * N_ + MT(z, ginv[e->g]);
                if (markv[u] != markc) { markv[u] = markc; distv[u] = dv + 1; qv[tail++] = u; }
            }
        }
    }
    return tail;
}

/* Unordered bad pairs of the current lift. The lift is invariant under left multiplication
 * by G on each fibre, so every vertex of a fibre has the same profile as the fibre's
 * identity vertex: total ordered bad = N * sum_reps bad(rep), and unordered = half of that. */
static long lift_bad(void) {
    long tot = 0;
    int total = 2 * P_ * N_;
    for (int i = 0; i < P_; i++) tot += total - reach_count(i * N_);
    for (int j = 0; j < P_; j++) tot += total - reach_count(P_ * N_ + j * N_);
    return tot * N_ / 2;
}

/* Explicit graph of the current lift. */
static void build_full(Graph *g) {
    int p = P_, N = N_;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd_; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt_[t].i * N + x, p * N + dt_[t].j * N + MT(x, dt_[t].g));
}

/* Hill-climb the voltages of the current base. On success g holds the lift (not yet checked
 * by is_valid). */
static int lift_climb(Graph *g, int steps) {
    long bad = lift_bad();
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 255) == 0 && now() > t_end) break;
        int t = rndint(nd_);
        int old = dt_[t].g;
        dt_[t].g = fresh_voltage(dt_, nd_, t, dt_[t].i, dt_[t].j, N_);
        long nb = lift_bad();
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt_[t].g = old;
    }
    if (bad != 0) return 0;
    build_full(g);
    return 1;
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    static const int pp[7] = {5, 5, 7, 7, 11, 11, 13};   /* PSL/PGL(2,p) */
    static const int psl[7] = {1, 0, 1, 0, 1, 0, 1};
    unsigned char gens[3][MAXPT];
    long moore = moore_bound();
    int loaded = -2; /* -2 none, -1 metacyclic, >= 0 permutation group index */
    while (now() < until) {
        if (best->n + 2 > moore) return;
        int p = 1 + rndint(3);
        int N;
        if (rndint(10) < 6) {
            int gi = rndint(7);
            int q = pp[gi];
            N = q * (q * q - 1) / (psl[gi] ? 2 : 1);
            if (2L * p * N > MAXN || 2L * p * N > moore || 2L * p * N < best->n + 2 || N < d) continue;
            if (loaded != gi) {
                int ng = make_gens(q, psl[gi], gens);
                if (!build_perm_group(q + 1, ng, gens) || GN != N) { loaded = -2; continue; }
                loaded = gi;
            }
        } else {
            N = (best->n + 2 + 2 * p - 1) / (2 * p) + rndint(3);
            if (N < d || 2L * p * N > MAXN || 2L * p * N > moore || N > MAXG) continue;
            int m, k, r;
            if (!random_meta(N, &m, &k, &r)) continue;
            build_semidirect(m, k, r);
            loaded = -1;
        }
        setup_base(p, N);
        if (lift_climb(&cand, 2000 + rndint(18000)) && cand.n > best->n && is_valid(&cand))
            copy_graph(best, &cand);
    }
}

/* ------------------------------------------------------------------ grow by two */

/* Insert one new vertex per side into a copy of best (degree d each), then anneal edge swaps.
 * Returns 1 if work ends valid with best->n + 2 vertices. */
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

/* ------------------------------------------------------------------ main */

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
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);

    if (D >= 2 && best.n < moore_bound()) {
        lift_search(&best, t0 + (t_end - t0) * 0.8);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: always valid
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget], stdin_graph=start, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(*out, d, D):
                best = out
        except (RuntimeError, ValueError):
            pass   # keep the valid fallback
    return best
