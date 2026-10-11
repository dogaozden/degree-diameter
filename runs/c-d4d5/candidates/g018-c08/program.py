"""Bi-Cayley search over explicit non-metacyclic groups, then the parent's lift and grow search.

The parent only used semidirect products Z_m x| Z_k. This version passes small nonabelian
permutation groups (direct products of S3, S4, A4, D4, V4, cyclic groups, SL(2,3), GL(2,3),
and the Heisenberg group of order 27) to C. C first runs a bi-Cayley search: vertices A_x and B_x
for x in G, with edges A_x - B_{x s} for s in a d-subset S of G. Left multiplication is an
automorphism, so two BFS runs (from A_e and B_e) decide the diameter. If that search finds nothing
larger than the start, the parent's lift and grow phases still run. K_{d,d} and the algebraic
starts remain the fallback, and every output is checked with lib.is_valid."""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:   prog d D seed time_limit [group ...]   < start_graph
 * Each optional group argument is "N k" followed by N permutations of k points (all elements).
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * 1. Bi-Cayley graphs over the supplied groups (orbit-reduced diameter test: 2 BFS).
 * 2. Voltage lifts over semidirect groups Z_m x|_r Z_k, base multigraphs on p <= 4 vertices per side.
 * 3. Grow by two: insert one vertex per side and anneal degree-preserving edge swaps.
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
#define MAXG 16
#define MAXGN 128
#define MAXK 40

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

/* Z_m x|_r Z_k: element a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

static int random_group(int N, Grp *G) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)(count < 2000000000L ? count : 2000000000L)) == 0) {
                G->m = m; G->k = k; G->r = r;
            }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

typedef struct { int i, j, g; } Dart;

/* Random d-regular bipartite base multigraph on p + p vertices, connected. */
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

/* Vertex layout: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x. */
static void build_lift(Graph *g, int p, int N, const Grp *G, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(G, x, dt[t].g));
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Orbit-reduced diameter objective for a regular-fibre lift.
 * Left multiplication acts on every fibre, so it is enough to BFS from the 2p representatives
 * b*N. Returns the number of (representative, vertex) pairs at distance > D. */
static int dist_buf[MAXN], queue_buf[MAXN];

static long orbit_bad(const Graph *g, int p, int N) {
    int nv = g->n;
    long total = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
        for (int v = 0; v < nv; v++) dist_buf[v] = -1;
        int head = 0, tail = 0;
        dist_buf[src] = 0;
        queue_buf[tail++] = src;
        while (head < tail) {
            int v = queue_buf[head++];
            if (dist_buf[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dist_buf[u] < 0) {
                    dist_buf[u] = dist_buf[v] + 1;
                    queue_buf[tail++] = u;
                }
            }
        }
        total += nv - tail;
    }
    return total;
}

/* Hill-climb the voltages of one random base multigraph over the group G. */
static int lift_fast_try(Graph *g, int p, int N, const Grp *G, int steps, double until) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i; dt[nd].j = j;
                dt[nd].g = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(g, p, N, G, dt, nd);
    long bad = orbit_bad(g, p, N);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, G, dt, nd);
        long nb = orbit_bad(g, p, N);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
    }
    build_lift(g, p, N, G, dt, nd);
    return bad == 0;
}

/* Search lifts of size 2pN strictly larger than the current best. */
static void fast_lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    while (now() < until) {
        int r = rndint(20);
        int p = r < 8 ? 1 : r < 14 ? 2 : r < 18 ? 3 : 4;
        long target = best->n + 2;
        if (target > moore) return;
        int Nmin = (int)((target + 2 * p - 1) / (2 * p));
        int N = Nmin + rndint(3);
        if (N < d) N = d;
        if (2L * p * N > moore || 2 * p * N > MAXN) continue;
        if (!random_group(N, &G)) continue;
        for (int a = 0; a < 3 && now() < until; a++) {
            if (lift_fast_try(&cand, p, N, &G, 20000, until) && is_valid(&cand) &&
                cand.n > best->n) {
                copy_graph(best, &cand);
                break;
            }
        }
    }
}

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

/* ---- explicit groups (all elements given as permutations) and bi-Cayley search ---- */

typedef struct {
    int N, k;
    int mt[MAXGN][MAXGN];   /* mt[x][y] = index of x*y */
} BGroup;

static BGroup bg[MAXG];
static int nbg = 0;

static unsigned long long perm_hash(const int *p, int k) {
    unsigned long long h = 1469598103934665603ULL;
    for (int j = 0; j < k; j++) h = (h ^ (unsigned long long)(p[j] + 1)) * 1099511628211ULL;
    return h;
}

static int perm_eq(const int *a, const int *b, int k) {
    for (int j = 0; j < k; j++) if (a[j] != b[j]) return 0;
    return 1;
}

static int in_set(const int *S, int k, int x) {
    for (int u = 0; u < k; u++) if (S[u] == x) return 1;
    return 0;
}

/* Parse "N k p_0 ... p_{N-1}" (each p_i is k integers). Adds the group if it is a valid group. */
static int parse_group(const char *s) {
    char *end = NULL;
    long N = strtol(s, &end, 10);
    long k = strtol(end, &end, 10);
    static int P[MAXGN][MAXK];
    static unsigned long long H[MAXGN];
    if (N < 1 || N > MAXGN || k < 1 || k > MAXK) return 0;
    for (int i = 0; i < N; i++)
        for (int j = 0; j < k; j++) {
            long v = strtol(end, &end, 10);
            if (v < 0 || v >= k) return 0;
            P[i][j] = (int)v;
        }
    for (int i = 0; i < N; i++) {
        int seen[MAXK] = {0};
        for (int j = 0; j < k; j++) {
            if (seen[P[i][j]]) return 0;
            seen[P[i][j]] = 1;
        }
        H[i] = perm_hash(P[i], (int)k);
        for (int t = 0; t < i; t++)
            if (H[t] == H[i] && perm_eq(P[t], P[i], (int)k)) return 0;
    }
    BGroup *G = &bg[nbg];
    G->N = (int)N;
    G->k = (int)k;
    for (int x = 0; x < G->N; x++)
        for (int y = 0; y < G->N; y++) {
            int z[MAXK];
            for (int j = 0; j < k; j++) z[j] = P[x][P[y][j]];
            unsigned long long h = perm_hash(z, (int)k);
            int found = -1;
            for (int t = 0; t < G->N && found < 0; t++)
                if (H[t] == h && perm_eq(P[t], z, (int)k)) found = t;
            if (found < 0) return 0;   /* not closed under composition: not a group */
            G->mt[x][y] = found;
        }
    nbg++;
    return 1;
}

/* Choose d distinct elements of Z-indices 0..N-1 as connection set S. */
static void bc_pick_S(int N, int *S) {
    for (int t = 0; t < d; t++) {
        int x;
        do { x = rndint(N); } while (in_set(S, t, x));
        S[t] = x;
    }
}

/* Bi-Cayley graph: A_x (index x) joins B_{x*s} (index N + x*s) for s in S. */
static void build_bc(Graph *g, const BGroup *G, const int *S) {
    int N = G->N;
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int t = 0; t < d; t++)
            add_edge(g, x, N + G->mt[x][S[t]]);
}

static void bicayley_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    while (now() < until) {
        int cands[MAXG], nc = 0;
        for (int gi = 0; gi < nbg; gi++) {
            long N = bg[gi].N;
            if (N <= d || 2 * N <= best->n || 2 * N > moore || 2 * N > MAXN) continue;
            cands[nc++] = gi;
        }
        if (nc == 0) return;
        const BGroup *G = &bg[cands[rndint(nc)]];
        int N = G->N;
        int S[MAXD];
        bc_pick_S(N, S);
        build_bc(&cand, G, S);
        long bad = orbit_bad(&cand, 1, N);
        for (int s = 0; s < 3000 && bad > 0; s++) {
            if ((s & 63) == 0 && now() > until) break;
            int t = rndint(d);
            int x;
            do { x = rndint(N); } while (in_set(S, d, x));
            int old = S[t];
            S[t] = x;
            build_bc(&cand, G, S);
            long nb = orbit_bad(&cand, 1, N);
            if (nb <= bad || rnd01() < 0.02) bad = nb;
            else S[t] = old;
        }
        if (bad == 0 && cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [groups...] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.94;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    for (int i = 5; i < argc && nbg < MAXG; i++) parse_group(argv[i]);

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);

    if (D >= 2 && best.n < moore_bound()) {
        double span = t_end - t0;
        bicayley_search(&best, t0 + span * 0.5);
        fast_lift_search(&best, t0 + span * 0.65);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
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
    return out


# ------------------------------------------------ explicit groups for the bi-Cayley search

_FACTORS = ["S3", "S4", "A4", "D4", "V4", "Z2", "Z3", "Z4", "Z5", "Z6", "Z7",
            "SL23", "GL23", "H3"]


def _closure(gens, cap):
    """All elements of the permutation group generated by gens, or None if more than cap."""
    k = len(gens[0])
    ident = tuple(range(k))
    elems = [ident]
    seen = {ident}
    i = 0
    while i < len(elems):
        x = elems[i]
        i += 1
        for g in gens:
            y = tuple(x[g[j]] for j in range(k))
            if y not in seen:
                if len(elems) >= cap:
                    return None
                seen.add(y)
                elems.append(y)
    return elems


def _apply3(M, v):
    """Matrix M (tuple of rows) applied to vector v over GF(3)."""
    return tuple(sum(M[i][j] * v[j] for j in range(len(v))) % 3 for i in range(len(M)))


def _matrix_perms(mats, dim):
    pts = list(itertools.product(range(3), repeat=dim))
    idx = {v: i for i, v in enumerate(pts)}
    return [tuple(idx[_apply3(M, v)] for v in pts) for M in mats]


def _even(p):
    inv = sum(1 for i in range(len(p)) for j in range(i + 1, len(p)) if p[i] > p[j])
    return inv % 2 == 0


def _factor(name):
    """(degree, elements) of a small permutation group."""
    if name == "S3":
        return 3, list(itertools.permutations(range(3)))
    if name == "S4":
        return 4, list(itertools.permutations(range(4)))
    if name == "A4":
        return 4, [p for p in itertools.permutations(range(4)) if _even(p)]
    if name == "D4":
        return 4, _closure([(1, 2, 3, 0), (0, 3, 2, 1)], 200)
    if name == "V4":
        return 4, _closure([(1, 0, 3, 2), (2, 3, 0, 1)], 200)
    if name == "SL23":
        return 9, _closure(_matrix_perms([((1, 1), (0, 1)), ((1, 0), (1, 1))], 2), 200)
    if name == "GL23":
        return 9, _closure(_matrix_perms(
            [((1, 1), (0, 1)), ((1, 0), (1, 1)), ((2, 0), (0, 1))], 2), 200)
    if name == "H3":
        return 27, _closure(_matrix_perms(
            [((1, 1, 0), (0, 1, 0), (0, 0, 1)), ((1, 0, 0), (0, 1, 1), (0, 0, 1))], 3), 200)
    k = int(name[1:])  # cyclic group Z_k
    return k, _closure([tuple((i + 1) % k for i in range(k))], 200)


def _group_args(lo, hi, maxg=14):
    """Argument strings for direct products of small groups with order in [lo, hi]."""
    if hi < lo:
        return []
    fac = {name: _factor(name) for name in _FACTORS}
    cands = []
    for i, a in enumerate(_FACTORS):
        for b in _FACTORS[i:]:
            if fac[a][1] is None or fac[b][1] is None:
                continue
            n = len(fac[a][1]) * len(fac[b][1])
            if lo <= n <= hi:
                cands.append((n, a, b))
    cands.sort()
    if len(cands) > maxg:
        idx = sorted({round(i * (len(cands) - 1) / (maxg - 1)) for i in range(maxg)})
        cands = [cands[i] for i in idx]
    out = []
    for n, a, b in cands:
        da, ea = fac[a]
        db, eb = fac[b]
        parts = [str(n), str(da + db)]
        for x in ea:
            for y in eb:
                parts.extend(str(v) for v in x)
                parts.extend(str(da + v) for v in y)
        out.append(" ".join(parts))
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 0.2:
        return best
    try:
        lo = best[0] // 2 + 1
        hi = min(lib.moore_bound(d, D) // 2, 127)
        groups = _group_args(lo, hi)
    except Exception:
        groups = []
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget, *groups],
                         stdin_graph=best, timeout=budget + 4)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
