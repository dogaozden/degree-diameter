"""Base-graph voltage-lift search plus the parent's sweep and grow-by-two repair.

New in this version: a base-graph lift. For each known start graph B (projective plane,
GQ W(3), hexagon H(3)), the C engine looks for a Z_m voltage lift of B with
|B| * m vertices, which is larger than the current best and at most the Moore bound.
Voltages on a BFS spanning tree of B are gauge-fixed to 0, so only the non-tree darts
are searched. Simulated annealing minimises the orbit-reduced count of unreached
(representative, vertex) pairs. A lift is accepted only if lib-style full bitset
checking confirms diameter <= D. Small bases such as W(3) have cheap evaluations,
so this search can reach orders above the parent's sweep.

Python runs the base lift on each start graph, then runs the parent's full engine
(sweep and grow) from the best graph found.
"""
import time

import itertools

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:   prog d D seed time_limit [target_n] [mode]  < start_graph
 *   stdin:  "n m" then m lines "u v", or "0 0" for none.
 *   stdout: "n m" then m lines "u v": the largest valid graph found.
 *   mode 1: base-graph Z_m lift search only.
 *   mode 0: base-graph lift, then bi-Cayley sweep, then grow-by-two repair.
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
#define SWEEP_SPREAD 12
#define SWEEP_BAND 200
#define MAXDART (MAXN * MAXD / 2)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static int target_n = 0;
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

/* Orbit-reduced diameter objective for a regular-fibre lift. Left multiplication by the group
 * is an automorphism, so BFS from the identity of each fibre suffices. */
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

/* ------------------------------------------------------------------------
 * Base-graph Z_m voltage lift.
 * Base B has nb vertices. Each base edge (u on side 0, v on side 1) is a dart with a
 * voltage g in Z_m. Lift vertex (v, x) is v*m + x, and dart (u, v, g) joins
 * (u, x) to (v, x+g mod m) for every x. The lift keeps the base degrees and is bipartite.
 * Voltages on a BFS spanning tree of B are gauge-fixed to 0 (switching), so only the
 * remaining darts are searched.
 * ------------------------------------------------------------------------ */
static int bdu[MAXDART], bdv[MAXDART], bdg[MAXDART], bfree[MAXDART];
static int nbd;
static int bpar[MAXN], bq[MAXN];

static void prepare_darts(const Graph *base) {
    nbd = 0;
    for (int u = 0; u < base->n; u++) {
        if (base->side[u] != 0) continue;
        for (int i = 0; i < base->deg[u]; i++) {
            if (nbd >= MAXDART) break;
            bdu[nbd] = u;
            bdv[nbd] = base->adj[u][i];
            nbd++;
        }
    }
    int n = base->n;
    for (int v = 0; v < n; v++) bpar[v] = -2;
    int h = 0, t = 0;
    bpar[0] = -1;
    bq[t++] = 0;
    while (h < t) {
        int v = bq[h++];
        for (int i = 0; i < base->deg[v]; i++) {
            int u = base->adj[v][i];
            if (bpar[u] == -2) { bpar[u] = v; bq[t++] = u; }
        }
    }
    for (int e = 0; e < nbd; e++)
        bfree[e] = !(bpar[bdu[e]] == bdv[e] || bpar[bdv[e]] == bdu[e]);
}

static void build_blift(Graph *L, const Graph *base, int m) {
    L->n = base->n * m;
    for (int v = 0; v < L->n; v++) { L->deg[v] = 0; L->side[v] = base->side[v / m]; }
    for (int e = 0; e < nbd; e++) {
        int g = bdg[e];
        for (int x = 0; x < m; x++) {
            int a = bdu[e] * m + x;
            int b = bdv[e] * m + (x + g) % m;
            add_edge(L, a, b);
        }
    }
}

/* Orbit-reduced count of unreached (source, vertex) pairs; sources are one vertex per fibre. */
static long blift_bad(const Graph *L, int nb, int m) {
    int nv = L->n;
    long total = 0;
    for (int b = 0; b < nb; b++) {
        int src = b * m;
        for (int v = 0; v < nv; v++) dist_buf[v] = -1;
        int head = 0, tail = 0;
        dist_buf[src] = 0;
        queue_buf[tail++] = src;
        while (head < tail) {
            int v = queue_buf[head++];
            if (dist_buf[v] >= D) continue;
            for (int i = 0; i < L->deg[v]; i++) {
                int u = L->adj[v][i];
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

static int anneal_blift(const Graph *base, int m, double deadline, Graph *out) {
    static Graph L;
    int nb = base->n;
    int nfree = 0;
    for (int e = 0; e < nbd; e++) nfree += bfree[e];
    for (int e = 0; e < nbd; e++) bdg[e] = 0;
    for (int e = 0; e < nbd; e++)
        if (bfree[e]) bdg[e] = rndint(m);
    build_blift(&L, base, m);
    long bad = blift_bad(&L, nb, m);
    long best_bad = bad;
    long stall = 0;
    long stall_limit = 500 + 10L * nb;
    long steps = 0;
    while (bad > 0) {
        if (nfree == 0) return 0;
        if ((steps & 7) == 0 && now() > deadline) return 0;
        steps++;
        int e;
        do { e = rndint(nbd); } while (!bfree[e]);
        int old = bdg[e];
        int ng = rndint(m - 1);
        if (ng >= old) ng++;
        bdg[e] = ng;
        build_blift(&L, base, m);
        long nbv = blift_bad(&L, nb, m);
        double T = 0.5 + 0.02 * (double)bad;
        if (nbv <= bad || rnd01() < exp(-(double)(nbv - bad) / T)) bad = nbv;
        else bdg[e] = old;
        if (bad < best_bad) {
            best_bad = bad;
            stall = 0;
        } else if (++stall > stall_limit) {
            for (int f = 0; f < nbd; f++)
                if (bfree[f]) bdg[f] = rndint(m);
            build_blift(&L, base, m);
            bad = blift_bad(&L, nb, m);
            best_bad = bad;
            stall = 0;
        }
    }
    build_blift(&L, base, m);
    if (!is_valid(&L)) return 0;
    copy_graph(out, &L);
    return 1;
}

/* Search Z_m lifts of the base graph for orders above the current best, up to the Moore bound. */
static void base_lift(Graph *best, const Graph *base, double until) {
    static Graph cand;
    int nb = base->n;
    if (nb < 2) return;
    prepare_darts(base);
    if (nbd == 0) return;
    long moore = moore_bound();
    long mhi_l = moore / nb;
    if (mhi_l > MAXN / nb) mhi_l = MAXN / nb;
    int mhi = (int)mhi_l;
    while (now() < until) {
        int mlo = best->n / nb + 1;
        if (mlo < 2) mlo = 2;
        if (mlo > mhi) break;
        int span = mhi - mlo + 1;
        int m = mlo;
        if (span > 1 && rndint(3) == 0) m = mlo + rndint(span < 3 ? span : 3);
        double rem = until - now();
        double slice = rem * 0.35;
        if (slice < 0.5) slice = rem;
        if (anneal_blift(base, m, now() + slice, &cand) && cand.n > best->n)
            copy_graph(best, &cand);
    }
}

/* Bi-Cayley sweep. The group order N is drawn from [lo, hi], where lo gives a lift just
 * above the current best and hi reaches toward the target size (within SWEEP_BAND of lo).
 * Any valid lift larger than the best is kept, which raises the floor for later draws. */
static void lift_sweep(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    while (now() < until) {
        int p = rndint(5) == 0 ? 2 : 1;
        int lo = best->n / (2 * p) + 1;
        int hi = lo + SWEEP_SPREAD;
        if (target_n > 0) {
            int th = target_n / (2 * p);
            if (th > hi) hi = th < lo + SWEEP_BAND ? th : lo + SWEEP_BAND;
        }
        int N = lo + rndint(hi - lo + 1);
        if (2L * p * N > moore || 2 * p * N > MAXN) {
            N = lo;
            if (2L * p * N > moore || 2 * p * N > MAXN) {
                if (p == 1) return;
                continue;
            }
        }
        for (int a = 0; a < 4 && now() < until; a++) {
            if (!random_group(N, &G)) break;
            if (lift_fast_try(&cand, p, N, &G, 6000, until) && cand.n > best->n &&
                is_valid(&cand)) {
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

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [target_n] [mode] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    target_n = argc > 5 ? atoi(argv[5]) : 0;
    int mode = argc > 6 ? atoi(argv[6]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best, start;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    copy_graph(&start, &best);

    if (D >= 2 && best.n < moore_bound()) {
        double lift_end = mode == 1 ? t_end : t0 + (t_end - t0) * 0.45;
        base_lift(&best, &start, lift_end);
        if (mode == 0 && best.n < moore_bound()) lift_sweep(&best, t0 + (t_end - t0) * 0.7);
        if (mode == 0 && best.n > 0) grow_search(&best, t_end);
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


def _h3_lines(pts, index, s):
    """Lines of H(3) from Tits' description, with the right-hand sign multiplier s (1 or 2 mod 3)."""
    P = len(pts)

    def bil(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1]
                + x[2] * y[6] + x[6] * y[2] - 2 * x[3] * y[3]) % 3

    def norm(v):
        c = next(t for t in v if t)
        inv = 1 if c == 1 else 2
        return tuple((t * inv) % 3 for t in v)

    lines = set()
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            y = pts[j]
            if bil(x, y):
                continue

            def pl(a, b):
                return (x[a] * y[b] - x[b] * y[a]) % 3

            conds = [(pl(1, 2), pl(3, 4)), (pl(5, 4), pl(3, 2)), (pl(2, 0), pl(3, 5)),
                     (pl(6, 5), pl(3, 0)), (pl(0, 1), pl(3, 6)), (pl(4, 6), pl(3, 1))]
            if any((a - s * b) % 3 for a, b in conds):
                continue
            L = set()
            for a in range(3):
                for b in range(3):
                    if a == 0 and b == 0:
                        continue
                    v = tuple((a * x[k] + b * y[k]) % 3 for k in range(7))
                    if any(v):
                        L.add(index[norm(v)])
            if len(L) == 4:
                lines.add(tuple(sorted(L)))
    return lines


def _hexagon_h3():
    """Incidence graph of the split Cayley hexagon H(3): 728 vertices, 4-regular, diameter 6.

    Both sign conventions are tried, and the result is accepted only if lib.is_valid confirms
    it. Returns (n, edges) or None.
    """
    pts = []
    for v in itertools.product(range(3), repeat=7):
        if not any(v):
            continue
        if v[next(i for i, c in enumerate(v) if c)] != 1:
            continue
        if (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % 3:
            continue
        pts.append(v)
    P = len(pts)
    if P != 364:
        return None
    index = {v: i for i, v in enumerate(pts)}
    for s in (1, 2):
        lines = _h3_lines(pts, index, s)
        if len(lines) != P:
            continue
        lines = sorted(lines)
        edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
        if lib.is_valid(2 * P, edges, 4, 6):
            return 2 * P, edges
    return None


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


# Known record orders used as sweep targets, keyed by (d, D).
RECORDS = {
    (4, 7): 840,
}


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


def _valid_starts(d, D):
    """Haar K_{d,d} first, then every valid algebraic start (and H(3) when D >= 6)."""
    starts = [lib.haar_graph(d, range(d))]
    for n, e in known_starts(d, D):
        if lib.is_valid(n, e, d, D):
            starts.append((n, e))
    if d == 4 and D >= 6:
        try:
            hexg = _hexagon_h3()
        except Exception:
            hexg = None
        if hexg is not None and lib.is_valid(hexg[0], hexg[1], d, D):
            starts.append(hexg)
    return starts


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    starts = _valid_starts(d, D)
    best = max(starts, key=lambda g: g[0])
    moore = lib.moore_bound(d, D)
    if d > 31 or best[0] >= moore:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.2:
        return best
    target = RECORDS.get((d, D), 0)

    # Phase A: base-graph Z_m lifts of each algebraic start (mode 1: lift only).
    bases = [s for s in starts[1:] if s[0] < moore]
    per = 0.5 * budget / len(bases) if bases else 0.0
    for base in bases:
        if per < 0.5:
            break
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(per, 2), target, 1],
                             stdin_graph=base, timeout=per + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass

    # Phase B: full engine (lift, sweep, grow) from the best graph found so far.
    remaining = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if remaining > 0.5 and best[0] < moore:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), target, 0],
                             stdin_graph=best, timeout=remaining + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass
    return best
