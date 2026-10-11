"""Starter program: Python builds the best known start graph, the C engine searches from it.

Change in this version: the C grow step now adds ONE vertex at a time and allows vertices
to end below degree d. The new vertex takes d neighbours from the other side, which leaves
d deficient vertices on its own side. Annealing then fills deficits with new edges and moves
edge endpoints onto deficient vertices, so odd orders (base + 1) are reachable. Degree-preserving
2-switches and the old pair-growth move remain as fallbacks. The lift search runs only when no
structured start exists. This change is untested here; build() still validates everything.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a known-valid starting graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found
 *          (bipartite, every degree <= d, every pair of vertices within D steps).
 *
 * Search:
 *   1. Voltage lifts over groups Z_m x| Z_k, only when no start graph is given.
 *   2. Growth. A new vertex x on side s takes d neighbours from the other side, each giving
 *      up one of its neighbours. Degrees may fall below d (deficits). Then anneal with:
 *        - add an edge between deficient, non-adjacent vertices on opposite sides;
 *        - move one endpoint of an edge to a deficient vertex on the same side;
 *        - degree-preserving 2-switches.
 *      The objective is the number of pairs at distance > D. Growth by one vertex
 *      gives odd orders; growth by two (one per side) is the fallback.
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

/* ------------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN]; /* badv[v] = vertices farther than D from v, after bad_pairs() */

/* Number of unordered pairs at distance > D (0 means connected with diameter <= D). */
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

/* Read "n m" + edges from stdin; 2-colour it. Leaves g->n = 0 if absent or invalid. */
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

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a, b) is the int a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct {
    int m, k, r;
    int rp[MAXN]; /* rp[b] = r^b mod m */
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Pick a uniformly random (m, k, r) with m*k = N, gcd(r, m) = 1 and r^k = 1 mod m. */
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

/* ------------------------------------------------------------------ voltage lifts */

typedef struct { int i, j, g; } Dart; /* base A-vertex i -> base B-vertex j, voltage g */

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

static int lift_try(Graph *g, int p, int N, const Grp *G, int steps) {
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
    long bad = bad_pairs(g);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 15) == 0 && now() > t_end) return 0;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, G, dt, nd);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < 0.01) bad = nb;
        else dt[t].g = old;
    }
    if (bad != 0) return 0;
    return 1;
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        int r = rndint(10);
        int p = r < 4 ? 1 : r < 7 ? 2 : r < 9 ? 3 : 4;
        long target = best->n + 2;
        if (target > moore) return;
        int N = (int)((target + 2 * p - 1) / (2 * p)) + rndint(2);
        if (best->n == 0) N = d + rndint(3);
        if (N < d || 2L * p * N > moore || 2 * p * N > MAXN) {
            if (++fails > 1000) return;
            continue;
        }
        if (!random_group(N, &G)) continue;
        int steps = 200 + 400000 / (2 * p * N);
        if (lift_try(&cand, p, N, &G, steps) && cand.n > best->n && is_valid(&cand))
            copy_graph(best, &cand);
    }
}

/* ------------------------------------------------------------------ growth with deficits */

/* Add vertex x on side s. x takes d distinct neighbours u on the other side; each u gives its
 * neighbour w (on side s) to x. Every u keeps its degree, every w ends one short (a deficit). */
static int attach_new(Graph *g, int s) {
    static int taken[MAXN];
    static int stamp = 0;
    int n = g->n, x = n, k = 0;
    if (n + 1 > MAXN) return 0;
    stamp++;
    g->n = n + 1;
    g->deg[x] = 0;
    g->side[x] = (unsigned char)s;
    for (long tries = 0; k < d && tries < 200000; tries++) {
        int u = rndint(n);
        if (g->side[u] == s || g->deg[u] == 0 || taken[u] == stamp) continue;
        int w = g->adj[u][rndint(g->deg[u])];
        taken[u] = stamp;
        del_edge(g, w, u);
        add_edge(g, x, u);
        k++;
    }
    return k == d;
}

/* Anneal a graph whose degrees are <= d until its diameter is <= D.
 * Moves: fill an edge between deficient opposite-side vertices (never hurts),
 * move an edge endpoint onto a deficient vertex, or a degree-preserving 2-switch.
 * Returns 1 when bad pairs reach 0 before the deadline. */
static int anneal_fill(Graph *g, double until) {
    static int defA[MAXN], defB[MAXN];
    long bad = bad_pairs(g);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        int na = 0, nbv = 0;
        for (int v = 0; v < g->n; v++) {
            if (g->deg[v] >= d) continue;
            if (g->side[v] == 0) defA[na++] = v;
            else defB[nbv++] = v;
        }
        if (na > 0 && nbv > 0) {
            int i0 = rndint(na), j0 = rndint(nbv), done = 0;
            for (int i = 0; i < na && !done; i++) {
                int a = defA[(i + i0) % na];
                for (int j = 0; j < nbv && !done; j++) {
                    int b = defB[(j + j0) % nbv];
                    if (!has_edge(g, a, b)) { add_edge(g, a, b); done = 1; }
                }
            }
            if (done) { bad = bad_pairs(g); continue; }
        }
        int u = rndint(g->n);
        if (rnd01() < 0.7)
            for (int t = 0; t < 30 && badv[u] == 0; t++) u = rndint(g->n);
        if (g->deg[u] == 0) continue;
        int w = g->adj[u][rndint(g->deg[u])];
        int *dl = g->side[w] == 0 ? defA : defB;
        int ndl = g->side[w] == 0 ? na : nbv;
        if (ndl > 0 && rnd01() < 0.7) {
            /* move edge (u,w) to (u,w2), w2 deficient on w's side */
            int w2 = dl[rndint(ndl)];
            if (w2 == w || has_edge(g, w2, u)) continue;
            del_edge(g, w, u);
            add_edge(g, w2, u);
            long nb = bad_pairs(g);
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
            else { del_edge(g, w2, u); add_edge(g, w, u); }
        } else {
            /* degree-preserving switch: (u,w),(s,t) -> (u,t),(s,w) */
            int s = rndint(g->n);
            if (s == u || g->side[s] != g->side[u] || g->deg[s] == 0) continue;
            int t = g->adj[s][rndint(g->deg[s])];
            if (t == w || has_edge(g, u, t) || has_edge(g, s, w)) continue;
            del_edge(g, u, w);
            del_edge(g, s, t);
            add_edge(g, u, t);
            add_edge(g, s, w);
            long nb = bad_pairs(g);
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
            else {
                del_edge(g, u, t);
                del_edge(g, s, w);
                add_edge(g, u, w);
                add_edge(g, s, t);
            }
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return 1;
}

/* Grow by one vertex on side s (order n + 1). */
static int grow_single(const Graph *best, Graph *work, int s, double until) {
    if (best->n + 1 > moore_bound() || best->n + 1 > MAXN) return 0;
    copy_graph(work, best);
    if (!attach_new(work, s)) return 0;
    if (!anneal_fill(work, until)) return 0;
    return is_valid(work);
}

/* Grow by two: one new vertex per side (order n + 2). */
static int grow_pair(const Graph *best, Graph *work, double until) {
    if (best->n + 2 > moore_bound() || best->n + 2 > MAXN) return 0;
    copy_graph(work, best);
    if (!attach_new(work, 0) || !attach_new(work, 1)) return 0;
    if (!anneal_fill(work, until)) return 0;
    return is_valid(work);
}

static void grow_search(Graph *best, double until) {
    static Graph work;
    int fails = 0;
    while (now() < until && fails < 40) {
        if (best->n + 1 > moore_bound() || best->n + 1 > MAXN) break;
        double left = until - now();
        double slice = left / 6.0 > 3.0 ? left / 6.0 : 3.0;
        if (slice > left) slice = left;
        int cnt[2] = {0, 0};
        for (int v = 0; v < best->n; v++) cnt[best->side[v]]++;
        int s = cnt[0] < cnt[1] ? 0 : cnt[1] < cnt[0] ? 1 : rndint(2);
        if (grow_single(best, &work, s, now() + slice)) {
            copy_graph(best, &work);
            fails = 0;
            continue;
        }
        if (now() < until) {
            double dl = now() + slice;
            if (dl > until) dl = until;
            if (grow_pair(best, &work, dl)) {
                copy_graph(best, &work);
                fails = 0;
                continue;
            }
        }
        fails++;
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
    int had_start = best.n > 0;

    if (D >= 2 && best.n < moore_bound()) {
        /* With a structured start, spend all the time on growth. */
        if (!had_start) lift_search(&best, t0 + (t_end - t0) * 0.6);
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


def conic_blowup(d, D):
    """Twin-blow-up of PG(2,q) with q = d-3 odd, using a conic and a dual conic.

    Each point of a conic S (no 3 collinear) and each line of a dual conic T (no 3 concurrent)
    is duplicated once. Copies are twins of the originals, so the diameter stays 3. A copy
    adds one degree to each neighbour, so each line gains at most 2 and each point at most 2.
    Gives 2(q^2+q+1) + 2(q+1) vertices, which is 394 for q = 13 (d = 16).
    """
    q = d - 3
    if D != 3 or q < 3 or q % 2 == 0 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {v: i for i, v in enumerate(pts)}
    m = len(pts)
    conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if any(v not in index for v in conic):
        return None
    arc = [index[v] for v in conic]              # same indices serve as dual conic for lines
    n0, base = lib.projective_plane_incidence(q)  # points 0..m-1, lines m..2m-1
    pcopy = {i: [i] for i in range(m)}
    lcopy = {j: [m + j] for j in range(m)}
    n = n0
    for i in arc:
        pcopy[i].append(n)
        n += 1
    for j in arc:
        lcopy[j].append(n)
        n += 1
    edges = set()
    for u, v in base:            # u is a point (< m), v = m + line index
        i, j = u, v - m
        for a in pcopy[i]:
            for b in lcopy[j]:
                edges.add((a, b) if a < b else (b, a))
    return n, sorted(edges)


def starts(d, D):
    """Candidate structured start graphs (each already built, validity checked later)."""
    out = []
    ks = known_start(d, D)
    if ks is not None:
        out.append(ks)
    cb = conic_blowup(d, D)
    if cb is not None:
        out.append(cb)
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = None
    for cand in starts(d, D):
        try:
            ok = lib.is_valid(cand[0], cand[1], d, D)
        except Exception:
            ok = False
        if ok and (start is None or cand[0] > start[0]):
            start = cand
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
        except Exception:
            pass   # keep the valid structured or K_{d,d} fallback
    return best
