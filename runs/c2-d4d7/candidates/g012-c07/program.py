"""Bold change for the weakest target (d=4, D=7): bi-Cayley lifts over permutation groups.

The parent searched voltage lifts over metacyclic groups Z_m x| Z_k only. This version adds a
different construction. The engine builds each candidate group as a closed permutation group from
generators, then runs an iterated local search over voltages of a base multigraph with 1 or 2
vertices per side. Groups come from PSL/PGL(2,p) and affine groups Z_m x| <r>, and from direct
products with small cyclic and abelian factors. For one base vertex per side the diameter check
needs only two BFS runs, so the search evaluates many voltage assignments per second.

The best starting graph (split Cayley hexagon H(3), 728 vertices, or a smaller known graph) is
kept as the fallback. A lift replaces it only if it is strictly larger and passes lib.is_valid.
After the group search, the parent's grow-by-two annealing uses the remaining time.
"""
import itertools
import math
import random
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core, group-lift edition.
 * Usage:   prog d D seed time_limit [group ...] < start_graph
 * Group:   generators as permutations, "g1a,g1b,...;g2a,g2b,..." (points 0..deg-1).
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * 1. Each group is closed from its generators and given a full multiplication table.
 *    A lift over it has base multigraph with p <= 2 vertices per side and degree d, and each
 *    dart (i, j, g) joins A_{i,x} to B_{j,x*g}. The group acts on each fibre by left
 *    multiplication, so the diameter check needs only BFS from the 2p fibre representatives.
 *    Each lift is an iterated local search with elite restarts and two-dart kicks.
 * 2. Grow by two: insert one vertex per side and anneal degree-preserving edge swaps.
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
#define MAXP 2
#define MAXG 1200
#define MAXDEG 32
#define MAXGEN 8
#define MAXGROUPS 64
#define HSIZE 8192
#define KICK_AFTER 2000

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;

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

/* ---------------------------------------------------------------- permutation groups */

static int G_N, G_deg;
static unsigned char G_el[MAXG][MAXDEG];
static short G_mul[MAXG][MAXG];
static int G_htab[HSIZE];

static unsigned hash_perm(const unsigned char *p, int deg) {
    unsigned h = 2166136261u;
    for (int i = 0; i < deg; i++) { h ^= p[i]; h *= 16777619u; }
    return h & (HSIZE - 1);
}

static int htab_find(const unsigned char *p) {
    unsigned h = hash_perm(p, G_deg);
    while (G_htab[h]) {
        int idx = G_htab[h] - 1;
        if (memcmp(G_el[idx], p, G_deg) == 0) return idx;
        h = (h + 1) & (HSIZE - 1);
    }
    return -1;
}

static int htab_insert(const unsigned char *p) {
    if (G_N >= MAXG) return -1;
    unsigned h = hash_perm(p, G_deg);
    while (G_htab[h]) h = (h + 1) & (HSIZE - 1);
    memcpy(G_el[G_N], p, G_deg);
    G_htab[h] = G_N + 1;
    return G_N++;
}

/* Close the generated group and build its multiplication table, x*y = x after y.
 * Returns 0 if the group is larger than MAXG. */
static int build_group(int ng, unsigned char gen[MAXGEN][MAXDEG], int deg) {
    G_deg = deg;
    G_N = 0;
    memset(G_htab, 0, sizeof G_htab);
    unsigned char id[MAXDEG];
    for (int i = 0; i < deg; i++) id[i] = (unsigned char)i;
    htab_insert(id);
    for (int h = 0; h < G_N; h++)
        for (int s = 0; s < ng; s++) {
            unsigned char c[MAXDEG];
            for (int i = 0; i < deg; i++) c[i] = gen[s][G_el[h][i]];
            if (htab_find(c) < 0 && htab_insert(c) < 0) return 0;
        }
    for (int x = 0; x < G_N; x++)
        for (int y = 0; y < G_N; y++) {
            unsigned char c[MAXDEG];
            for (int i = 0; i < deg; i++) c[i] = G_el[x][G_el[y][i]];
            G_mul[x][y] = (short)htab_find(c);
        }
    return 1;
}

/* Parse "g1a,g1b;g2a,g2b;..." into generator arrays. Checks that each generator is a permutation. */
static int parse_group(const char *s, unsigned char gen[MAXGEN][MAXDEG], int *ng_out, int *deg_out) {
    int g = 0, k = 0, deg = -1, val = 0, have = 0;
    for (const char *p = s;; p++) {
        if (*p >= '0' && *p <= '9') {
            val = val * 10 + (*p - '0');
            if (val > MAXDEG) return 0;
            have = 1;
            continue;
        }
        if (have) {
            if (k >= MAXDEG || g >= MAXGEN || val >= MAXDEG) return 0;
            gen[g][k++] = (unsigned char)val;
            val = 0;
            have = 0;
        }
        if (*p == ',') continue;
        if (*p == ';' || *p == '\0') {
            if (k == 0) return 0;
            if (deg < 0) deg = k;
            else if (k != deg) return 0;
            g++;
            k = 0;
            if (*p == '\0') break;
            continue;
        }
        return 0;
    }
    if (deg < 2 || deg > MAXDEG || g == 0) return 0;
    for (int h = 0; h < g; h++) {
        int seen[MAXDEG];
        memset(seen, 0, sizeof seen);
        for (int i = 0; i < deg; i++) {
            int v = gen[h][i];
            if (v >= deg || seen[v]) return 0;
            seen[v] = 1;
        }
    }
    *ng_out = g;
    *deg_out = deg;
    return 1;
}

static int ngroups = 0;
static unsigned char store_gen[MAXGROUPS][MAXGEN][MAXDEG];
static int store_ng[MAXGROUPS], store_deg[MAXGROUPS];

/* ---------------------------------------------------------------- lifts */

typedef struct { int i, j, g; } Dart;

/* Layout: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x.
 * Dart (i, j, g) joins A_{i,x} to B_{j, x*g}. */
static void build_lift(Graph *g, int p, int N, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + G_mul[x][dt[t].g]);
}

static void make_base(int p, int M[MAXP][MAXP], int d_) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d_; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
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

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static int dist_buf[MAXN], queue_buf[MAXN];

/* Number of (representative, vertex) pairs at distance > D; zero iff the lift has diameter <= D. */
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

/* Iterated local search over the voltages of one random base multigraph over the current group.
 * Stops at time `until`. Returns 1 if the best assignment has diameter <= D. */
static int lift_ils(Graph *g, int p, int N, double until) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP], bestdt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M, d);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(g, p, N, dt, nd);
    long bad = orbit_bad(g, p, N);
    long bestbad = bad;
    memcpy(bestdt, dt, sizeof(Dart) * nd);
    int stall = 0;
    for (long s = 0; bestbad > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, dt, nd);
        long nb = orbit_bad(g, p, N);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
        if (bad < bestbad) {
            bestbad = bad;
            memcpy(bestdt, dt, sizeof(Dart) * nd);
            stall = 0;
        } else {
            stall++;
        }
        if (stall > KICK_AFTER && bestbad > 0) {
            memcpy(dt, bestdt, sizeof(Dart) * nd);
            for (int k = 0; k < 2; k++) {
                int u = rndint(nd);
                dt[u].g = fresh_voltage(dt, nd, u, dt[u].i, dt[u].j, N);
            }
            build_lift(g, p, N, dt, nd);
            bad = orbit_bad(g, p, N);
            stall = 0;
        }
    }
    memcpy(dt, bestdt, sizeof(Dart) * nd);
    build_lift(g, p, N, dt, nd);
    return bestbad == 0;
}

/* Round-robin over the supplied groups, each with a short iterated search, until `until`. */
static void group_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    if (ngroups == 0) return;
    while (now() < until) {
        int gi = rndint(ngroups);
        if (!build_group(store_ng[gi], store_gen[gi], store_deg[gi])) continue;
        int N = G_N;
        int ps[MAXP], np = 0;
        for (int p = 1; p <= MAXP; p++) {
            long v = 2L * p * N;
            if (v > best->n && v <= moore && v <= MAXN) ps[np++] = p;
        }
        if (!np) continue;
        int p = ps[rndint(np)];
        double stop = now() + 0.6;
        if (stop > until) stop = until;
        if (lift_ils(&cand, p, N, stop) && is_valid(&cand) && cand.n > best->n)
            copy_graph(best, &cand);
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
        fprintf(stderr, "usage: %s d D seed time_limit [groups...] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    double t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    for (int a = 5; a < argc && ngroups < MAXGROUPS; a++) {
        int ng = 0, dg = 0;
        if (parse_group(argv[a], store_gen[ngroups], &ng, &dg)) {
            store_ng[ngroups] = ng;
            store_deg[ngroups] = dg;
            ngroups++;
        }
    }

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && best.n < moore_bound()) {
        group_search(&best, t0 + (t_end - t0) * 0.7);
        if (best.n > 0) grow_search(&best, t_end);
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
    """Incidence graph of the split Cayley hexagon H(3): 364 + 364 vertices, degree 4, diameter 6."""
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


# ------------------------------------------------------------ permutation groups

def _prime_factors(n):
    f, x = [], n
    p = 2
    while p * p <= x:
        if x % p == 0:
            f.append(p)
            while x % p == 0:
                x //= p
        p += 1
    if x > 1:
        f.append(x)
    return f


def _primitive_root(p):
    if p == 2:
        return 1
    for s in range(2, p):
        if all(pow(s, (p - 1) // f, p) != 1 for f in _prime_factors(p - 1)):
            return s
    return 1


def _psl_pgl(p, pgl):
    """Generators of PSL(2,p) or PGL(2,p) on the projective line (points 0..p-1, infinity = p)."""
    inf = p
    T = [(x + 1) % p if x < p else inf for x in range(p + 1)]
    J = []
    for x in range(p + 1):
        if x == inf:
            J.append(0)
        elif x == 0:
            J.append(inf)
        else:
            J.append((-pow(x, p - 2, p)) % p)
    gens = [T, J]
    if pgl:
        s = _primitive_root(p)
        gens.append([(s * x) % p if x < p else inf for x in range(p + 1)])
    return gens


def _cyclic(k):
    return k, [[(i + 1) % k for i in range(k)]]


def _affine(m, r):
    """Z_m x| <r>: translations x -> x+1 and multiplier x -> r*x (r a unit mod m)."""
    return m, [[(x + 1) % m for x in range(m)], [(r * x) % m for x in range(m)]]


def _product(A, B):
    da, ga = A
    db, gb = B
    gens = [g + list(range(da, da + db)) for g in ga] + \
           [list(range(da)) + [da + x for x in g] for g in gb]
    return da + db, gens


def _order_mod(r, m):
    k, x = 1, r % m
    while x != 1 % m:
        x = (x * r) % m
        k += 1
    return k


def _group_pool(seed):
    """Candidate groups with orders in the useful range, as (order, (degree, generators)), shuffled."""
    rng = random.Random(seed)
    pool, seen = [], set()

    def add(order, G):
        deg, gens = G
        key = (deg, tuple(tuple(g) for g in gens))
        if 365 <= order <= 1100 and 2 <= deg <= 32 and len(gens) <= 8 and key not in seen:
            seen.add(key)
            pool.append((order, G))

    def psl(p):
        return p + 1, _psl_pgl(p, False)

    def pgl(p):
        return p + 1, _psl_pgl(p, True)

    bases = [(12, psl(3)), (24, pgl(3)), (6, pgl(2)), (60, psl(5)), (120, pgl(5)),
             (168, psl(7)), (336, pgl(7)), (660, psl(11)), (1092, psl(13))]
    for ob, Gb in bases:
        for k in range(2, 41):
            add(ob * k, _product(Gb, _cyclic(k)))
        for a in range(2, 8):
            for b in range(a, 8):
                add(ob * a * b, _product(_product(Gb, _cyclic(a)), _cyclic(b)))
    for m in range(3, 32):
        for r in range(2, m):
            if math.gcd(r, m) != 1:
                continue
            add(m * _order_mod(r, m), _affine(m, r))
    rng.shuffle(pool)
    return pool


def _group_args(seed, limit=40):
    pool = _group_pool(seed)
    out = []
    for _, (deg, gens) in pool[:limit]:
        out.append(";".join(",".join(str(x) for x in g) for g in gens))
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

    # Most of the case budget goes to the engine; keep a margin for compile, startup and output.
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if budget <= 1.0:
        return best
    try:
        groups = _group_args(seed)
        text = lib.run_c(C_SOURCE, [d, D, seed, budget, *groups],
                         stdin_graph=best, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
