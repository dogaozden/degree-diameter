"""Group-lift search for bipartite degree-diameter graphs.

Python builds the best algebraic start (PG(2,q), W(q), Araujo-Pardo-Lopez, or K_{d,d}) and
validates it with lib.is_valid. It then supplies a pool of explicit finite groups, given as
generating permutations of their left regular representations: cyclic, dihedral, semidirect,
direct products, small permutation and matrix groups, and random permutation groups.

The C engine forms each group's multiplication table and searches voltage lifts over these
groups. A lift over a group G with p base vertices per side has 2pG vertices. Its diameter is
checked by BFS from the 2p fibre representatives only, since the group acts regularly on each
fibre. Remaining time grows the best graph by two vertices at a time, with saturation after
each accepted step.
"""
import itertools
import math
import random
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search: voltage lifts over supplied finite groups, then growth.
 * Usage:  prog d D seed time_limit [group_spec ...]   < start_graph
 * group_spec: "N:p1:p2:...:pk", where each pi is a permutation of 0..N-1 written as N
 *             comma-separated integers. The pi generate a group G acting regularly (left regular
 *             representation). The program closes them into a multiplication table, identity 0.
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
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
#define MAXGN 128
#define MAXGR 64
#define HSZ 1024

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
    for (int i = 0; i < D && s < 100000000L; i++) {
        s += p;
        p *= (d - 1);
        if (p > 1000000000L) p = 1000000000L;
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

/* Number of unordered vertex pairs at distance > D (bitset all-pairs). */
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

/* Adding an A-B edge between vertices with spare degree never increases a distance. */
static int saturate(Graph *g) {
    int added = 0;
    for (int a = 0; a < g->n; a++) {
        if (g->side[a] != 0 || g->deg[a] >= d) continue;
        for (int b = 0; b < g->n && g->deg[a] < d; b++) {
            if (g->side[b] != 1 || g->deg[b] >= d || has_edge(g, a, b)) continue;
            add_edge(g, a, b);
            added++;
        }
    }
    return added;
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

/* ---------------------------------------------------------------- groups */

static int gcount = 0;
static int gsize[MAXGR];
static unsigned char gtab[MAXGR][MAXGN * MAXGN];

static unsigned char cl_elem[MAXGN][MAXGN];
static unsigned char cl_gen[8][MAXGN];
static int cl_ngen, cl_deg, cl_nel;
static int cl_htab[HSZ];

static unsigned cl_hash(const unsigned char *p) {
    unsigned h = 2166136261u;
    for (int i = 0; i < cl_deg; i++) {
        h ^= p[i];
        h *= 16777619u;
    }
    return h;
}

/* Index of permutation p among the closure elements; adds it when new (isnew = 1). */
static int cl_intern(const unsigned char *p, int *isnew) {
    unsigned h = cl_hash(p) & (HSZ - 1);
    for (;;) {
        int e = cl_htab[h];
        if (!e) break;
        if (memcmp(cl_elem[e - 1], p, cl_deg) == 0) { *isnew = 0; return e - 1; }
        h = (h + 1) & (HSZ - 1);
    }
    if (cl_nel >= MAXGN) return -1;
    memcpy(cl_elem[cl_nel], p, cl_deg);
    cl_htab[h] = cl_nel + 1;
    *isnew = 1;
    return cl_nel++;
}

static int is_perm(const unsigned char *p, int deg) {
    unsigned char seen[MAXGN];
    memset(seen, 0, sizeof seen);
    for (int i = 0; i < deg; i++) {
        if (seen[p[i]]) return 0;
        seen[p[i]] = 1;
    }
    return 1;
}

/* Parse one "N:p1:...:pk" spec, close the generated group, store its table. */
static int parse_spec(const char *s) {
    char *end;
    long deg = strtol(s, &end, 10);
    if (end == s || deg < 2 || deg > MAXGN || gcount >= MAXGR) return 0;
    s = end;
    cl_deg = (int)deg;
    cl_ngen = 0;
    while (*s == ':') {
        s++;
        if (cl_ngen >= 8) return 0;
        for (int i = 0; i < cl_deg; i++) {
            long v = strtol(s, &end, 10);
            if (end == s || v < 0 || v >= cl_deg) return 0;
            cl_gen[cl_ngen][i] = (unsigned char)v;
            s = end;
            if (i + 1 < cl_deg) {
                if (*s != ',') return 0;
                s++;
            }
        }
        if (!is_perm(cl_gen[cl_ngen], cl_deg)) return 0;
        cl_ngen++;
    }
    if (cl_ngen == 0) return 0;

    memset(cl_htab, 0, sizeof cl_htab);
    cl_nel = 0;
    unsigned char id[MAXGN], y[MAXGN];
    for (int i = 0; i < cl_deg; i++) id[i] = (unsigned char)i;
    int isnew = 0;
    if (cl_intern(id, &isnew) < 0) return 0;
    for (int x = 0; x < cl_nel; x++)
        for (int g = 0; g < cl_ngen; g++) {
            for (int i = 0; i < cl_deg; i++) y[i] = cl_gen[g][cl_elem[x][i]];
            if (cl_intern(y, &isnew) < 0) return 0;
        }
    int N = cl_nel;
    if (N < 2) return 0;
    /* Multiplication table: element x times z is the composition x after z. */
    for (int x = 0; x < N; x++)
        for (int z = 0; z < N; z++) {
            for (int i = 0; i < cl_deg; i++) y[i] = cl_elem[x][cl_elem[z][i]];
            int r = cl_intern(y, &isnew);
            if (r < 0 || isnew) return 0;
            gtab[gcount][x * N + z] = (unsigned char)r;
        }
    gsize[gcount++] = N;
    return 1;
}

/* ---------------------------------------------------------- voltage lifts */

typedef struct { int i, j, g; } Dart;

/* Random d-regular connected base multigraph on p + p vertices. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
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
                if (linked) {
                    seen[u] = 1;
                    nseen++;
                    stack[top++] = u;
                }
            }
        }
        if (nseen == 2 * p) return;
    }
}

/* Vertex layout: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x.
 * Dart (i, j, g) joins (i,x) to (j, x*g) for every x. */
static void build_lift(Graph *g, int p, int N, const unsigned char *tab, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + tab[x * N + dt[t].g]);
}

/* A voltage not already used by another dart on the same (i, j) pair; -1 if none found. */
static int fresh_volt(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (int tries = 0; tries < 1000; tries++) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
    return -1;
}

static int dist_buf[MAXN], queue_buf[MAXN];

/* Orbit-reduced objective: BFS from the 2p fibre representatives (element 0 of each fibre).
 * Returns the number of (representative, vertex) pairs at distance > D; zero means diameter <= D. */
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

/* Anneal the voltages of one random base multigraph over the group. */
static int glift_try(Graph *g, int p, int N, const unsigned char *tab, int steps, double until) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            if (M[i][j] > N) return 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                int v = fresh_volt(dt, nd, -1, i, j, N);
                if (v < 0) return 0;
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = v;
                nd++;
            }
    build_lift(g, p, N, tab, dt, nd);
    long bad = orbit_bad(g, p, N);
    double T = 1.0;
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        int nv = fresh_volt(dt, nd, t, dt[t].i, dt[t].j, N);
        if (nv < 0) continue;
        dt[t].g = nv;
        build_lift(g, p, N, tab, dt, nd);
        long nb = orbit_bad(g, p, N);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else dt[t].g = old;
        T *= 0.9995;
        if (T < 0.2) T = 1.0;
    }
    build_lift(g, p, N, tab, dt, nd);
    return bad == 0;
}

/* Repeatedly pick a feasible (group, p) whose lift beats the current best, and try to find it. */
static void group_search(Graph *best, double until) {
    static Graph cand;
    if (d < 2) return;
    long moore = moore_bound();
    static int fi[MAXGR * MAXP], fp[MAXGR * MAXP];
    while (now() < until) {
        int nf = 0;
        for (int gi = 0; gi < gcount; gi++)
            for (int p = 1; p <= MAXP; p++) {
                long size = 2L * p * gsize[gi];
                if (size > best->n && size <= moore && size <= MAXN && gsize[gi] >= d) {
                    fi[nf] = gi;
                    fp[nf] = p;
                    nf++;
                }
            }
        if (nf == 0) return;
        int k = rndint(nf);
        int gi = fi[k], p = fp[k];
        for (int a = 0; a < 4 && now() < until; a++) {
            if (glift_try(&cand, p, gsize[gi], gtab[gi], 3000, until) && is_valid(&cand) &&
                cand.n > best->n) {
                saturate(&cand);
                copy_graph(best, &cand);
                break;
            }
        }
    }
}

/* ------------------------------------------------------------ growth */

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
    if (!is_valid(work)) return 0;
    saturate(work);
    return 1;
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
        fprintf(stderr, "usage: %s d D seed time_limit [group_specs...] < start_graph\n", argv[0]);
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

    for (int a = 5; a < argc; a++) (void)parse_spec(argv[a]);

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) {
        complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    if (best.n > 0) {
        saturate(&best);
        if (!is_valid(&best)) best.n = 0;
    }

    long moore = moore_bound();
    if (D >= 2 && best.n < moore) {
        group_search(&best, t0 + (t_end - t0) * 0.8);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ------------------------------------------------------------ constructions

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


# ------------------------------------------------------------ group pool
# A group is (N, tab, gens): tab[x][y] = index of x*y (identity 0), gens = generator indices.

def _pmul(a, b):
    """Composition of permutations: (a o b)[i] = a[b[i]]."""
    return tuple(a[t] for t in b)


def _mat_mul(p):
    """Multiplication of 2x2 matrices (a, b, c, d) over GF(p)."""
    def mul(A, B):
        a, b, c, d_ = A
        e, f, g, h = B
        return ((a * e + b * g) % p, (a * f + b * h) % p,
                (c * e + d_ * g) % p, (c * f + d_ * h) % p)
    return mul


def _closure(gens, mul, ident, cap):
    """Group generated by gens (identity first); None if the order exceeds cap."""
    elems = [ident]
    index = {ident: 0}
    i = 0
    while i < len(elems):
        x = elems[i]
        i += 1
        for g in gens:
            y = mul(g, x)
            if y not in index:
                if len(elems) >= cap:
                    return None
                index[y] = len(elems)
                elems.append(y)
    tab = [[index[mul(a, b)] for b in elems] for a in elems]
    return len(elems), tab, [index[g] for g in gens]


def _cyc(m):
    tab = [[(x + y) % m for y in range(m)] for x in range(m)]
    return m, tab, [1]


def _semi(m, k, r):
    """Z_m x|_r Z_k; element (a, b) is coded a*k + b."""
    N, mul, _ = lib.semidirect_group(m, k, r)
    tab = [[mul(x, y) for y in range(N)] for x in range(N)]
    gens = ([k] if m > 1 else []) + ([1] if k > 1 else [])
    return N, tab, gens


def _direct(A, B):
    na, ta, ga = A
    nb, tb, gb = B
    N = na * nb
    tab = [[ta[x // nb][y // nb] * nb + tb[x % nb][y % nb] for y in range(N)]
           for x in range(N)]
    gens = [g * nb for g in ga] + list(gb)
    return N, tab, gens


def _library(hi, rng):
    items = []

    def add(name, g):
        if g is not None and 2 <= g[0] <= hi:
            items.append((name, g))

    for m in range(2, 9):
        add("Z%d" % m, _cyc(m))
    for k in range(3, 41):
        if 2 * k <= hi:
            add("D%d" % k, _semi(k, 2, k - 1))
    specs = []
    for m in range(3, hi + 1):
        for k in range(2, hi // m + 1):
            for r in range(2, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    specs.append((m, k, r))
    for m, k, r in rng.sample(specs, min(15, len(specs))):
        add("Z%dx%dr%d" % (m, k, r), _semi(m, k, r))

    perm_gens = [
        ("S4", [(1, 0, 2, 3), (1, 2, 3, 0)]),
        ("A4", [(1, 2, 0, 3), (1, 0, 3, 2)]),
        ("S5", [(1, 0, 2, 3, 4), (1, 2, 3, 4, 0)]),
        ("A5", [(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)]),
        ("Z2wrZ3", [(1, 0, 2, 3, 4, 5), (2, 3, 4, 5, 0, 1)]),
        ("Z2wrS3", [(1, 0, 2, 3, 4, 5), (2, 3, 4, 5, 0, 1), (0, 1, 4, 5, 2, 3)]),
        ("Z2wrZ4", [(1, 0, 2, 3, 4, 5, 6, 7), (2, 3, 4, 5, 6, 7, 0, 1)]),
        ("Z4wrZ2", [(1, 2, 3, 0, 4, 5, 6, 7), (4, 5, 6, 7, 0, 1, 2, 3)]),
        ("Z3wrZ2", [(1, 2, 0, 3, 4, 5), (3, 4, 5, 0, 1, 2)]),
        ("Z3wrZ3", [(1, 2, 0, 3, 4, 5, 6, 7, 8), (3, 4, 5, 6, 7, 8, 0, 1, 2)]),
    ]
    for name, gens in perm_gens:
        add(name, _closure(gens, _pmul, tuple(range(len(gens[0]))), hi))

    mat_gens = [
        ("SL23", 3, [(1, 1, 0, 1), (0, 2, 1, 0)]),
        ("GL23", 3, [(1, 1, 0, 1), (0, 1, 1, 0), (2, 0, 0, 1)]),
        ("SL25", 5, [(1, 1, 0, 1), (0, 4, 1, 0)]),
    ]
    for name, p, gens in mat_gens:
        add(name, _closure(gens, _mat_mul(p), (1, 0, 0, 1), hi))
    return items


def _random_perm_groups(rng, lo, hi, count, deadline):
    out = []
    tries = 0
    while len(out) < count and tries < 3000 and time.monotonic() < deadline:
        tries += 1
        deg = rng.choice((6, 7, 8))
        gens = []
        for _ in range(2):
            p = list(range(deg))
            rng.shuffle(p)
            gens.append(tuple(p))
        g = _closure(gens, _pmul, tuple(range(deg)), hi)
        if g is not None and g[0] >= lo:
            out.append(g)
    return out


def _group_pool(d, lo, hi, seed, deadline):
    rng = random.Random(seed * 1000003 + d * 7919 + hi)
    base = _library(hi, rng)
    pool = [(name, g) for name, g in base if g[0] >= lo]
    pairs = [(i, j) for i in range(len(base)) for j in range(i, len(base))
             if lo <= base[i][1][0] * base[j][1][0] <= hi]
    rng.shuffle(pairs)
    for i, j in pairs[:30]:
        pool.append((base[i][0] + "x" + base[j][0], _direct(base[i][1], base[j][1])))
    for g in _random_perm_groups(rng, lo, hi, 12, deadline):
        pool.append(("rand", g))
    rng.shuffle(pool)
    return pool[:40]


def _spec(g):
    """Regular-representation spec: N, then one permutation per generator (y -> x*y)."""
    N, tab, gens = g
    parts = [str(N)]
    for x in gens:
        parts.append(",".join(str(v) for v in tab[x]))
    return ":".join(parts)


# ------------------------------------------------------------ build

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

    moore = lib.moore_bound(d, D)
    if d > 31 or best[0] >= moore:
        return best

    lo = max(d, 12)
    hi = min(120, moore // 2)
    if hi < lo:
        return best

    pool = _group_pool(d, lo, hi, seed, deadline=time.monotonic() + min(3.0, 0.06 * time_limit))
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 1.0 or not pool:
        return best

    args = [d, D, seed, round(budget, 2)] + [_spec(g) for _, g in pool]
    try:
        text = lib.run_c(C_SOURCE, args, stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
