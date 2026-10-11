"""Combined search: algebraic and group-lift constructions in Python, then the C engine
(semidirect-group voltage lifts plus grow-by-two annealing) starting from the best graph."""
import itertools
import math
import random
import time

import numpy as np

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
#define MAXP 4

typedef uint64_t u64;

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

typedef struct {
    int i, j, g;
} Dart;

static int d, D;
static double t_end;
static u64 rng_state = 88172645463325252ULL;
static u64 RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static u64 rnd64(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}

static int rndint(int k) { return (int)(rnd64() % (u64)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_int(int a, int b) {
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
    long s = 0, p = 1;
    int i;
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    for (i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static int has_edge(const Graph *g, int u, int v) {
    int i;
    for (i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void del_half(Graph *g, int u, int v) {
    int i;
    for (i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][g->deg[u] - 1];
            g->deg[u]--;
            return;
        }
}

static void del_edge(Graph *g, int u, int v) {
    del_half(g, u, v);
    del_half(g, v, u);
}

static void copy_graph(Graph *dst, const Graph *src) {
    int v;
    dst->n = src->n;
    for (v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

/* Number of unordered pairs at distance > D. Also fills badv[]. Zero iff diameter <= D. */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    int v, r, w;
    long total = 0;
    u64 *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(u64) * (size_t)n * (size_t)W);
    for (v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (r = 0; r < D; r++) {
        for (v = 0; v < n; v++) {
            u64 *dst = nxt + (size_t)v * W;
            const u64 *src = cur + (size_t)v * W;
            int i;
            for (w = 0; w < W; w++) dst[w] = src[w];
            for (i = 0; i < g->deg[v]; i++) {
                const u64 *s = cur + (size_t)g->adj[v][i] * W;
                for (w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        {
            u64 *t = cur;
            cur = nxt;
            nxt = t;
        }
    }
    for (v = 0; v < n; v++) {
        int c = 0;
        const u64 *s = cur + (size_t)v * W;
        for (w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        badv[v] = n - c;
        total += n - c;
    }
    return total / 2;
}

static int is_valid(const Graph *g) {
    int v, i, j;
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

static void read_start(Graph *g) {
    static int queue[MAXN];
    int n, m, v, e, s;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (v = 0; v < n; v++) {
        g->deg[v] = 0;
        g->side[v] = 255;
    }
    for (e = 0; e < m; e++) {
        int u, w;
        if (scanf("%d %d", &u, &w) != 2 || u < 0 || w < 0 || u >= n || w >= n || u == w ||
            g->deg[u] >= MAXD || g->deg[w] >= MAXD) {
            g->n = 0;
            return;
        }
        add_edge(g, u, w);
    }
    for (s = 0; s < n; s++) {
        int head = 0, tail = 0;
        if (g->side[s] != 255) continue;
        g->side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int x = queue[head++], i;
            for (i = 0; i < g->deg[x]; i++) {
                int y = g->adj[x][i];
                if (g->side[y] == 255) {
                    g->side[y] = (unsigned char)(1 - g->side[x]);
                    queue[tail++] = y;
                } else if (g->side[y] == g->side[x]) {
                    g->n = 0;
                    return;
                }
            }
        }
    }
    if (!is_valid(g)) g->n = 0;
}

static void print_graph(const Graph *g) {
    long m = 0;
    int u, i;
    for (u = 0; u < g->n; u++)
        for (i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (u = 0; u < g->n; u++)
        for (i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    int a, b;
    g->n = 2 * d;
    for (a = 0; a < g->n; a++) {
        g->deg[a] = 0;
        g->side[a] = (unsigned char)(a >= d);
    }
    for (a = 0; a < d; a++)
        for (b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* Group Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)(((long)a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

static int random_group(int N, Grp *G) {
    long count = 0;
    int m, r;
    for (m = 1; m <= N; m++) {
        int k, rmax;
        if (N % m) continue;
        k = N / m;
        rmax = m > 1 ? m : 2;
        for (r = 1; r < rmax; r++) {
            if (m > 1 && gcd_int(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) {
                G->m = m;
                G->k = k;
                G->r = r;
            }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (r = 1; r < G->k; r++) G->rp[r] = (int)((long)G->rp[r - 1] * G->r % G->m);
    return 1;
}

/* Random d-regular bipartite base multigraph on p+p vertices (sum of d permutations),
 * connected. M[i][j] = number of darts from A-vertex i to B-vertex j. */
static int make_base(int p, int M[MAXP][MAXP]) {
    int tries;
    for (tries = 0; tries < 500; tries++) {
        int t, i;
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (t = 0; t < d; t++) {
            int perm[MAXP];
            for (i = 0; i < p; i++) perm[i] = i;
            for (i = p - 1; i > 0; i--) {
                int j = rndint(i + 1), s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
            for (i = 0; i < p; i++) M[i][perm[i]]++;
        }
        {
            int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, nseen = 1;
            seen[0] = 1;
            stack[top++] = 0;
            while (top) {
                int v = stack[--top], u;
                for (u = 0; u < 2 * p; u++) {
                    int linked;
                    if (seen[u]) continue;
                    if (v < p) linked = (u >= p && M[v][u - p] > 0);
                    else linked = (u < p && M[u][v - p] > 0);
                    if (linked) {
                        seen[u] = 1;
                        nseen++;
                        stack[top++] = u;
                    }
                }
            }
            if (nseen == 2 * p) return 1;
        }
    }
    return 0;
}

static void build_lift(Graph *g, int p, int N, const Grp *G, const Dart *dt, int nd) {
    int v, t, x;
    g->n = 2 * p * N;
    for (v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= p * N);
    }
    for (t = 0; t < nd; t++)
        for (x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(G, x, dt[t].g));
}

/* A voltage not used by another dart between the same base pair. Needs N >= d. */
static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), t, clash = 0;
        for (t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) {
                clash = 1;
                break;
            }
        if (!clash) return g;
    }
}

/* Anneal voltages of a random base until the lift has diameter <= D. g holds the result. */
static int lift_try(Graph *g, int p, int N, const Grp *G, int steps) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0, i, j, c, s;
    long bad;
    if (!make_base(p, M)) return 0;
    for (i = 0; i < p; i++)
        for (j = 0; j < p; j++)
            for (c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = (c == 0) ? 0 : fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(g, p, N, G, dt, nd);
    bad = bad_pairs(g);
    for (s = 0; s < steps && bad > 0; s++) {
        int t, old;
        double T;
        long nb;
        if ((s & 15) == 0 && now() > t_end) break;
        t = rndint(nd);
        old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, G, dt, nd);
        nb = bad_pairs(g);
        T = 2.0 * (1.0 - (double)s / (double)steps) + 0.05;
        if (nb <= bad || rnd01() < exp(-(double)(nb - bad) / T)) bad = nb;
        else dt[t].g = old;
    }
    build_lift(g, p, N, G, dt, nd);
    return bad == 0;
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    long fails = 0;
    while (now() < until) {
        int r = rndint(10);
        int p = r < 4 ? 1 : (r < 7 ? 2 : (r < 9 ? 3 : 4));
        long target = best->n + 2, N;
        int steps;
        if (target > moore) return;
        N = (target + 2L * p - 1) / (2L * p) + rndint(2);
        if (best->n == 0) N = d + rndint(3);
        if (N < d || 2L * p * N > moore || 2L * p * N > MAXN) {
            if (++fails > 100000) return;
            continue;
        }
        if (!random_group((int)N, &G)) continue;
        steps = (int)(200 + 400000L / (2L * p * N));
        if (lift_try(&cand, p, (int)N, &G, steps) && cand.n > best->n && is_valid(&cand))
            copy_graph(best, &cand);
    }
}

/* Insert x (side 0) and y (side 1) with x-y and d-1 edges spliced in from best, then anneal. */
static int grow_once(const Graph *best, Graph *work, double until) {
    static int used[MAXN];
    static int stamp = 0;
    int n = best->n, x = n, y = n + 1, k = 0, tries = 0;
    long bad, it = 0;
    double T = 1.0;
    if (n + 2 > MAXN || n + 2 > moore_bound()) return 0;
    copy_graph(work, best);
    work->n = n + 2;
    work->deg[x] = 0;
    work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    stamp++;
    used[x] = stamp;
    used[y] = stamp;
    while (k < d - 1 && tries < 100000) {
        int a, b;
        tries++;
        a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        b = work->adj[a][rndint(work->deg[a])];
        if (b >= n || used[b] == stamp) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = stamp;
        used[b] = stamp;
        k++;
    }
    bad = bad_pairs(work);
    while (bad > 0) {
        int v, u, s, t, tr;
        long nb;
        if ((++it & 15) == 0 && now() > until) return 0;
        v = rndint(work->n);
        for (tr = 0; tr < 30 && badv[v] == 0; tr++) v = rndint(work->n);
        if (work->deg[v] == 0) continue;
        u = work->adj[v][rndint(work->deg[v])];
        s = rndint(work->n);
        if (s == v || work->side[s] != work->side[v] || work->deg[s] == 0) continue;
        t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
        nb = bad_pairs(work);
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
        double slice = left < 4.0 ? left : (left / 4.0 > 4.0 ? left / 4.0 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
    }
}

int main(int argc, char **argv) {
    static Graph best;
    double t0;
    long seed;
    int round;
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    seed = atol(argv[3]);
    t0 = now();
    t_end = t0 + 0.92 * atof(argv[4]);
    rng_state ^= (u64)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (round = 0; round < 10; round++) rnd64();
    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    for (round = 0; round < 3; round++) {
        double slice = (t_end - now()) / (double)(3 - round);
        if (slice <= 0) break;
        lift_search(&best, now() + 0.5 * slice);
        grow_search(&best, now() + 0.5 * slice);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''

GQ_Q_MAX = 8                  # largest q for which W(q) is built
N_CAP = 6000                  # hard cap on vertex count
ITERS_G = 1200                # annealing moves per Python lift attempt
S_LIST = (1, 2, 3)            # Python base sizes per side
RETRIES = 2                   # annealing attempts per lift order
EXTEND_SLICE = 0.5            # seconds per greedy extension run
EXTEND_TRIES = 6              # randomized greedy restarts
POOL_KEEP = 8                 # candidates kept in the pool
PY_FRAC = 0.3                 # share of time_limit for Python constructions
C_FRAC = 0.9                  # share of time_limit the whole run should finish by
C_OVERHEAD = 3.0              # seconds reserved for compile and wrap-up


# ---------------------------------------------------------------- algebraic bases

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q): degree q+1, diameter 4."""
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
    """W(q) for the largest prime power q <= min(d-1, GQ_Q_MAX)."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _trivial(d, D):
    """Optimal or near-optimal graphs for small d or D; always valid for d >= 1, D >= 1."""
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]
    return lib.haar_graph(d, range(d))   # K_{d,d}, optimal for D = 2


# ---------------------------------------------------------------- extension helpers

def _two_colour(n, edges):
    adj = lib.adjacency(n, edges)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _extend(n, edges, d, D, rng, deadline):
    """Greedily add vertices, each attached to a set cover of radius-(D-1) balls of the current graph."""
    edges = list(edges)
    if D < 2 or n == 0:
        return n, edges
    color = _two_colour(n, edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1

    while time.monotonic() < deadline:
        full = (1 << n) - 1
        balls = lib._balls(n, edges, D - 1)
        grown = False
        order = [0, 1] if rng.random() < 0.5 else [1, 0]
        for c in order:
            cand = [u for u in range(n) if color[u] == 1 - c and deg[u] < d]
            rng.shuffle(cand)
            covered, chosen = 0, []
            while covered != full and len(chosen) < d and cand:
                best_u, best_gain = -1, 0
                for u in cand:
                    g = (balls[u] & ~covered).bit_count()
                    if g > best_gain:
                        best_u, best_gain = u, g
                if best_u < 0:
                    break
                chosen.append(best_u)
                covered |= balls[best_u]
                cand.remove(best_u)
            if covered == full and chosen:
                x = n
                n += 1
                color.append(c)
                deg.append(len(chosen))
                for u in chosen:
                    edges.append((u, x))
                    deg[u] += 1
                grown = True
                break
        if not grown:
            break
    return n, edges


def _extend_best(n, edges, d, D, rng, deadline, tries=EXTEND_TRIES):
    best = (n, list(edges))
    for t in range(tries):
        now = time.monotonic()
        if now >= deadline:
            break
        per = now + (deadline - now) / (tries - t)
        cand = _extend(n, edges, d, D, rng, per)
        if cand[0] > best[0]:
            best = cand
    return best


def _augment(n, edges, d, seed):
    """Add edges between opposite colour classes using spare degree."""
    rng = random.Random(seed + 7)
    color = _two_colour(n, edges)
    deg = [0] * n
    adj = [set() for _ in range(n)]
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        adj[u].add(v)
        adj[v].add(u)
    side0 = [u for u in range(n) if color[u] == 0]
    side1 = [v for v in range(n) if color[v] == 1]
    new_edges = list(edges)
    for _ in range(3):
        us = [u for u in side0 if deg[u] < d]
        rng.shuffle(us)
        for u in us:
            if deg[u] >= d:
                continue
            cands = [v for v in side1 if deg[v] < d and v not in adj[u]]
            if not cands:
                continue
            v = rng.choice(cands)
            adj[u].add(v)
            adj[v].add(u)
            deg[u] += 1
            deg[v] += 1
            new_edges.append((u, v))
    return n, new_edges


def _grow_alt(n, edges, d, D, rng, deadline):
    """Alternate spare-degree augmentation and greedy cover extension."""
    for _ in range(4):
        if time.monotonic() >= deadline:
            break
        _, e2 = _augment(n, edges, d, rng.randrange(1 << 30))
        n2, e3 = _extend(n, e2, d, D, rng, deadline)
        if n2 == n and len(e2) == len(edges):
            break
        n, edges = n2, e3
    return n, edges


def _finish(cands, d, D):
    """Largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


# ---------------------------------------------------------------- semidirect groups

def _presentations(M, rng, limit):
    """Random semidirect presentations (m, k, r) of groups of order M (k <= 8)."""
    out = []
    ks = [k for k in range(1, 9) if M % k == 0]
    rng.shuffle(ks)
    for k in ks:
        m = M // k
        if m == 1:
            out.append((1, k, 0))
        elif k == 1:
            out.append((m, 1, 1))
        else:
            cands = [m - 1] if k == 2 else []
            for _ in range(40):
                r = rng.randrange(1, m)
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                    cands.append(r)
            if cands:
                out.append((m, k, rng.choice(cands)))
        if len(out) >= limit:
            break
    return out


class _Grp:
    """Semidirect group Z_m x|_r Z_k with vectorised right multiplication."""

    def __init__(self, m, k, r):
        self.m, self.k, self.r = m, k, r
        self.M = m * k
        self.powers = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
        X = np.arange(self.M, dtype=np.int64)
        a, b = X // k, X % k
        nb = (-b) % k
        c = (-self.powers[nb] * a) % m
        self.inv = c * k + nb

    def mul(self, X, g):
        """Return X * g elementwise (X an array, g a scalar element)."""
        a1, b1 = X // self.k, X % self.k
        a2, b2 = g // self.k, g % self.k
        a = (a1 + self.powers[b1] * a2) % self.m
        b = (b1 + b2) % self.k
        return a * self.k + b


def _gcol(nbr, kk, sig, sinv, G, s, M, grp):
    """Fill neighbour column kk for every lift vertex."""
    Y = np.arange(M, dtype=np.int64)
    for i in range(s):
        j = int(sig[kk, i])
        nbr[i * M:(i + 1) * M, kk] = s * M + j * M + grp.mul(Y, int(G[kk, i]))
    for j in range(s):
        i = int(sinv[kk, j])
        gi = int(grp.inv[int(G[kk, i])])
        nbr[s * M + j * M: s * M + (j + 1) * M, kk] = i * M + grp.mul(Y, gi)


def _swap(P, Pinv, k, a, b):
    P[k, a], P[k, b] = P[k, b], P[k, a]
    Pinv[k, P[k, a]] = a
    Pinv[k, P[k, b]] = b


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D."""
    n = nbr.shape[0]
    S = len(sources)
    R = np.zeros((S, n), dtype=bool)
    R[np.arange(S), sources] = True
    for _ in range(D):
        Mx = R.copy()
        for k in range(nbr.shape[1]):
            Mx |= R[:, nbr[:, k]]
        if np.array_equal(Mx, R):
            break
        R = Mx
    return int(S * n - np.count_nonzero(R))


def _lift_anneal(s, M, grp, d, D, rng, deadline, iters):
    """Anneal a group lift until diameter <= D. Returns neighbour table or None."""
    n = 2 * s * M
    sig = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    sinv = np.zeros_like(sig)
    for kk in range(d):
        for i in range(s):
            sinv[kk, sig[kk, i]] = i
    G = np.array([[rng.randrange(M) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    nbr = np.empty((n, d), dtype=np.int64)
    for kk in range(d):
        _gcol(nbr, kk, sig, sinv, G, s, M, grp)
    sources = [i * M for i in range(s)] + [s * M + j * M for j in range(s)]
    cur = _cost(nbr, sources, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / iters) + 0.05
        if s == 1 or rng.random() < 0.6:
            kk, i = rng.randrange(d), rng.randrange(s)
            old = int(G[kk, i])
            new = rng.randrange(M)
            if new == old:
                continue
            G[kk, i] = new
            _gcol(nbr, kk, sig, sinv, G, s, M, grp)
            c = _cost(nbr, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                G[kk, i] = old
                _gcol(nbr, kk, sig, sinv, G, s, M, grp)
        else:
            kk = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(sig, sinv, kk, a, b)
            _gcol(nbr, kk, sig, sinv, G, s, M, grp)
            c = _cost(nbr, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                _swap(sig, sinv, kk, a, b)
                _gcol(nbr, kk, sig, sinv, G, s, M, grp)
    return nbr if cur == 0 else None


def _nbr_edges(nbr):
    """Deduplicated edge list from a neighbour table."""
    n, d = nbr.shape
    xs = np.repeat(np.arange(n, dtype=np.int64), d)
    ys = nbr.reshape(-1)
    lo = np.minimum(xs, ys)
    hi = np.maximum(xs, ys)
    keys = np.unique(lo * n + hi)
    return [(int(x // n), int(x % n)) for x in keys.tolist()]


def _lift_try(s, M, d, D, rng, deadline):
    pres = _presentations(M, rng, 4)
    for _ in range(RETRIES):
        if time.monotonic() >= deadline:
            break
        m, k, r = rng.choice(pres)
        grp = _Grp(m, k, r)
        nbr = _lift_anneal(s, M, grp, d, D, rng, deadline, ITERS_G)
        if nbr is not None:
            return _nbr_edges(nbr)
    return None


def _lift_search(s, d, D, rng, deadline, cap):
    """Doubling then bisection over group order M for base size s. Returns (n, edges) or None."""
    best = None
    lo, hi = 0, None
    M = max(2, d)
    while time.monotonic() < deadline:
        if 2 * s * M > cap:
            if lo == 0:
                break
            hi = M
        else:
            edges = _lift_try(s, M, d, D, rng, deadline)
            if edges is not None:
                lo = M
                best = (2 * s * M, edges)
            elif lo == 0:
                M *= 2
                continue
            else:
                hi = M
        if hi is None:
            M = 2 * M
        else:
            if hi - lo <= max(1, lo // 16):
                break
            M = (lo + hi) // 2
    return best


# ---------------------------------------------------------------- Python pipeline

def _python_best(d, D, seed, deadline):
    rng = random.Random(seed)
    cap = min(N_CAP, lib._moore_bound(d, D))
    pool = [lib.haar_graph(d, range(d))]

    def add(c):
        if c is None:
            return
        pool.append(c)
        pool.sort(key=lambda item: -item[0])
        del pool[POOL_KEEP:]

    if D == 3:
        base = _pg_base(d)
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                add(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
    else:
        base = _best_gq(d)

    if base is not None:
        add(base)
        start = time.monotonic()
        ext_end = min(deadline, start + 0.35 * max(0.0, deadline - start))
        aug = _augment(base[0], base[1], d, seed)
        add(aug)
        for h in (base, aug):
            now = time.monotonic()
            if now >= ext_end:
                break
            add(_extend_best(h[0], h[1], d, D, rng, min(ext_end, now + EXTEND_SLICE)))
        now = time.monotonic()
        if now < ext_end:
            add(_grow_alt(aug[0], aug[1], d, D, rng, min(ext_end, now + EXTEND_SLICE)))

    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(S_LIST) - idx)
        try:
            add(_lift_search(s, d, D, rng, slice_end, cap))
        except Exception:
            pass

    if pool:
        top = pool[0]
        try:
            add(_extend_best(top[0], top[1], d, D, rng, deadline, tries=2))
        except Exception:
            pass
    return _finish(pool, d, D)


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 3 or D < 3:
        triv = _trivial(d, D)
        if lib.is_valid(triv[0], triv[1], d, D):
            return triv
        return lib.haar_graph(d, range(d)) if d >= 1 else (1, [])

    # Exact or Moore-type algebraic graphs need no search.
    if D == 3 and lib.is_prime_power(d - 1):
        return _finish([lib.projective_plane_incidence(d - 1)], d, D)
    if D == 4 and lib.is_prime_power(d - 1) and d - 1 <= GQ_Q_MAX:
        return _finish([_gq_w(d - 1)], d, D)

    fallback = lib.haar_graph(d, range(d))
    deadline = t0 + PY_FRAC * time_limit
    try:
        best = _python_best(d, D, seed, deadline)
    except Exception:
        best = fallback
    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback

    # C engine: lifts and grow-by-two annealing from the best Python graph.
    budget = C_FRAC * time_limit - (time.monotonic() - t0) - C_OVERHEAD
    if budget >= 2.0 and d <= 32:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 6.0)
            n2, e2 = lib.parse_graph_text(text)
            if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)
        except Exception:
            pass
    return best
