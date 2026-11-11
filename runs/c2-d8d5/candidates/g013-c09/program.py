"""Lift-first search: exact constructions, then a C engine that searches group-invariant lifts.

The C engine exploits left-translation symmetry of semidirect-product lifts. Distances from one
representative per fiber determine validity, so each voltage evaluation costs 2p BFS passes.
"""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact and small constructions (calibration cases return immediately).
# ----------------------------------------------------------------------------

def _best_pg(d):
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C engine: group-invariant voltage lifts found by simulated annealing.
#
# A lift of a base with p vertices per side over a group G of order N:
#   A_{i,x} ~ B_{j, x*g} for each dart (i, j, g); vertex index A: i*N+x, B: (p+j)*N+x.
# Left multiplication by any h in G is an automorphism, so the whole graph has diameter
# <= D iff every representative (s, identity) reaches all vertices within D steps.
# Cost = number of (representative, vertex) pairs at distance > D. Zero means valid.
# ----------------------------------------------------------------------------

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
#define MAXP 6
#define MAXDART (MAXD * MAXP)
#define PATIENCE 4000

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

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
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

/* Number of unordered pairs at distance > D. */
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

/* Z_m x|_r Z_k: element (a,b) = a*k+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k). Identity = 0. */
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
            if (m > 1 && gcd_int(r, m) != 1) continue;
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

/* Lift state. */
static Grp GG;
static int P_, N_;
static int nd;
static int dart_i[MAXDART], dart_j[MAXDART], dart_g[MAXDART];
static int best_g[MAXDART];
static int nbr[MAXN * MAXD];
static int cntv[MAXN];
static int dist_[MAXN], queue_[MAXN];

/* Random base: d permutations summed, so every row and column of M sums to d. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (int attempt = 0; attempt < 200; attempt++) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
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

/* A voltage for a dart (i,j) that differs from every other dart with the same (i,j), among darts < upto. */
static int fresh_voltage(int upto, int skip, int i, int j) {
    for (int tries = 0; tries < 100000; tries++) {
        int g = rndint(N_);
        int clash = 0;
        for (int t = 0; t < upto; t++)
            if (t != skip && dart_i[t] == i && dart_j[t] == j && dart_g[t] == g) { clash = 1; break; }
        if (!clash) return g;
    }
    return 0;
}

static void make_darts(int p, int M[MAXP][MAXP]) {
    nd = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dart_i[nd] = i;
                dart_j[nd] = j;
                dart_g[nd] = fresh_voltage(nd, -1, i, j);
                nd++;
            }
}

/* Neighbour lists of the current lift (d-regular). */
static void build_nbr(void) {
    int p = P_, N = N_, V = 2 * p * N;
    memset(cntv, 0, sizeof(int) * V);
    for (int t = 0; t < nd; t++) {
        int i = dart_i[t], j = dart_j[t], g = dart_g[t];
        for (int x = 0; x < N; x++) {
            int a = i * N + x;
            int b = (p + j) * N + gmul(&GG, x, g);
            if (cntv[a] < MAXD) nbr[a * MAXD + cntv[a]++] = b;
            if (cntv[b] < MAXD) nbr[b * MAXD + cntv[b]++] = a;
        }
    }
}

/* Sum over representatives (s, identity) of the number of vertices at distance > D. */
static long lift_cost(void) {
    int p = P_, N = N_, V = 2 * p * N;
    long total = 0;
    for (int s = 0; s < 2 * p; s++) {
        int src = s * N;
        for (int v = 0; v < V; v++) dist_[v] = -1;
        int head = 0, tail = 0, reached = 1;
        dist_[src] = 0;
        queue_[tail++] = src;
        while (head < tail) {
            int v = queue_[head++];
            if (dist_[v] >= D) continue;
            for (int k = 0; k < d; k++) {
                int u = nbr[v * MAXD + k];
                if (dist_[u] < 0) {
                    dist_[u] = dist_[v] + 1;
                    queue_[tail++] = u;
                    reached++;
                }
            }
        }
        total += V - reached;
    }
    return total;
}

/* Annealing over voltages of the current base and group. Returns the best cost; 0 means valid.
 * On return dart_g holds the best state found. */
static long sa_run(double until) {
    double t_begin = now();
    double span = until - t_begin;
    if (span <= 0) return -1;
    build_nbr();
    long cur = lift_cost();
    long best = cur;
    memcpy(best_g, dart_g, sizeof(int) * nd);
    double frac = 0.0;
    long it = 0, last = 0;
    while (cur > 0) {
        if ((it & 15) == 0) {
            double tn = now();
            if (tn >= until) break;
            frac = (tn - t_begin) / span;
        }
        if (it - last > PATIENCE) break;
        it++;
        int t = rndint(nd);
        int old = dart_g[t];
        int ng = fresh_voltage(nd, t, dart_i[t], dart_j[t]);
        if (ng == old) continue;
        dart_g[t] = ng;
        build_nbr();
        long nc = lift_cost();
        long delta = nc - cur;
        double T = 0.04 * (double)cur * (1.0 - frac) + 0.3;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur < best) {
                best = cur;
                last = it;
                memcpy(best_g, dart_g, sizeof(int) * nd);
            }
        } else {
            dart_g[t] = old;
        }
    }
    memcpy(dart_g, best_g, sizeof(int) * nd);
    return best;
}

static void lift_driver(Graph *best, double until) {
    static Graph cand;
    static int M[MAXP][MAXP];
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        if (best->n + 2 > moore) break;
        int p = 1 + rndint(MAXP);
        long N = best->n / (2L * p) + 1;
        if (rnd01() < 0.3) N++;
        if (N < d) N = d;
        if (2L * p * N > moore || 2L * p * N > MAXN) {
            if (++fails > 2000) break;
            continue;
        }
        if (!random_group((int)N, &GG)) continue;
        P_ = p;
        N_ = (int)N;
        make_base(p, M);
        make_darts(p, M);
        double endt = now() + 2.0 + 4.0 * rnd01();
        if (endt > until) endt = until;
        if (sa_run(endt) != 0) continue;
        build_nbr();
        int V = 2 * p * N_;
        cand.n = V;
        for (int v = 0; v < V; v++) {
            cand.deg[v] = d;
            cand.side[v] = v >= p * N_;
            for (int k = 0; k < d; k++) cand.adj[v][k] = nbr[v * MAXD + k];
        }
        if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
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
    double t_end = t0 + limit * 0.92 - 0.2;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) {
        if (d < 1 || d > MAXD) d = 1;
        complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (D >= 2 && d >= 2) lift_driver(&best, t_end);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is a larger valid graph."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: C lift annealing over group-invariant voltage lifts.
    if D >= 2 and d >= 2:
        c_budget = end - time.monotonic() - 1.0
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=best, timeout=c_budget + 8)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
