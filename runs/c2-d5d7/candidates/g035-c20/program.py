"""Mixed-fibre voltage-lift annealing for the d=5, D=7 target.

Replaces the bi-Cayley hill climb with a different construction: lifts of random d-regular
bipartite base multigraphs on p+p vertices (p = 1..5 fibres) over semidirect products Z_m x| Z_k.
The C engine evaluates the orbit-reduced diameter objective implicitly (no graph is built per
step), anneals the voltages, and climbs the order ladder from the current best. Every success is
verified by the all-pairs check in C and again in Python with lib.is_valid. Starts are the
split Cayley hexagon H(q) and other algebraic graphs, so every case returns a valid graph.
"""
import time

import itertools

import numpy as np

import lib

C_SOURCE = r'''
/* Mixed-fibre voltage lift annealing for bipartite degree-diameter graphs.
 * Usage:   prog d D seed time_limit   < start_graph
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
#define MAXP 5
#define MAXH 2048
#define MAXDART (MAXD * MAXP)
#define ANNEAL_STEPS 6000
#define ATTEMPTS 4
#define GROUP_TRIES 4

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int i, j, g; } Dart;

typedef struct { int m, k, r; int rp[MAXH]; } Grp;

static int d, D;
static double g_until;
static Graph best, cand;

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

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* All-pairs check by bitsets: number of unordered pairs at distance > D. */
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

/* ---------------- groups: Z_m x|_r Z_k, element a*k+b ---------------- */

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)(((long)a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Uniformly random admissible semidirect product of order N (reservoir sampling). */
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

/* Prefer a non-abelian choice when one is sampled quickly. */
static int pick_group(int N, Grp *G) {
    for (int t = 0; t < 8; t++) {
        if (!random_group(N, G)) return 0;
        if (G->m > 1 && G->k > 1 && G->r != 1) return 1;
    }
    return 1;
}

static int MTAB[MAXH * MAXH];
static int INVT[MAXH];

static void setup_group(int N, const Grp *G) {
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            MTAB[x * N + y] = gmul(G, x, y);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MTAB[x * N + y] == 0) { INVT[x] = y; break; }
}

/* ---------------- base multigraphs and darts ---------------- */

static Dart DT[MAXDART];
static int DT_ND;
static int LA[MAXP][MAXD], LB[MAXP][MAXD], CA[MAXP], CB[MAXP];

/* Random d-regular bipartite base multigraph on p+p vertices, connected. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
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
                int linked;
                if (v < p) linked = (u >= p) && M[v][u - p];
                else linked = (u < p) && M[u][v - p];
                if (linked) { seen[u] = 1; nseen++; stack[top++] = u; }
            }
        }
        if (nseen == 2 * p) return;
    }
}

static void index_darts(int p) {
    for (int i = 0; i < p; i++) { CA[i] = 0; CB[i] = 0; }
    for (int t = 0; t < DT_ND; t++) {
        int i = DT[t].i, j = DT[t].j;
        LA[i][CA[i]++] = t;
        LB[j][CB[j]++] = t;
    }
}

/* True if voltage g on dart t clashes with another dart on the same fibre pair. */
static int clashes(int t, int g) {
    for (int u = 0; u < DT_ND; u++)
        if (u != t && DT[u].g == g && DT[u].i == DT[t].i && DT[u].j == DT[t].j) return 1;
    return 0;
}

static void init_darts(int p, int N) {
    int M[MAXP][MAXP];
    make_base(p, M);
    DT_ND = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                DT[DT_ND].i = i;
                DT[DT_ND].j = j;
                DT[DT_ND].g = -1;
                DT_ND++;
            }
    for (int t = 0; t < DT_ND; t++) {
        if (p == 1 && t == 0) { DT[t].g = 0; continue; }
        int g;
        do { g = rndint(N); } while (clashes(t, g));
        DT[t].g = g;
    }
    index_darts(p);
}

/* ---------------- implicit orbit-reduced objective ----------------
 * Lift vertices: A-fibre i, element x -> i*N + x; B-fibre j, element y -> (p+j)*N + y.
 * Dart (i, j, g): A(i,x) -- B(j, x*g). Left multiplication is an automorphism, so one
 * source per fibre suffices. Returns the number of (source, vertex) pairs at distance > D. */

static int dist_l[MAXN], mark_l[MAXN], queue_l[MAXN];
static int stamp_l = 0;

static long orbit_eval(int p, int N) {
    int half = p * N, V = 2 * half;
    long total = 0;
    for (int s = 0; s < 2 * p; s++) {
        int src = s * N;
        stamp_l++;
        int head = 0, tail = 0;
        mark_l[src] = stamp_l;
        dist_l[src] = 0;
        queue_l[tail++] = src;
        while (head < tail) {
            int v = queue_l[head++];
            int dv = dist_l[v];
            if (dv >= D) continue;
            if (v < half) {
                int i = v / N, x = v - i * N;
                for (int k = 0; k < d; k++) {
                    int t = LA[i][k];
                    int u = half + DT[t].j * N + MTAB[x * N + DT[t].g];
                    if (mark_l[u] != stamp_l) {
                        mark_l[u] = stamp_l;
                        dist_l[u] = dv + 1;
                        queue_l[tail++] = u;
                    }
                }
            } else {
                int w = v - half;
                int j = w / N, y = w - j * N;
                for (int k = 0; k < d; k++) {
                    int t = LB[j][k];
                    int u = DT[t].i * N + MTAB[y * N + INVT[DT[t].g]];
                    if (mark_l[u] != stamp_l) {
                        mark_l[u] = stamp_l;
                        dist_l[u] = dv + 1;
                        queue_l[tail++] = u;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

/* Annealed voltage search on the current darts. Returns 0 on success (DT is then valid). */
static long anneal(int p, int N, long steps) {
    long bad = orbit_eval(p, N);
    double T = 2.0;
    const double alpha = pow(0.1, 1.0 / (double)steps);
    for (long s = 0; s < steps && bad > 0; s++) {
        if ((s & 255) == 0 && now() > g_until) break;
        int t = rndint(DT_ND);
        if (p == 1 && t == 0) continue;
        int old = DT[t].g, ng;
        do { ng = rndint(N); } while (clashes(t, ng));
        DT[t].g = ng;
        long nb = orbit_eval(p, N);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else DT[t].g = old;
        T *= alpha;
        if (T < 0.2) T = 0.2;
    }
    return bad;
}

static void build_lift_graph(Graph *g, int p, int N) {
    int half = p * N;
    g->n = 2 * half;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= half; }
    for (int t = 0; t < DT_ND; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, DT[t].i * N + x, half + DT[t].j * N + MTAB[x * N + DT[t].g]);
}

/* Order ladder: each success raises the bar to the new order. */
static void lift_search(void) {
    static Grp G;
    long moore = moore_bound();
    int idle = 0;
    while (now() < g_until) {
        int r = rndint(100);
        int p = r < 40 ? 1 : r < 62 ? 2 : r < 78 ? 3 : r < 90 ? 4 : 5;
        long twoP = 2L * p;
        long Nlo = best.n / twoP + 1;
        if (Nlo < d) Nlo = d;
        long Nhi = moore / twoP;
        if (Nhi > MAXN / twoP) Nhi = MAXN / twoP;
        if (Nhi > MAXH) Nhi = MAXH;
        if (Nlo > Nhi) {
            if (++idle > 2000) return;
            continue;
        }
        idle = 0;
        long span = Nhi - Nlo + 1;
        if (span > 400) span = 400;
        double u = rnd01();
        long N = Nlo + (long)(u * sqrt(u) * (double)span);
        if (N > Nhi) N = Nhi;
        int found = 0;
        for (int grp = 0; grp < GROUP_TRIES && !found && now() < g_until; grp++) {
            if (!pick_group((int)N, &G)) break;
            setup_group((int)N, &G);
            for (int att = 0; att < ATTEMPTS && !found && now() < g_until; att++) {
                init_darts(p, (int)N);
                if (anneal(p, (int)N, ANNEAL_STEPS) == 0) {
                    build_lift_graph(&cand, p, (int)N);
                    if (cand.n > best.n && is_valid(&cand)) {
                        best = cand;
                        found = 1;
                    }
                }
            }
        }
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
    g_until = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (D >= 2 && d >= 2 && best.n < moore_bound()) lift_search();

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


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
    Points: points of the quadric X0X4 + X1X5 + X2X6 = X3^2. Lines: quadric lines whose Grassmann
    coordinates satisfy p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31.
    Characteristic 2, so signs are irrelevant. The caller validates the result with lib.is_valid.
    """
    F = lib.GF(q)
    MT, AT = F.mul_table, F.add_table
    pts = []
    for v in itertools.product(range(q), repeat=7):
        if any(v) and next(c for c in v if c) == 1:
            s = AT[AT[MT[v[0], v[4]], MT[v[1], v[5]]], AT[MT[v[2], v[6]], MT[v[3], v[3]]]]
            if s == 0:
                pts.append(tuple(int(c) for c in v))
    N = len(pts)
    index = {v: i for i, v in enumerate(pts)}
    P = np.array(pts, dtype=np.int64)
    lines = set()
    for i in range(N - 1):
        x = P[i]
        Y = P[i + 1:]

        def pp(a, b):
            """Grassmann coordinate p_ab = x_a y_b - x_b y_a, for all y in Y."""
            return AT[MT[x[a], Y[:, b]], MT[x[b], Y[:, a]]]

        # Collinearity on the quadric: polar form B(x, y) = 0 (char 2 has no 2*x3*y3 term).
        s = np.zeros(len(Y), dtype=np.int64)
        for a, b in ((0, 4), (1, 5), (2, 6)):
            s = AT[s, AT[MT[x[a], Y[:, b]], MT[Y[:, a], x[b]]]]
        ok = (s == 0)
        ok &= pp(1, 2) == pp(3, 4)
        ok &= pp(5, 4) == pp(3, 2)
        ok &= pp(2, 0) == pp(3, 5)
        ok &= pp(6, 5) == pp(3, 0)
        ok &= pp(0, 1) == pp(3, 6)
        ok &= pp(4, 6) == pp(3, 1)
        for jj in np.nonzero(ok)[0]:
            y = Y[jj]
            # Points of the line: x, and t*x + y for t in GF(q).
            vecs = [tuple(int(c) for c in x)]
            for t in range(q):
                vecs.append(tuple(int(AT[MT[t, x[k]], y[k]]) for k in range(7)))
            idx = []
            for v in vecs:
                c = next(e for e in v if e)
                inv = F.inv(c)
                idx.append(index[tuple(F.mul(inv, e) for e in v)])
            lines.add(tuple(sorted(idx)))
    lines = sorted(lines)
    edges = [(pt, N + k) for k, L in enumerate(lines) for pt in L]
    return 2 * N, edges


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates (may be empty); build() keeps only those that pass lib.is_valid."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 6 and d - 1 in (2, 4):
        try:
            out.append(_hexagon_incidence(d - 1))
        except Exception:
            pass
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
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

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.5:
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
