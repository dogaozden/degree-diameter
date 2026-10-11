"""Difference-covering Haar search for bipartite degree-diameter graphs with D = 3.

Bold change: the parent grew a start graph by annealing whole-graph swaps. This version
replaces that with a much smaller search. For a group G of order N and a set S of d elements,
the Haar graph (a_x ~ b_{x s}, s in S) has 2N vertices, is d-regular and bipartite, and has
diameter <= 3 exactly when every non-identity g in G is a quotient s t^{-1} with s, t in S.
The C engine anneals S against this covering count using O(d) incremental updates, over
random cyclic and semidirect groups Z_m x| Z_k of order N just above the current best half.
Any covering found gives a valid graph of order 2N, which is kept only if it beats the start.

Python still builds the Araujo-Pardo and Lopez record, the projective plane (Moore-optimal when
d-1 is a prime power) and the generalized quadrangle for D >= 4. The result is always checked
with lib.is_valid, and K_{d,d} is the fallback. Non-D=3 cases do not call C in this version.
"""
import itertools
import time

import lib

GQ_Q_MAX = 7      # largest q for which W(q) is built in Python (D >= 4 only)
TIME_FRAC = 0.82  # fraction of time_limit spent before the C engine is given its budget

C_SOURCE = r'''
/* Difference-covering Haar search, D = 3.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v" (valid start), or "0 0".
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * For a group G of order N (cyclic or Z_m x| Z_k) and S = {s_1..s_d} in G, the Haar graph
 * a_x ~ b_{x s} has order 2N, is d-regular and bipartite, and has diameter <= 3 iff every
 * g != 1 in G equals s t^{-1} for some s != t in S. The search anneals S to cover G\{1}.
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
#define MAXG 512

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
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

/* ------------------------------------------------------------------ graph basics */

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

/* ------------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance > D (0 means diameter <= D). */
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

/* Simple, bipartite (by side labels), degree <= d, diameter <= D. */
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
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            u == v || g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
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

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ groups */

static int G_N, G_m, G_k, G_r;
static int MUL[MAXG * MAXG];   /* MUL[x*N + y] = x*y */
static int INV[MAXG];

/* Group Z_m x|_r Z_k, element (a,b) is the int a*k + b; identity is 0. */
static void build_group(int m, int k, int r) {
    int N = m * k;
    int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    G_N = N; G_m = m; G_k = k; G_r = r;
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            int A = (int)((a + (long)rp[b] * c) % m);
            MUL[x * N + y] = A * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MUL[x * N + y] == 0) { INV[x] = y; break; }
}

/* Uniformly random group of order N among all (m, k, r) with gcd(r,m)=1, r^k=1 mod m. */
static int random_group(int N) {
    long count = 0;
    int bm = -1, bk = -1, br = -1;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (count == 0) return 0;
    build_group(bm, bk, br);
    return 1;
}

/* ------------------------------------------------------------------ covering anneal */

static int cnt_[MAXG];
static int unc_;   /* number of g != 1 with no representation s t^{-1} yet */

static void cnt_inc(int g) { if (g && cnt_[g]++ == 0) unc_--; }
static void cnt_dec(int g) { if (g && --cnt_[g] == 0) unc_++; }

static int in_set(const int *S, int k, int y) {
    for (int j = 0; j < k; j++) if (S[j] == y) return 1;
    return 0;
}

static void cover_init(const int *S) {
    int N = G_N;
    memset(cnt_, 0, sizeof(int) * N);
    unc_ = N - 1;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            if (i != j) cnt_inc(MUL[S[i] * N + INV[S[j]]]);
}

/* Replace S[i] by y, updating the coverage counts in O(d). */
static void replace_elem(int *S, int i, int y) {
    int N = G_N, x = S[i];
    for (int j = 0; j < d; j++) if (j != i) {
        cnt_dec(MUL[x * N + INV[S[j]]]);
        cnt_dec(MUL[S[j] * N + INV[x]]);
    }
    S[i] = y;
    for (int j = 0; j < d; j++) if (j != i) {
        cnt_inc(MUL[y * N + INV[S[j]]]);
        cnt_inc(MUL[S[j] * N + INV[y]]);
    }
}

/* Anneal S (size d, distinct) to cover G\{1}. Returns the uncovered count (0 = success). */
static int anneal_cover(int *S, long iters) {
    int N = G_N;
    for (int i = 0; i < d; i++) {
        int y;
        do { y = rndint(N); } while (in_set(S, i, y));
        S[i] = y;
    }
    cover_init(S);
    double T = 0.6;
    for (long it = 0; it < iters && unc_ > 0; it++) {
        int i = rndint(d), y = rndint(N);
        if (in_set(S, d, y)) continue;
        int x = S[i], old = unc_;
        replace_elem(S, i, y);
        int nc = unc_;
        if (!(nc <= old || rnd01() < exp((double)(old - nc) / T)))
            replace_elem(S, i, x);
        T *= 0.99995;
        if (T < 0.03) T = 0.6;
    }
    return unc_;
}

/* Haar graph: a_x ~ b_{x s} for s in S. Order 2N, d-regular, bipartite. */
static void build_haar(Graph *g, int N, const int *S) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            add_edge(g, x, N + MUL[x * N + S[i]]);
}

static void cover_search(Graph *best, double until) {
    static Graph cand;
    int Nmax = d * d - d + 1;          /* covering bound: d(d-1) >= N-1 */
    if (Nmax > MAXG - 1) Nmax = MAXG - 1;
    if (2 * Nmax > MAXN) Nmax = MAXN / 2;
    int S[MAXD];
    while (now() < until) {
        int h = best->n / 2 + 1;
        if (h < d + 1) h = d + 1;
        if (h > Nmax) return;
        int span = Nmax - h + 1;
        if (span > 6) span = 6;
        int N = h + rndint(span);
        if (!random_group(N)) continue;
        int ok = 0;
        for (int rep = 0; rep < 5 && !ok && now() < until; rep++)
            ok = (anneal_cover(S, 150000) == 0);
        if (ok) {
            build_haar(&cand, N, S);
            if (cand.n > best->n && is_valid(&cand)) *best = cand;
        }
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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (D == 3 && d >= 3) cover_search(&best, t_end);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ---------------------------------------------------------------- Python constructions

def _gq_w(q):
    """Point-line incidence graph of the generalized quadrangle W(q): degree q+1, diameter 4."""
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


def known_start(d, D):
    """Best known construction Python builds directly for (d, D), or None."""
    if D == 3:
        if lib.is_prime_power(d - 1):
            return lib.projective_plane_incidence(d - 1)       # Moore graph, optimal
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                return lib.araujo_lopez_graph(d - 2)           # record 2(q^2+q+5), q = d-2
            except ValueError:
                return None
        return None
    if D >= 4:
        return _best_gq(d)
    return None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))          # K_{d,d} is extremal for D = 2

    best = lib.haar_graph(d, range(d))              # K_{d,d}: always valid for D >= 2

    start = None
    try:
        start = known_start(d, D)
    except Exception:
        start = None
    if start is not None and not lib.is_valid(start[0], start[1], d, D):
        start = None
    if start is not None and start[0] > best[0]:
        best = start

    # Moore-extremal start: nothing to search for.
    if start is not None and start[0] >= lib.moore_bound(d, D):
        return best

    # This version searches only D = 3; other diameters keep the Python construction.
    if D != 3 or d < 3:
        return best

    budget = TIME_FRAC * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 1.0:
        return best

    stdin_graph = best if best[0] > 2 * d else None
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=stdin_graph, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass                                        # keep the valid Python fallback
    return best
