"""Combined program, v3 (bold change for the weak d=3, D=9 case).

v2 searched only cyclic bi-Cayley graphs exhaustively and sampled a few semidirect groups at random.
v3 treats the whole family of metacyclic groups Z_m x|_r Z_k of each order N as the search space.
Each candidate is a bi-Cayley graph with one vertex per side: A-vertex x is joined to B-vertex x*g_t
for voltages g_0 = e, g_1, ..., g_{d-1}. Phase 1 runs an exhaustive cyclic scan (d = 3), cheap and
ascending in N. Phase 2 runs every metacyclic group of each order N, exhaustively over {e, a, b} when
the count is small and by random sampling otherwise. Diameter is checked with two BFS runs, from a_e
and from b_e, because left multiplication acts regularly on each side. Any graph returned by C is
checked again with lib.is_valid. The start graph (projective plane, W(q), or K_{d,d}) is the fallback,
so a valid graph is always returned."""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley search core, v3 (all metacyclic groups per order).
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXG 1024
#define MAXGR 96

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

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance > D, by bitset BFS. */
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

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct { int m, k, r; } Grp;

static Grp grps[MAXGR];
static int ngrp;

/* Multiplication table and inverses of the current group (identity is element 0). */
static int MT[MAXG][MAXG];
static int INV[MAXG];

/* All metacyclic groups of order N (one entry per (m, r), k = N / m). */
static void list_groups(int N) {
    ngrp = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (ngrp < MAXGR) { grps[ngrp].m = 1; grps[ngrp].k = k; grps[ngrp].r = 0; ngrp++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ngrp < MAXGR) { grps[ngrp].m = m; grps[ngrp].k = k; grps[ngrp].r = r; ngrp++; }
        }
    }
}

static void build_group(const Grp *G) {
    int m = G->m, k = G->k, r = G->r;
    int n = m * k;
    int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < n; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < n; y++) {
            int c = y / k, e = y % k;
            MT[x][y] = (int)(((a + (long)rp[b] * c) % m) * k + (b + e) % k);
        }
        int nb = (k - b) % k;
        long c = (m - ((long)rp[nb] * a) % m) % m;
        INV[x] = (int)(c * k + nb);
    }
}

/* ------------------------------------------------ bi-Cayley checks */

static int bdist[2 * MAXG];
static int bq[2 * MAXG];

/* BFS from src within depth D; true iff every vertex of the 2N-vertex graph is reached. */
static int reach_all(int N, const int *gs, const int *gi, int nd, int src) {
    int nv = 2 * N;
    for (int v = 0; v < nv; v++) bdist[v] = -1;
    int head = 0, tail = 0;
    bdist[src] = 0;
    bq[tail++] = src;
    while (head < tail) {
        int v = bq[head++];
        if (bdist[v] >= D) continue;
        for (int t = 0; t < nd; t++) {
            int u = v < N ? N + MT[v][gs[t]] : MT[v - N][gi[t]];
            if (bdist[u] < 0) {
                bdist[u] = bdist[v] + 1;
                bq[tail++] = u;
            }
        }
    }
    return tail == nv;
}

/* A-vertex x ~ B-vertex x*g_t. Left multiplication is an automorphism acting regularly on
 * each side, so BFS from a_e and from b_e decides the diameter. */
static int check_set(int N, int nd, const int *gs) {
    int gi[MAXD];
    for (int t = 0; t < nd; t++) gi[t] = INV[gs[t]];
    return reach_all(N, gs, gi, nd, 0) && reach_all(N, gs, gi, nd, N);
}

static int accept(int N, int nd, const int *gs, Graph *out) {
    out->n = 2 * N;
    for (int v = 0; v < out->n; v++) { out->deg[v] = 0; out->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int t = 0; t < nd; t++) add_edge(out, x, N + MT[x][gs[t]]);
    return is_valid(out);
}

/* Returns 1 if a valid graph was found (in out), 0 if none, -1 on timeout.
 * For d = 3, enumerates every {0,a,b} with a < b when the count is at most cap
 * (or always when force is set); otherwise samples cap random voltage sets. */
static int search_group(int N, int nd, int force, double until, long cap, Graph *out) {
    int gs[MAXD];
    long cnt = 0;
    if (nd == 3 && (force || (long)N * (N - 1) / 2 <= cap)) {
        for (int a = 1; a < N; a++)
            for (int b = a + 1; b < N; b++) {
                if ((++cnt & 255) == 0 && now() > until) return -1;
                gs[0] = 0; gs[1] = a; gs[2] = b;
                if (check_set(N, 3, gs) && accept(N, 3, gs, out)) return 1;
            }
        return 0;
    }
    for (long s = 0; s < cap; s++) {
        if ((s & 255) == 0 && now() > until) return -1;
        gs[0] = 0;
        int ok = 1;
        for (int t = 1; t < nd && ok; t++) {
            int tries = 0;
            for (;;) {
                int g = 1 + rndint(N - 1), dup = 0;
                for (int u = 0; u < t; u++)
                    if (gs[u] == g) { dup = 1; break; }
                if (!dup) { gs[t] = g; break; }
                if (++tries > 200) { ok = 0; break; }
            }
        }
        if (!ok) continue;
        if (check_set(N, nd, gs) && accept(N, nd, gs, out)) return 1;
    }
    return 0;
}

/* ------------------------------------------------------ scan driver */

static Graph best, cand;

/* Ascending over N from best.n/2 + 1. cyc_only restricts to cyclic groups, searched
 * exhaustively (d = 3 only). Otherwise every metacyclic group of order N is tried. */
static void scan(int cyc_only, long cap, double until) {
    long Nmax_l = moore_bound() / 2;
    if (Nmax_l > MAXG) Nmax_l = MAXG;
    int Nmax = (int)Nmax_l;
    int N = best.n / 2 + 1;
    if (N < d + 1) N = d + 1;
    while (N <= Nmax && now() < until) {
        int found = 0, timeout = 0;
        list_groups(N);
        for (int gi = 0; gi < ngrp && !found && !timeout; gi++) {
            if (cyc_only && grps[gi].k != 1) continue;
            build_group(&grps[gi]);
            int r = search_group(N, d, cyc_only, until, cap, &cand);
            if (r == 1) found = 1;
            else if (r < 0) timeout = 1;
        }
        if (found) copy_graph(&best, &cand);
        if (timeout) break;
        N++;
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
    double t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && d >= 3 && best.n < moore_bound()) {
        double span = t_end - t0;
        if (d == 3) scan(1, 0, t0 + 0.30 * span);
        scan(0, 60000, t_end);
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

    # Leave headroom for the C compile (first call) and output parsing.
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
