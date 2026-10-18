"""Bi-Cayley group-lift search in C with a fast BFS cost and a climbing order target.

The C engine lifts small base graphs (1-4 vertices per side) over random semidirect
products Z_m x| Z_k, annealing the voltages so every block representative reaches all
vertices within distance D. Each accepted lift is checked exactly before it is kept.
Exact small constructions (PG(2,q), Araujo-Pardo-Lopez, generalized quadrangles)
are still used when they apply, and K_{d,d} is the fallback.
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
# C engine: group-lift search. A lift has 2p blocks of N vertices (block i is
# A_i for i < p, B_{i-p} otherwise). Each of the d slots t is a perfect matching
# between A-blocks and B-blocks with a voltage g in the group G:
#   (A_i, x) ~ (B_{perm[t][i]}, x*g).
# Left multiplication is an automorphism, so distances from the 2p block
# representatives decide the diameter. Cost = total unreached pairs.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bi-Cayley group-lift search for bipartite degree-diameter graphs.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid start), or "0 0".
 * stdout: "n m" + edge lines, the largest valid graph found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXW (MAXN / 64)
#define MAXD 32
#define MAXP 4

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

/* Number of unordered pairs at distance > D (bitset BFS). */
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

static int valid_graph(const Graph *g) {
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
    if (!valid_graph(g)) g->n = 0;
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

/* ---------- groups: Z_m x|_r Z_k, element (a,b) = a*k+b ---------- */

typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;
static Grp G;

static int gmul(int x, int y) {
    int a = x / G.k, b = x % G.k, c = y / G.k, e = y % G.k;
    return (int)(((long)a + (long)G.rp[b] * c) % G.m) * G.k + (b + e) % G.k;
}

/* Random group of order N; always succeeds (cyclic fallback). */
static void make_group(int N) {
    static int dv[MAXN];
    int nd = 0;
    for (int m = 1; m <= N; m++)
        if (N % m == 0) dv[nd++] = m;
    int m = dv[rndint(nd)];
    int k = N / m;
    int r = 1;
    if (m > 2 && k > 1 && rndint(10) >= 3) {
        for (int q = 0; q < 60; q++) {
            int c = 2 + rndint(m - 2);
            if (gcd(c, m) == 1 && powmod(c, k, m) == 1 % m) { r = c; break; }
        }
    }
    G.m = m;
    G.k = k;
    G.r = r;
    G.rp[0] = 1 % m;
    for (int b = 1; b < k; b++) G.rp[b] = (int)((long)G.rp[b - 1] * r % m);
}

/* ---------- lift configuration ---------- */

static int P_, N_;
static int perm[MAXD][MAXP];
static int vg[MAXD][MAXP];
static int nbrL[MAXN][MAXD];
static int vstamp[MAXN];
static int curstamp = 0;
static int qbuf[MAXN];

/* Write slot t for the dart (A_i -> B_{perm[t][i]}, voltage vg[t][i]) on all N x values. */
static void fill_block(int t, int i) {
    int p = P_, N = N_, j = perm[t][i], g = vg[t][i];
    for (int x = 0; x < N; x++) {
        int y = gmul(x, g);
        nbrL[i * N + x][t] = (p + j) * N + y;
        nbrL[(p + j) * N + y][t] = i * N + x;
    }
}

static void fill_all(void) {
    for (int t = 0; t < d; t++)
        for (int i = 0; i < P_; i++) fill_block(t, i);
}

/* True if some other slot u < ulim has the same (perm, voltage) at block i. */
static int dup_clash(int t, int i, int ulim) {
    for (int u = 0; u < ulim; u++)
        if (u != t && perm[u][i] == perm[t][i] && vg[u][i] == vg[t][i]) return 1;
    return 0;
}

static void init_config(void) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < P_; i++) perm[t][i] = i;
        for (int i = P_ - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[t][i];
            perm[t][i] = perm[t][j];
            perm[t][j] = s;
        }
    }
    for (int t = 0; t < d; t++)
        for (int i = 0; i < P_; i++) {
            int tries = 0;
            do {
                vg[t][i] = rndint(N_);
            } while (dup_clash(t, i, t) && ++tries < 1000);
        }
}

static int ball_size(int src) {
    curstamp++;
    int head = 0, tail = 0;
    qbuf[tail++] = src;
    vstamp[src] = curstamp;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int lend = tail;
        while (head < lend) {
            int v = qbuf[head++];
            for (int t = 0; t < d; t++) {
                int u = nbrL[v][t];
                if (vstamp[u] != curstamp) {
                    vstamp[u] = curstamp;
                    qbuf[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* Unreached (source, vertex) pairs over the 2p block representatives. */
static long total_cost(void) {
    long n = 2L * P_ * N_, c = 0;
    for (int s = 0; s < 2 * P_; s++) c += n - ball_size(s * N_);
    return c;
}

/* Simulated annealing on voltages (and, for p > 1, on the matchings). */
static int attempt(long steps, double until) {
    long c = total_cost();
    for (long s = 0; s < steps && c > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        double T = 0.3 + 2.0 * (1.0 - (double)s / (double)steps);
        if (P_ > 1 && rnd01() < 0.1) {
            int t = rndint(d), i1 = rndint(P_), i2 = rndint(P_);
            if (i1 == i2) continue;
            int tmp = perm[t][i1];
            perm[t][i1] = perm[t][i2];
            perm[t][i2] = tmp;
            if (dup_clash(t, i1, d) || dup_clash(t, i2, d)) {
                tmp = perm[t][i1];
                perm[t][i1] = perm[t][i2];
                perm[t][i2] = tmp;
                continue;
            }
            fill_block(t, i1);
            fill_block(t, i2);
            long c2 = total_cost();
            if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) {
                c = c2;
            } else {
                tmp = perm[t][i1];
                perm[t][i1] = perm[t][i2];
                perm[t][i2] = tmp;
                fill_block(t, i1);
                fill_block(t, i2);
            }
            continue;
        }
        int t = rndint(d), i = rndint(P_);
        int old = vg[t][i];
        int ng = rndint(N_);
        if (ng == old) continue;
        vg[t][i] = ng;
        if (dup_clash(t, i, d)) { vg[t][i] = old; continue; }
        fill_block(t, i);
        long c2 = total_cost();
        if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) {
            c = c2;
        } else {
            vg[t][i] = old;
            fill_block(t, i);
        }
    }
    return c == 0;
}

static Graph best, cand;

/* Build the current lift as a Graph, check it exactly, and keep it if larger. */
static int try_store(void) {
    int A = P_ * N_, n = 2 * A;
    if (n <= best.n) return 0;
    cand.n = n;
    for (int v = 0; v < n; v++) {
        cand.deg[v] = 0;
        cand.side[v] = v >= A;
    }
    for (int v = 0; v < A; v++)
        for (int t = 0; t < d; t++) add_edge(&cand, v, nbrL[v][t]);
    if (!valid_graph(&cand)) return 0;
    copy_graph(&best, &cand);
    return 1;
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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 2 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!valid_graph(&best)) complete_bipartite(&best);

    long moore = moore_bound();
    while (now() < t_end && (long)best.n < moore) {
        int r = rndint(100);
        int p = r < 40 ? 1 : r < 70 ? 2 : r < 85 ? 3 : 4;
        long base = best.n / (2 * p);
        long Nl = base + 1;
        if (rndint(2)) Nl += rndint(3);
        else Nl += rndint((int)(base / 20 + 1));
        if (Nl < d) Nl = d;
        if (2L * p * Nl > moore || 2L * p * Nl > MAXN) continue;

        make_group((int)Nl);
        P_ = p;
        N_ = (int)Nl;
        init_config();
        fill_all();
        double until = now() + 3.0;
        if (until > t_end) until = t_end;
        if (attempt(30000, until)) try_store();
    }

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
        """Keep (n, e) if it is a larger valid graph."""
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

    # Main search (C): group lifts with climbing order target.
    if D >= 2:
        c_budget = end - time.monotonic() - 0.5
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
