"""Orbit-restricted voltage-lift annealing for bipartite degree-diameter graphs.

Construction: a base bipartite multigraph with P vertices per side and d darts per
vertex, lifted over a metacyclic group G = Z_m x|_r Z_k of order N. Vertices are
A(i,x) and B(j,y), with a dart (t, i) joining A(i,x) to B(tg[t][i], x*vl[t][i]).
Left multiplication is an automorphism, so the diameter is decided by 2P BFS runs,
one from each A(i,e) and each B(j,e). The annealing moves are voltage changes and
target swaps, which keep the base regular. Cost = vertices missed within distance D
from those 2P sources. This is a different family from the Cayley and lift search
in the parent: it uses larger base graphs (up to 8 per side) and orbit-restricted
costs, and it anneals instead of hill-climbing.

Fallback: the starter graph (if any) or K_{d,d}, both checked with lib.is_valid.
"""
import time

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
#define MAXP 8
#define MAXG 512
#define MAXGR 4096

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

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

/* ------------------------------------------------------------ graph basics */

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void copy_graph(Graph *dst, const Graph *src) { memcpy(dst, src, sizeof(Graph)); }

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance > D. Zero means diameter <= D. */
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
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
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

static int gN, gm, gk, gr;
static int gtab[MAXG * MAXG];
static int ginv[MAXG];
static int rpw[MAXG];
#define GM(x, y) gtab[(x) * gN + (y)]

/* Multiplication table of Z_m x|_r Z_k, element (a,b) coded a*k+b. */
static void set_group(int m, int k, int r) {
    gm = m; gk = k; gr = r; gN = m * k;
    for (int b = 0; b < k; b++) rpw[b] = (int)powmod(r, b, m);
    for (int x = 0; x < gN; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < gN; y++) {
            int c = y / k, e = y % k;
            gtab[x * gN + y] = (int)((a + (long)rpw[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < gN; x++)
        for (int y = 0; y < gN; y++)
            if (gtab[x * gN + y] == 0) { ginv[x] = y; break; }
}

static int glist[MAXGR][3];
static int ngl;

static void add_grp(int m, int k, int r) {
    if (ngl < MAXGR) { glist[ngl][0] = m; glist[ngl][1] = k; glist[ngl][2] = r; ngl++; }
}

/* All metacyclic groups of order N (m, k, r), with gcd(r,m)=1 and r^k = 1 mod m. */
static int list_groups(int N) {
    ngl = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) { add_grp(1, k, 0); continue; }
        for (int r = 1; r < m; r++)
            if (gcd(r, m) == 1 && powmod(r, k, m) == 1 % m) add_grp(m, k, r);
    }
    return ngl;
}

/* ------------------------------------------------------------ lift state */

static int P;                 /* vertices per side of the base multigraph */
static int tg[MAXD][MAXP];    /* layer t: dart from A_i goes to B_{tg[t][i]}; each layer is a permutation */
static int vl[MAXD][MAXP];    /* voltage of that dart */
static int srcA[MAXD][MAXP];  /* srcA[t][j] = i with tg[t][i] = j */
static int vinv[MAXD][MAXP];  /* inverse voltage of the dart into B_j in layer t */

static void rebuild_inv(void) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < P; i++) srcA[t][tg[t][i]] = i;
        for (int j = 0; j < P; j++) vinv[t][j] = ginv[vl[t][srcA[t][j]]];
    }
}

/* No two darts from the same A_i to the same B_j with equal voltage (would create a multi-edge). */
static int lift_valid(void) {
    for (int i = 0; i < P; i++)
        for (int t = 0; t < d; t++)
            for (int t2 = 0; t2 < t; t2++)
                if (tg[t][i] == tg[t2][i] && vl[t][i] == vl[t2][i]) return 0;
    return 1;
}

static int dist_[MAXN];
static int queue_[MAXN];

/* Vertices missed within distance D from the 2P representative sources A(i,e), B(j,e). */
static long lift_cost(void) {
    int N = gN;
    int V = 2 * P * N;
    int PN = P * N;
    long miss = 0;
    for (int s = 0; s < 2 * P; s++) {
        int s0 = s < P ? s * N : PN + (s - P) * N;
        for (int v = 0; v < V; v++) dist_[v] = -1;
        int head = 0, tail = 0;
        dist_[s0] = 0;
        queue_[tail++] = s0;
        while (head < tail) {
            int v = queue_[head++];
            int dv = dist_[v];
            if (dv >= D) continue;
            if (v < PN) {
                int i = v / N, x = v - i * N;
                for (int t = 0; t < d; t++) {
                    int u = PN + tg[t][i] * N + GM(x, vl[t][i]);
                    if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
                }
            } else {
                int w = v - PN, j = w / N, y = w - j * N;
                for (int t = 0; t < d; t++) {
                    int i = srcA[t][j];
                    int u = i * N + GM(y, vinv[t][j]);
                    if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
                }
            }
        }
        miss += V - tail;
    }
    return miss;
}

static int init_lift(void) {
    int perm[MAXP];
    for (int tries = 0; tries < 2000; tries++) {
        for (int t = 0; t < d; t++) {
            for (int i = 0; i < P; i++) perm[i] = i;
            for (int i = P - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < P; i++) tg[t][i] = perm[i];
        }
        for (int t = 0; t < d; t++)
            for (int i = 0; i < P; i++) vl[t][i] = rndint(gN);
        if (lift_valid()) return 1;
    }
    return 0;
}

/* Simulated annealing over voltages and target swaps. Returns 1 with a zero-cost lift in place. */
static int anneal(double until, long maxsteps) {
    if (!init_lift()) return 0;
    rebuild_inv();
    long cur = lift_cost();
    for (long s = 0; s < maxsteps && cur > 0; s++) {
        if ((s & 127) == 0 && now() > until) return 0;
        double T = 1.2 * (1.0 - (double)s / (double)maxsteps) + 0.03;
        int t = rndint(d), i = rndint(P);
        if (rndint(3) < 2) {
            int old = vl[t][i];
            int nv = rndint(gN);
            if (nv == old) continue;
            vl[t][i] = nv;
            if (!lift_valid()) { vl[t][i] = old; continue; }
            rebuild_inv();
            long c = lift_cost();
            if (c <= cur || rnd01() < exp(-(double)(c - cur) / T)) cur = c;
            else { vl[t][i] = old; rebuild_inv(); }
        } else {
            if (P < 2) continue;
            int i2 = rndint(P);
            if (i2 == i) continue;
            int a = tg[t][i]; tg[t][i] = tg[t][i2]; tg[t][i2] = a;
            if (!lift_valid()) {
                a = tg[t][i]; tg[t][i] = tg[t][i2]; tg[t][i2] = a;
                continue;
            }
            rebuild_inv();
            long c = lift_cost();
            if (c <= cur || rnd01() < exp(-(double)(c - cur) / T)) cur = c;
            else {
                a = tg[t][i]; tg[t][i] = tg[t][i2]; tg[t][i2] = a;
                rebuild_inv();
            }
        }
    }
    return cur == 0;
}

static void extract(Graph *g) {
    int N = gN, PN = P * N;
    g->n = 2 * PN;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= PN; }
    for (int t = 0; t < d; t++)
        for (int i = 0; i < P; i++)
            for (int x = 0; x < N; x++)
                add_edge(g, i * N + x, PN + tg[t][i] * N + GM(x, vl[t][i]));
}

/* Repeatedly aim for the next order above best, with a random base size and group. */
static void lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    long cap = moore < MAXN ? moore : MAXN;
    while (now() < until) {
        long target = best->n + 2;
        if (target > cap) break;
        int p = 1 + rndint(MAXP);
        long Nlow = (target + 2L * p - 1) / (2L * p);
        int N = (int)(Nlow + rndint(3));
        if (N < 2 || N > MAXG || 2L * p * N > cap) continue;
        int nl = list_groups(N);
        if (nl == 0) continue;
        int gi = rndint(nl);
        set_group(glist[gi][0], glist[gi][1], glist[gi][2]);
        P = p;
        double slice_end = now() + 3.0;
        if (slice_end > until) slice_end = until;
        if (anneal(slice_end, 150000)) {
            extract(&cand);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ------------------------------------------------------------ main */

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
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    if (best.n < moore_bound() && now() < t_end) lift_search(&best, t_end);
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    fallback = lib.haar_graph(d, range(d))             # K_{d,d}: valid for D >= 2
    start = known_start(d, D)
    best = start if start is not None else fallback
    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    elapsed = time.monotonic() - t0
    budget = 0.8 * time_limit - elapsed - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        timeout = max(1.0, time_limit - (time.monotonic() - t0) - 1.5)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=start, timeout=timeout)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except (RuntimeError, ValueError):
            pass   # keep the valid fallback
    return best
