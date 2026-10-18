"""Combined search: bi-Cayley graphs over metacyclic groups (nonabelian first, scanned upward
from a lower bound), then grow-by-two annealing from the best graph found.

C side:
  1. Bi-Cayley phase: for each order N (upward from nlo), random metacyclic groups Z_m x| Z_k
     of order N, hill-climb on the connection set S (|S| = d) minimising the number of vertices
     missed within distance D from A_e and B_e. Left multiplication is transitive on each side,
     so these two BFS runs decide validity. The largest N that succeeds is kept.
  2. Build the explicit graph (A_x ~ B_{x s}), verify it with a full check, and keep it if larger.
  3. Grow-by-two: add one vertex per side, then anneal 2-switches until diameter <= D.
  The result is re-verified before printing; fallback is K_{d,d} (or K_2 for D = 1).

Python side:
  Uses known constructions (projective plane, Araujo-Lopez) when they apply, passes the best
  start graph to C on stdin, and returns the largest graph that lib.is_valid accepts.
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

#define MAXN 2048
#define MAXW (MAXN / 64)
#define MAXD 16
#define MAXG 1024
#define MAXV (2 * MAXG)
#define MAXGRP 8192

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

/* ------------------------------------------------------------ utilities */

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
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
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* ------------------------------------------------------------ graph basics */

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

/* ------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN]; /* vertices farther than D from v (set by bad_pairs) */

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
            memcpy(dst, src, sizeof(uint64_t) * W);
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

/* Simple, bipartite by side labels, degree <= d, diameter <= D. */
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

/* ------------------------------------------------------------ input / output */

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
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
                if (g->side[u] == 255) { g->side[u] = (unsigned char)(1 - g->side[v]); queue[tail++] = u; }
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

/* K_{d,d} for D >= 2, a single edge for D = 1. */
static void fallback(Graph *g) {
    if (D >= 2) complete_bipartite(g);
    else {
        g->n = 2;
        g->deg[0] = g->deg[1] = 0;
        g->side[0] = 0;
        g->side[1] = 1;
        add_edge(g, 0, 1);
    }
}

/* ------------------------------------------------------------ groups Z_m x|_r Z_k */

/* Element (a, b) is coded a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct { int m, k, r; } Grp;
static Grp groups[MAXGRP];
static int ngroups, nnab; /* groups[0..nnab-1] are nonabelian */

static void enum_groups(int N) {
    ngroups = 0;
    nnab = 0;
    for (int pass = 0; pass < 2; pass++) {
        for (int m = 1; m <= N; m++) {
            if (N % m) continue;
            int k = N / m;
            if (m == 1) {
                if (pass == 1 && ngroups < MAXGRP) groups[ngroups++] = (Grp){1, k, 0};
                continue;
            }
            for (int r = 1; r < m; r++) {
                if (gcd(r, m) != 1 || powmod(r, k, m) != 1 % m) continue;
                int nonab = (r != 1);
                if ((pass == 0) != nonab) continue;
                if (ngroups < MAXGRP) groups[ngroups++] = (Grp){m, k, r};
            }
        }
        if (pass == 0) nnab = ngroups;
    }
}

static int MT[MAXG * MAXG]; /* multiplication table of the current group */
static int INV[MAXG];       /* inverses */

static void build_group(Grp G) {
    int n = G.m * G.k;
    static int rp[MAXG];
    rp[0] = 1 % G.m;
    for (int b = 1; b < G.k; b++) rp[b] = (int)((long)rp[b - 1] * G.r % G.m);
    for (int x = 0; x < n; x++) {
        int a = x / G.k, b = x % G.k;
        for (int y = 0; y < n; y++) {
            int c = y / G.k, e = y % G.k;
            MT[x * n + y] = (int)(((long)a + (long)rp[b] * c) % G.m) * G.k + (b + e) % G.k;
        }
    }
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (MT[x * n + y] == 0) { INV[x] = y; break; }
}

static int pick_group(void) {
    if (nnab > 0 && (ngroups == nnab || rnd01() < 0.8)) return rndint(nnab);
    return nnab + rndint(ngroups - nnab);
}

/* ------------------------------------------------------------ bi-Cayley search */

/* A_x = x, B_h = N + h. A_x ~ B_{x s} for s in S. Returns number of vertices missed
 * within distance D from A_0 and from B_0 (zero means diameter <= D). */
static int dist_[MAXV], queue_[MAXV];

static long cayley_miss(const int *S, int N) {
    int V = 2 * N;
    long miss = 0;
    for (int src = 0; src < 2; src++) {
        int s0 = src ? N : 0;
        for (int v = 0; v < V; v++) dist_[v] = -1;
        int head = 0, tail = 0;
        dist_[s0] = 0;
        queue_[tail++] = s0;
        while (head < tail) {
            int v = queue_[head++];
            int dv = dist_[v];
            if (dv >= D) continue;
            if (v < N) {
                const int *row = MT + v * N;
                for (int i = 0; i < d; i++) {
                    int u = N + row[S[i]];
                    if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
                }
            } else {
                const int *row = MT + (v - N) * N;
                for (int i = 0; i < d; i++) {
                    int u = row[INV[S[i]]];
                    if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
                }
            }
        }
        miss += V - tail;
    }
    return miss;
}

static int in_set(const int *S, int cnt, int x) {
    for (int j = 0; j < cnt; j++)
        if (S[j] == x) return 1;
    return 0;
}

/* Hill-climb on connection sets for the group currently in MT (order N > d). */
static int climb_group(int N, int restarts, int steps, double until, int *Sout) {
    int S[MAXD];
    for (int rep = 0; rep < restarts; rep++) {
        S[0] = 0;
        for (int i = 1; i < d; i++) {
            int x;
            do { x = 1 + rndint(N - 1); } while (in_set(S, i, x));
            S[i] = x;
        }
        long cur = cayley_miss(S, N);
        for (long s = 0; s < steps && cur > 0; s++) {
            if ((s & 63) == 0 && now() > until) return 0;
            int i = 1 + rndint(d - 1);
            int x;
            do { x = 1 + rndint(N - 1); } while (in_set(S, d, x));
            int old = S[i];
            S[i] = x;
            long c = cayley_miss(S, N);
            if (c <= cur || rnd01() < 0.02) cur = c;
            else S[i] = old;
        }
        if (cur == 0) {
            memcpy(Sout, S, sizeof(int) * (size_t)d);
            return 1;
        }
        if (now() > until) return 0;
    }
    return 0;
}

static int bestCN = 0;
static Grp bestCG;
static int bestCS[MAXD];

/* Scan orders N upward from nlo. Each order gets a slice of the remaining time; the last
 * order that succeeds is kept. */
static void cayley_phase(double until, int nlo) {
    long moore = moore_bound();
    int nmax = (int)(moore / 2);
    if (nmax > MAXG - 1) nmax = MAXG - 1;
    if (nlo < d + 1) nlo = d + 1;
    for (int N = nlo; N <= nmax; N++) {
        double t = now();
        if (t >= until) break;
        double left = until - t;
        int remaining = nmax - N + 1;
        double slice = 2.0 * left / remaining;
        if (slice < 0.05) slice = 0.05;
        if (slice > left) slice = left;
        double end = t + slice;
        enum_groups(N);
        if (ngroups == 0) continue;
        while (now() < end) {
            int gi = pick_group();
            Grp G = groups[gi];
            build_group(G);
            int S[MAXD];
            if (climb_group(N, 3, 3000, end, S)) {
                bestCN = N;
                bestCG = G;
                memcpy(bestCS, S, sizeof(int) * (size_t)d);
                break;
            }
        }
    }
}

static int build_cayley_graph(Graph *g) {
    int N = bestCN;
    build_group(bestCG);
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = (unsigned char)(v >= N); }
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) add_edge(g, x, N + MT[x * N + bestCS[i]]);
    return is_valid(g);
}

/* ------------------------------------------------------------ grow by two */

/* Insert one vertex per side (degree d), then anneal 2-switches until diameter <= D. */
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
        if (used[b] == stamp) continue;
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
    long moore = moore_bound();
    while (now() < until && best->n + 2 <= moore && best->n + 2 <= MAXN) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed budget [nlo] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int nlo = argc > 5 ? atoi(argv[5]) : 0;

    double t0 = now();
    t_end = t0 + budget * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD) { printf("0 0\n"); return 0; }

    static Graph best, cand;
    read_start(&best);
    if (best.n == 0) fallback(&best);

    if (D >= 2 && d >= 2 && best.n < moore_bound()) {
        int nl = nlo;
        if (nl < best.n / 2 + 1) nl = best.n / 2 + 1;
        cayley_phase(t0 + (t_end - t0) * 0.6, nl);
        if (bestCN > 0 && 2 * bestCN > best.n) {
            if (build_cayley_graph(&cand) && cand.n > best.n) copy_graph(&best, &cand);
        }
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) fallback(&best);
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


def _trivial(d, D):
    """Always-valid fallback graph."""
    if d < 1:
        return (1, [])
    if D < 2:
        return (2, [(0, 1)])
    return lib.haar_graph(d, range(d))   # K_{d,d}, diameter 2


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    best = _trivial(d, D)
    try:
        start = known_start(d, D)
        if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
            best = start
    except Exception:
        pass

    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d < 2 or d > 16 or D < 2:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 1.0:
        return best

    # Scan lower bound (half-order units): below this, orders are already easy.
    nlo = max(d + 1, best[0] // 2 + 1, int(0.45 * moore) // 2)
    if 2 * nlo > moore:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), nlo],
                         stdin_graph=best, timeout=budget + 6)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
