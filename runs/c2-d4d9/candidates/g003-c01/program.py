"""Iterated local search over voltage lifts, with a grow-by-target schedule.

Change from the parent: the random-sampling simulated annealing over lift voltages
is replaced by iterated local search. Each move picks one dart and evaluates a sample
of alternative voltages with the exact orbit-representative cost (rep_cost). It takes
the best one, accepts plateau moves, and applies a random 2-dart kick after a stall.
Base graphs have 1-3 vertices per side. Groups are semidirect products Z_m x| Z_k.
The grow-by-two phase is dropped, since its full all-pairs check was too slow near
the thousands-of-vertices range. Targets grow by an adaptive fraction, and each target
gets a bounded search slice. Every returned graph is re-checked in C with the full
diameter test, and in Python with lib.is_valid. Fallbacks are K_{d,d} (D >= 2) or K_{1,1}.
This is an exploratory search and does not guarantee beating the record.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXP 3

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

typedef struct { int i, j, g; } Dart;

static int d, D;
static double t_end;

/* ------------------------------------------------------------ utilities */

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

/* ------------------------------------------------------------ graph basics */

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

/* Exact count of unordered pairs at distance > D (bitset BFS, all pairs). */
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

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

/* Full validity: simple, symmetric, bipartite by side label, degree <= d, diameter <= D. */
static int is_valid(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
            int back = 0;
            for (int j = 0; j < g->deg[u]; j++)
                if (g->adj[u][j] == v) back++;
            if (back != 1) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

static int vis[MAXN];
static int vstamp = 0;
static int qbuf[MAXN];

/* Sum over the 2p fibre representatives of the number of vertices at distance > D.
 * Zero iff the lift is connected with diameter <= D (group acts regularly on fibres). */
static long rep_cost(const Graph *g, int p, int N) {
    long cost = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
        if (vstamp >= 2000000000) { memset(vis, 0, sizeof vis); vstamp = 0; }
        vstamp++;
        int head = 0, tail = 0;
        vis[src] = vstamp;
        qbuf[tail++] = src;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int v = qbuf[head++];
                for (int i = 0; i < g->deg[v]; i++) {
                    int u = g->adj[v][i];
                    if (vis[u] != vstamp) {
                        vis[u] = vstamp;
                        qbuf[tail++] = u;
                    }
                }
            }
        }
        cost += g->n - tail;
    }
    return cost;
}

/* ------------------------------------------------------------ input / output */

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

static void single_edge(Graph *g) {
    g->n = 2;
    g->deg[0] = g->deg[1] = 0;
    g->side[0] = 0;
    g->side[1] = 1;
    add_edge(g, 0, 1);
}

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element a*k+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k). */
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

/* ------------------------------------------------------------ voltage lifts */

/* Random d-regular bipartite base on p+p vertices (sum of d permutations), connected. */
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
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) { seen[u] = 1; nseen++; stack[top++] = u; }
            }
        }
        if (nseen == 2 * p) return;
    }
}

static void build_lift(Graph *g, int p, int N, const Grp *G, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(G, x, dt[t].g));
}

/* 1 if voltage g for dart t collides with another dart on the same base pair. */
static int clash(const Dart *dt, int nd, int t, int g) {
    for (int s = 0; s < nd; s++)
        if (s != t && dt[s].i == dt[t].i && dt[s].j == dt[t].j && dt[s].g == g) return 1;
    return 0;
}

static long eval_cost(Graph *out, int p, int N, const Grp *G, const Dart *dt, int nd) {
    build_lift(out, p, N, G, dt, nd);
    return rep_cost(out, p, N);
}

/* Iterated local search over the voltages of one base and one group of order N.
 * Move: pick a dart, score a sample of alternative voltages, take the best (ties random,
 * plateau moves allowed). After 40 stalled moves, randomise two darts. */
static int ils(Graph *out, int p, int N, const Grp *G, double until) {
    int M[MAXP][MAXP];
    Dart dt[MAXP * MAXD];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            if (M[i][j] > N) return 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i; dt[nd].j = j; dt[nd].g = -1; nd++;
            }
    for (int t = 0; t < nd; t++) {
        do dt[t].g = rndint(N); while (clash(dt, nd, t, dt[t].g));
    }
    int S = N < 128 ? N : 128;
    long cost = eval_cost(out, p, N, G, dt, nd);
    int stall = 0;
    while (cost > 0 && now() < until) {
        int t = rndint(nd);
        int old = dt[t].g;
        long bc = LONG_MAX;
        int bg = -1, ties = 0;
        for (int s = 0; s < S; s++) {
            if ((s & 15) == 15 && now() > until) break;
            int g = (S == N) ? s : rndint(N);
            if (g == old || clash(dt, nd, t, g)) continue;
            dt[t].g = g;
            long c = eval_cost(out, p, N, G, dt, nd);
            dt[t].g = old;
            if (c < bc) { bc = c; bg = g; ties = 1; }
            else if (c == bc && rndint(++ties) == 0) bg = g;
        }
        if (bg >= 0 && bc < cost) { dt[t].g = bg; cost = bc; stall = 0; }
        else if (bg >= 0 && bc == cost) { dt[t].g = bg; stall++; }
        else stall++;
        if (stall > 40) {
            for (int k = 0; k < 2; k++) {
                int s = rndint(nd);
                do dt[s].g = rndint(N); while (clash(dt, nd, s, dt[s].g));
            }
            cost = eval_cost(out, p, N, G, dt, nd);
            stall = 0;
        }
    }
    build_lift(out, p, N, G, dt, nd);
    return rep_cost(out, p, N) == 0;
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
    t_end = t0 + limit * 0.93;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        printf("2 1\n0 1\n");
        return 0;
    }

    static Graph best, cand;
    static Grp G;
    read_start(&best);
    if (best.n == 0) {
        if (D >= 2) complete_bipartite(&best);
        else single_edge(&best);
    }

    long moore = moore_bound();
    if (moore > MAXN) moore = MAXN;
    double f = 0.01;   /* relative growth step of the target order */
    while (D >= 2 && now() < t_end && best.n + 2 <= moore) {
        long lo = best.n + 2;
        long step = (long)(best.n * f);
        if (step < 1) step = 1;
        long target = lo + (long)(rnd() % (uint64_t)step);
        int p = 1 + rndint(MAXP);
        long N = (target + 2L * p - 1) / (2L * p);
        if (N < 1) N = 1;
        long nn = 2L * p * N;
        if (nn > moore || nn > MAXN) break;
        int ok = 0;
        if (random_group((int)N, &G)) {
            double slice_end = now() + 6.0;
            if (slice_end > t_end) slice_end = t_end;
            if (ils(&cand, p, (int)N, &G, slice_end) && nn > best.n && is_valid(&cand)) {
                copy_graph(&best, &cand);
                ok = 1;
            }
        }
        if (ok) {
            f *= 1.2;
            if (f > 0.05) f = 0.05;
        } else {
            f *= 0.9;
            if (f < 0.002) f = 0.002;
        }
    }

    if (!is_valid(&best)) {
        if (D >= 2) complete_bipartite(&best);
        else single_edge(&best);
    }
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


def fallback(d, D):
    """Always-valid graph: K_{d,d} for D >= 2, otherwise a single edge."""
    if D >= 2 and d >= 1:
        return lib.haar_graph(d, range(d))             # K_{d,d}
    return (2, [(0, 1)])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback(d, D)
    budget = 0.92 * time_limit - (time.monotonic() - t0) - 1.5
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=start, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
