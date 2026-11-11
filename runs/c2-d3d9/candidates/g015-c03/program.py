"""Combined program: bi-Cayley search over metacyclic groups, then tabu-repaired growth.

C side (one run):
  1. If no start graph is given, scan orders N downward from the Moore limit. For each N,
     sample metacyclic groups Z_m x| Z_k and random connection sets S (|S| = d). The bi-Cayley
     graph (A_x ~ B_{xs}) is checked with two BFS runs, from A_e and B_e. The first success is
     the largest N found and is fully re-verified.
  2. Grow by two: insert one vertex per side, rewire d-1 edges to them, then repair the bad
     pairs with simulated annealing followed by a tabu search over double-edge swaps.
     Degrees stay fixed, and every accepted state is valid.

Python side: uses a known construction when one exists (Moore graph or Araujo-Pardo-Lopez),
otherwise K_{d,d}. It passes the start graph to C when there is one, and checks everything
with lib.is_valid before returning.
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
#define MAXG 1024
#define MAXV (2 * MAXG)
#define MAXGRP 4096
#define TABU_LEN 48
#define TABU_K 12
#define TABU_STALL 500

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
static int badv[MAXN];

/* Number of unordered pairs at distance > D. Also fills badv[]. */
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

/* Full validity: simple, bipartite by side labels, degree <= d, diameter <= D. */
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

/* Always-valid fallback: K_{d,d} when D >= 2, else a single edge. */
static void make_trivial(Graph *g) {
    for (int v = 0; v < MAXN; v++) { g->deg[v] = 0; g->side[v] = 0; }
    if (D >= 2) {
        g->n = 2 * d;
        for (int v = 0; v < g->n; v++) g->side[v] = v >= d;
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++) add_edge(g, a, d + b);
    } else {
        g->n = 2;
        g->side[1] = 1;
        add_edge(g, 0, 1);
    }
}

/* ------------------------------------------------------------ groups Z_m x|_r Z_k */

typedef struct { int m, k, r; } Grp;
static Grp groups[MAXGRP];
static int ngroups;

/* All metacyclic groups of order n: element (a,b) is coded a*k+b. */
static void enum_groups(int n) {
    ngroups = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            if (ngroups < MAXGRP) { groups[ngroups].m = 1; groups[ngroups].k = k; groups[ngroups].r = 0; ngroups++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ngroups < MAXGRP) { groups[ngroups].m = m; groups[ngroups].k = k; groups[ngroups].r = r; ngroups++; }
        }
    }
}

static int MT[MAXG * MAXG]; /* multiplication table of the current group */
static int INV[MAXG];
static int NN;

static void build_group(Grp G) {
    int n = G.m * G.k;
    NN = n;
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

/* ------------------------------------------------------------ bi-Cayley check */

static int dist_[MAXV], queue_[MAXV];

/* 1 iff every vertex of the bi-Cayley graph is within D of src.
 * A_x = x, B_h = NN + h, A_x ~ B_{x s} for s in S. */
static int reach_all(const int *S, int src) {
    int n = NN, V = 2 * n;
    for (int i = 0; i < V; i++) dist_[i] = -1;
    int head = 0, tail = 0;
    dist_[src] = 0;
    queue_[tail++] = src;
    while (head < tail) {
        int v = queue_[head++];
        int dv = dist_[v];
        if (dv >= D) continue;
        if (v < n) {
            for (int i = 0; i < d; i++) {
                int u = n + MT[v * n + S[i]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        } else {
            int h = v - n;
            for (int i = 0; i < d; i++) {
                int u = MT[h * n + INV[S[i]]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        }
    }
    return tail == V;
}

/* Random connection set {0, s_1, ..., s_{d-1}} of distinct elements. */
static void pick_set(int n, int *S) {
    S[0] = 0;
    for (int i = 1; i < d; i++) {
        for (;;) {
            int x = 1 + rndint(n - 1);
            int dup = 0;
            for (int j = 0; j < i; j++)
                if (S[j] == x) { dup = 1; break; }
            if (!dup) { S[i] = x; break; }
        }
    }
}

/* Scan N downward from the Moore limit. The first N with a valid bi-Cayley graph wins. */
static void cayley_phase(Graph *best, double until) {
    long moore = moore_bound();
    int nmax = (int)(moore / 2);
    if (nmax > MAXG - 1) nmax = MAXG - 1;
    int nmin = best->n / 2 + 1;
    if (nmin < d + 1) nmin = d + 1;
    static int S[MAXD];
    static int order[MAXGRP];
    static Graph cand;
    for (int n = nmax; n >= nmin; n--) {
        if (now() > until) return;
        enum_groups(n);
        if (ngroups == 0) continue;
        for (int i = 0; i < ngroups; i++) order[i] = i;
        for (int i = ngroups - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = order[i]; order[i] = order[j]; order[j] = t;
        }
        int tries_g = ngroups < 6 ? ngroups : 6;
        for (int gi = 0; gi < tries_g; gi++) {
            if (now() > until) return;
            Grp G = groups[order[gi]];
            build_group(G);
            for (int t = 0; t < 60; t++) {
                pick_set(n, S);
                if (reach_all(S, 0) && reach_all(S, n)) {
                    build_group(G);
                    cand.n = 2 * n;
                    for (int v = 0; v < cand.n; v++) { cand.deg[v] = 0; cand.side[v] = v >= n; }
                    for (int x = 0; x < n; x++)
                        for (int i = 0; i < d; i++) add_edge(&cand, x, n + MT[x * n + S[i]]);
                    if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
                    return;
                }
            }
        }
    }
}

/* ------------------------------------------------------------ tabu repair */

static int tabu_a[TABU_LEN], tabu_b[TABU_LEN];
static int tabu_cnt = 0, tabu_pos = 0;

static void push_tabu(int a, int b) {
    if (a > b) { int t = a; a = b; b = t; }
    tabu_a[tabu_pos] = a;
    tabu_b[tabu_pos] = b;
    tabu_pos = (tabu_pos + 1) % TABU_LEN;
    if (tabu_cnt < TABU_LEN) tabu_cnt++;
}

static int is_tabu(int a, int b) {
    if (a > b) { int t = a; a = b; b = t; }
    for (int i = 0; i < tabu_cnt; i++)
        if (tabu_a[i] == a && tabu_b[i] == b) return 1;
    return 0;
}

/* Random degree-preserving double-edge swap: (v,u),(s,t) -> (v,t),(s,u). */
static int rand_swap(Graph *g) {
    for (int tries = 0; tries < 100; tries++) {
        int v = rndint(g->n);
        if (g->deg[v] == 0) continue;
        int u = g->adj[v][rndint(g->deg[v])];
        int s = rndint(g->n);
        if (g->side[s] != g->side[v] || s == v || g->deg[s] == 0) continue;
        int t = g->adj[s][rndint(g->deg[s])];
        if (t == u || has_edge(g, v, t) || has_edge(g, s, u)) continue;
        del_edge(g, v, u);
        del_edge(g, s, t);
        add_edge(g, v, t);
        add_edge(g, s, u);
        return 1;
    }
    return 0;
}

/* Tabu search over degree-preserving swaps. Returns 1 if work becomes valid. */
static int tabu_repair(Graph *work, double until) {
    long bad = bad_pairs(work);
    long best_bad = bad, stall = 0;
    tabu_cnt = 0;
    tabu_pos = 0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        int v = -1;
        for (int tries = 0; tries < 50; tries++) {
            int c = rndint(work->n);
            if (badv[c] > 0 && work->deg[c] > 0) { v = c; break; }
        }
        if (v < 0) {
            v = rndint(work->n);
            if (work->deg[v] == 0) continue;
        }
        int u = work->adj[v][rndint(work->deg[v])];
        long nb_best = -1;
        int bs = -1, bt = -1;
        for (int k = 0; k < TABU_K; k++) {
            int s = rndint(work->n);
            if (work->side[s] != work->side[v] || s == v || work->deg[s] == 0) continue;
            int t = work->adj[s][rndint(work->deg[s])];
            if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
            del_edge(work, v, u);
            del_edge(work, s, t);
            add_edge(work, v, t);
            add_edge(work, s, u);
            long nb = bad_pairs(work);
            del_edge(work, v, t);
            del_edge(work, s, u);
            add_edge(work, v, u);
            add_edge(work, s, t);
            if ((is_tabu(v, t) || is_tabu(s, u)) && nb >= best_bad) continue;
            if (nb_best < 0 || nb < nb_best) { nb_best = nb; bs = s; bt = t; }
        }
        if (nb_best >= 0) {
            del_edge(work, v, u);
            del_edge(work, bs, bt);
            add_edge(work, v, bt);
            add_edge(work, bs, u);
            push_tabu(v, u);
            push_tabu(bs, bt);
        }
        bad = bad_pairs(work);
        if (bad < best_bad) {
            best_bad = bad;
            stall = 0;
        } else if (++stall > TABU_STALL) {
            for (int p = 0; p < 3; p++) rand_swap(work);
            tabu_cnt = 0;
            bad = bad_pairs(work);
            best_bad = bad;
            stall = 0;
        }
    }
    return is_valid(work);
}

/* ------------------------------------------------------------ grow by two */

/* Insert one vertex per side (degree d each), then repair: annealing, then tabu. */
static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = 0;
    work->deg[y] = 0;
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
    double t_sa = now() + 0.5 * (until - now());
    long bad = bad_pairs(work);
    double T = 1.0;
    while (bad > 0 && now() < t_sa) {
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
    if (bad > 0 && !tabu_repair(work, until)) return 0;
    return is_valid(work);
}

static void grow_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound() && best->n + 2 <= MAXN) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
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
    t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || d > MAXD) { printf("1 0\n"); return 0; }

    read_start(&best);
    int had_start = best.n > 0;
    if (!had_start) make_trivial(&best);

    if (D >= 2 && d >= 2 && best.n < moore_bound()) {
        double frac = had_start ? 0.25 : 0.45;
        cayley_phase(&best, t0 + (t_end - t0) * frac);
    }
    if (D >= 2 && best.n < moore_bound()) grow_search(&best, t_end);

    if (!is_valid(&best)) make_trivial(&best);
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


def trivial(d, D):
    """Always-valid fallback graph."""
    if d < 1:
        return (1, [])
    if D >= 2:
        return lib.haar_graph(d, range(d))             # K_{d,d}
    return (2, [(0, 1)])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = None
    try:
        start = known_start(d, D)
    except ValueError:
        start = None
    if start is not None and not lib.is_valid(start[0], start[1], d, D):
        start = None
    best = start if start is not None else trivial(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d < 2 or d > 32 or D < 2:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=start, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
