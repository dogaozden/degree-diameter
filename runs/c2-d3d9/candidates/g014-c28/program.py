"""Combined bi-Cayley / voltage-lift / grow search for bipartite degree-diameter graphs.

Stages inside the C engine, after reading the start graph from stdin:
  A. Bi-Cayley search: for each order n, scan metacyclic groups Z_m x| Z_k of order n
     (nonabelian first). A bi-Cayley graph has parts A_x, B_x (x in G) with A_x ~ B_{xs}
     for s in S, 1 in S. Left multiplication is an automorphism, so the diameter check needs
     only BFS from A_1 and B_1. For d = 3 the connection set {1, s, t} is searched
     exhaustively; otherwise it is sampled at random. Every hit is rebuilt explicitly and
     re-verified with the bitset check before it is kept.
  B. Voltage lifts with p = 2 or 3 base vertices per side over the same groups, with
     hill-climbing on the voltages (generalises stage A).
  C. Grow by two: add one vertex per side using spare edge slots, then anneal edge swaps.

Python supplies the best known start (or K_{d,d}), passes the search the lower order bound,
and keeps only graphs that pass lib.is_valid.
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

#define MAXN 2200
#define MAXD 16
#define MAXW ((MAXN + 63) / 64)
#define MAXG 1024
#define MAXV (2 * MAXG)
#define MAXGRP 8192
#define MAXP 4

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
        badv[v] = n - c;
        total += n - c;
    }
    return total / 2;
}

/* Full validity: simple, bipartite (by side labels), degree <= d, diameter <= D. */
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

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ groups Z_m x| Z_k */

/* Element (a, b) is coded a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct { int m, k, r; } Grp;

static int cur_m = 1, cur_k = 1;
static int rpw[MAXG];     /* rpw[b] = r^b mod m for the current group */
static int bc_n = 1;      /* current order */
static int MT[MAXG * MAXG];
static int INV[MAXG];

static void set_group(const Grp *G) {
    cur_m = G->m;
    cur_k = G->k;
    rpw[0] = 1 % cur_m;
    for (int b = 1; b < cur_k; b++) rpw[b] = (int)((long)rpw[b - 1] * G->r % cur_m);
}

static int gmul(int x, int y) {
    int a = x / cur_k, b = x % cur_k, c = y / cur_k, e = y % cur_k;
    return (int)(((long)a + (long)rpw[b] * c) % cur_m) * cur_k + (b + e) % cur_k;
}

/* Multiplication table and inverses of the current group. */
static void build_mt(void) {
    int n = cur_m * cur_k;
    bc_n = n;
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++) MT[x * n + y] = gmul(x, y);
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (MT[x * n + y] == 0) { INV[x] = y; break; }
}

/* All metacyclic groups of order N (m >= 2 covers every cyclic group via r = 1),
 * nonabelian ones first. Returns the count written to out. */
static int enum_groups(int N, Grp *out, int cap) {
    int cnt = 0;
    for (int pass = 0; pass < 2; pass++) {
        for (int m = 2; m <= N; m++) {
            if (N % m) continue;
            int k = N / m;
            for (int r = 1; r < m; r++) {
                if (gcd(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
                int nonab = (r != 1);
                if ((pass == 0) != nonab) continue;
                if (cnt < cap) {
                    out[cnt].m = m;
                    out[cnt].k = k;
                    out[cnt].r = r;
                    cnt++;
                }
            }
        }
    }
    return cnt;
}

/* ------------------------------------------------------------ bi-Cayley search */

static int dist_[MAXV], queue_[MAXV];

/* 1 iff every vertex of the bi-Cayley graph is within D of src.
 * A_x = x, B_h = n + h. A_x ~ B_{x s}; B_h ~ A_{h s^-1}. */
static int reach_all(const int *S, int src) {
    int n = bc_n, V = 2 * n;
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

/* Search connection sets S = {0, s_1, ..., s_{d-1}} for the current group until time 'until'.
 * d = 3: exhaustive over pairs. Otherwise random sampling. Returns 1 and fills S on success. */
static int search_bicayley(double until, int *S) {
    int n = bc_n;
    S[0] = 0;
    if (d == 3) {
        int cnt = 0;
        for (int s = 1; s < n; s++)
            for (int t = s + 1; t < n; t++) {
                if ((++cnt & 63) == 0 && now() > until) return 0;
                S[1] = s;
                S[2] = t;
                if (reach_all(S, 0) && reach_all(S, n)) return 1;
            }
        return 0;
    }
    for (long tries = 0;; tries++) {
        if ((tries & 31) == 0 && now() > until) return 0;
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
        if (reach_all(S, 0) && reach_all(S, n)) return 1;
    }
}

/* Explicit bi-Cayley graph for the current group and set S. */
static void build_bicayley(Graph *g, const int *S) {
    int n = bc_n;
    g->n = 2 * n;
    for (int v = 0; v < 2 * n; v++) { g->deg[v] = 0; g->side[v] = v >= n; }
    for (int x = 0; x < n; x++)
        for (int i = 0; i < d; i++) add_edge(g, x, n + MT[x * n + S[i]]);
}

/* Scan orders n upward from nlo; for each n try the groups in turn within a time slice. */
static void phaseA(Graph *best, int nlo, double until) {
    static Grp list[MAXGRP];
    static Graph cand;
    static int S[MAXD];
    long moore = moore_bound();
    int n0 = nlo > d ? nlo : d;
    if (n0 < 2) n0 = 2;
    for (int n = n0; now() < until; n++) {
        if (2L * n > moore || n >= MAXG || 2 * n > MAXN) break;
        if (2 * n <= best->n) continue;
        int ng = enum_groups(n, list, MAXGRP);
        if (ng == 0) continue;
        double rem = until - now();
        double slice = rem / 4.0;
        if (slice < 0.5) slice = rem < 0.5 ? rem : 0.5;
        double slice_end = now() + slice;
        for (int gi = 0; gi < ng; gi++) {
            double tn = now();
            if (tn >= slice_end) break;
            double gdl = tn + (slice_end - tn) / (ng - gi);
            set_group(&list[gi]);
            build_mt();
            if (search_bicayley(gdl, S)) {
                build_bicayley(&cand, S);
                if (is_valid(&cand) && cand.n > best->n) copy_graph(best, &cand);
                break;
            }
        }
    }
}

/* ------------------------------------------------------------ voltage lifts (p = 2, 3) */

typedef struct { int i, j, g; } Dart;

/* Random d-regular bipartite base multigraph on p + p vertices (sum of d permutation
 * matrices), retried until connected. M[i][j] = number of darts i -> j. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
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

/* A voltage not used by another dart between the same base pair (i, j). */
static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static void build_lift(Graph *g, int p, int N, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(x, dt[t].g));
}

/* Hill-climb over voltages of a random base graph for the current group. */
static int lift_try(Graph *g, int p, int N, int steps, double until) {
    static Dart dt[MAXD * MAXP];
    int M[MAXP][MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(g, p, N, dt, nd);
    long bad = bad_pairs(g);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 15) == 0 && now() > until) return 0;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, dt, nd);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < 0.01) bad = nb;
        else dt[t].g = old;
    }
    return bad == 0;
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp list[MAXGRP];
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        int p = 2 + rndint(2);
        long target = best->n + 2;
        int base_N = (int)((target + 2 * p - 1) / (2 * p));
        int N = base_N + rndint(2 + base_N / 16);
        if (N < d || N >= MAXG || 2L * p * N > moore || 2 * p * N > MAXN) {
            if (++fails > 1000) return;
            continue;
        }
        int ng = enum_groups(N, list, MAXGRP);
        if (ng == 0) continue;
        Grp G = list[rndint(ng)];
        set_group(&G);
        int steps = 200 + 400000 / (2 * p * N);
        if (lift_try(&cand, p, N, steps, until) && cand.n > best->n && is_valid(&cand))
            copy_graph(best, &cand);
    }
}

/* ------------------------------------------------------------ grow by two */

/* Insert one vertex per side using spare degree from d-1 removed edges, then anneal. */
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
        if (used[b] == stamp || b >= n) continue;
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
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [nlo] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int nlo = argc > 5 ? atoi(argv[5]) : 0;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("0 0\n"); return 0; }

    double t0 = now();
    t_end = t0 + budget * 0.92;

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (d >= 2 && D >= 2 && best.n < moore_bound()) {
        double span = t_end - t0;
        phaseA(&best, nlo, t0 + span * 0.55);
        lift_search(&best, t0 + span * 0.75);
        grow_search(&best, t_end);
    }
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


def _trivial(d, D):
    """A graph that is always valid when d >= 1 and D >= 1."""
    return (2, [(0, 1)]) if d >= 1 and D >= 1 else (1, [])


def _checked(g, d, D):
    """Return g if it is valid for (d, D), otherwise a trivial valid graph."""
    n, edges = g
    return g if lib.is_valid(n, edges, d, D) else _trivial(d, D)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return _trivial(d, D)
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}
    if d < 2 or D < 2 or d > 16:
        return _checked(best, d, D)
    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return _checked(best, d, D)

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return _checked(best, d, D)

    # Lower bound for the order scan: about 0.44 of the Moore bound, and above the start.
    nlo = max(d, best[0] // 2 + 1, int(0.44 * moore) // 2)
    if 2 * nlo > moore:
        return _checked(best, d, D)

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), nlo],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return _checked(best, d, D)
