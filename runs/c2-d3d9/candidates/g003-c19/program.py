"""Combined program: metacyclic bi-Cayley search (upward from the current best, with growing
effort per pass) + voltage-lift fallback + grow-by-two annealing, all in C.

Python builds the best known start graph, C improves it, and build() keeps the best valid
graph it has, so a failure in C can only cost time.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" then m lines "u v" (valid start), or "0 0".
 * stdout: "n m" then m lines "u v": the largest valid graph found.
 *
 * Phases:
 *  1. Bi-Cayley graphs over Z_m x|_r Z_k (order N, 2N vertices). Vertices A_x, B_y;
 *     edges A_x -- B_{x s}, s in S, |S| = d. Left multiplication is an automorphism
 *     transitive on each side, so the diameter is decided by BFS from A_e and B_e.
 *     Passes scan N downward from the Moore limit above the current best, and the
 *     per-N effort doubles each pass that finds nothing.
 *  2. Voltage lifts over the same groups (only if phase 1 gained nothing).
 *  3. Grow by two: add one vertex per side and anneal edge swaps until diameter <= D.
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
#define MAXP 4
#define MAXHALF 1100
#define MAXGRP 8192

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

/* ------------------------------------------------------------------ graph basics */

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
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * (size_t)src->deg[v]);
    }
}

/* ------------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D (0 means diameter <= D and connected). */
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

/* K_{d,d} for D >= 2 (diameter 2); K_2 for D = 1. */
static void complete_bipartite(Graph *g) {
    if (D < 2) {
        g->n = 2;
        g->deg[0] = g->deg[1] = 0;
        g->side[0] = 0; g->side[1] = 1;
        add_edge(g, 0, 1);
        return;
    }
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ groups Z_m x|_r Z_k */

/* Element (a, b) is the int a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct { int m, k, r; } Grp;
static Grp GL[MAXGRP];
static int nGL, nNonab;
static int cm, ck;
static int rpw[MAXN];   /* rpw[b] = r^b mod m for the current group */

static void setgrp(Grp G) {
    cm = G.m;
    ck = G.k;
    for (int b = 0; b < ck; b++)
        rpw[b] = (b == 0) ? (1 % cm) : (int)((long)rpw[b - 1] * G.r % cm);
}

static int gmul(int x, int y) {
    int a = x / ck, b = x % ck, c = y / ck, e = y % ck;
    return (int)(((long)a + (long)rpw[b] * c) % cm) * ck + (b + e) % ck;
}

/* Inverse of (a, b) is (-r^(-b) a, -b), and r^(-b) = r^(k-b) since r^k = 1 mod m. */
static int ginv(int x) {
    int a = x / ck, b = x % ck;
    int nb = (ck - b) % ck;
    int ia = (int)((cm - ((long)rpw[nb] * a) % cm) % cm);
    return ia * ck + nb;
}

/* All metacyclic groups of order N; nonabelian ones first (indices < nNonab). */
static void enum_groups(int N) {
    nGL = 0;
    nNonab = 0;
    for (int pass = 0; pass < 2; pass++) {
        for (int m = 1; m <= N; m++) {
            if (N % m) continue;
            int k = N / m;
            if (m == 1) {
                if (pass == 1 && nGL < MAXGRP) {
                    GL[nGL].m = 1; GL[nGL].k = k; GL[nGL].r = 0; nGL++;
                }
                continue;
            }
            for (int r = 1; r < m; r++) {
                if (gcd(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
                int nonab = (r != 1);
                if ((pass == 0) != nonab) continue;
                if (nGL < MAXGRP) { GL[nGL].m = m; GL[nGL].k = k; GL[nGL].r = r; nGL++; }
            }
        }
        if (pass == 0) nNonab = nGL;
    }
}

/* ------------------------------------------------------------------ bi-Cayley graphs */

/* Random connection set S = {0, s_1, ..., s_{d-1}} of distinct elements, with inverses. */
static void pick_set(int N, int *S, int *Si) {
    S[0] = 0;
    for (int i = 1; i < d; i++) {
        for (;;) {
            int x = 1 + rndint(N - 1), dup = 0;
            for (int j = 0; j < i; j++)
                if (S[j] == x) { dup = 1; break; }
            if (!dup) { S[i] = x; break; }
        }
    }
    for (int i = 0; i < d; i++) Si[i] = ginv(S[i]);
}

/* 1 iff the bi-Cayley graph for the current group and S has diameter <= D. */
static int cay_ok(int N, const int *S, const int *Si) {
    static int dist[2 * MAXHALF], q[2 * MAXHALF];
    int V = 2 * N;
    for (int src = 0; src < 2; src++) {
        int s0 = src ? N : 0;
        for (int v = 0; v < V; v++) dist[v] = -1;
        int head = 0, tail = 0;
        dist[s0] = 0;
        q[tail++] = s0;
        while (head < tail) {
            int v = q[head++];
            int dv = dist[v];
            if (dv >= D) continue;
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int u = N + gmul(v, S[i]);
                    if (dist[u] < 0) { dist[u] = dv + 1; q[tail++] = u; }
                }
            } else {
                int y = v - N;
                for (int i = 0; i < d; i++) {
                    int u = gmul(y, Si[i]);
                    if (dist[u] < 0) { dist[u] = dv + 1; q[tail++] = u; }
                }
            }
        }
        if (tail != V) return 0;
    }
    return 1;
}

/* Try up to `attempts` random (group, S) pairs for order N. On success the group stays
 * set (setgrp) and S is copied to outS. */
static int try_order(int N, long attempts, double until, int *outS) {
    enum_groups(N);
    if (nGL == 0) return 0;
    int S[MAXD], Si[MAXD];
    long left = attempts;
    while (left > 0) {
        if (now() > until) return 0;
        int gi = (nNonab > 0 && rnd01() < 0.8) ? rndint(nNonab) : rndint(nGL);
        setgrp(GL[gi]);
        for (int j = 0; j < 16 && left > 0; j++, left--) {
            pick_set(N, S, Si);
            if (cay_ok(N, S, Si)) {
                memcpy(outS, S, sizeof(int) * (size_t)d);
                return 1;
            }
        }
    }
    return 0;
}

/* Explicit bi-Cayley graph for the current group and S. */
static void build_cayley(Graph *g, int N, const int *S) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) add_edge(g, x, N + gmul(x, S[i]));
}

static void cayley_phase(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    int Nhi = (int)(moore / 2);
    if (Nhi > MAXHALF) Nhi = MAXHALF;
    int lo = best->n / 2 + 1;
    if (lo < d) lo = d;
    if (lo < 2) lo = 2;
    long budget = 300;
    while (now() < until && lo <= Nhi && budget < 1000000000000L) {
        int hit = 0;
        for (int N = Nhi; N >= lo && now() < until; N--) {
            int S[MAXD];
            if (try_order(N, budget, until, S)) {
                build_cayley(&cand, N, S);
                if (is_valid(&cand) && cand.n > best->n) copy_graph(best, &cand);
                lo = N + 1;
                hit = 1;
                break;
            }
        }
        if (!hit) budget *= 2;
    }
}

/* ------------------------------------------------------------------ voltage lifts */

typedef struct { int i, j, g; } Dart;

/* Random d-regular bipartite base multigraph with p vertices per side (sum of d permutations). */
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

static void build_lift(Graph *g, int p, int N, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(x, dt[t].g));
}

/* A voltage not already used by another dart between the same base pair (best effort). */
static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    int g = 0;
    for (int tries = 0; tries < 200; tries++) {
        g = rndint(N);
        int clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
    return g;
}

/* Hill-climb on voltages for the current group (set by setgrp). */
static int lift_try(Graph *g, int p, int N, int steps, double until) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
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
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        int r = rndint(10);
        int p = r < 4 ? 1 : r < 7 ? 2 : r < 9 ? 3 : 4;
        long target = best->n + 2;
        if (target > moore) return;
        int N = (int)((target + 2 * p - 1) / (2 * p)) + rndint(2);
        if (best->n == 0) N = d + rndint(3);
        if (N < d || 2L * p * N > moore || 2 * p * N > MAXN) {
            if (++fails > 1000) return;
            continue;
        }
        enum_groups(N);
        if (nGL == 0) return;
        setgrp(GL[rndint(nGL)]);
        int steps = 200 + 400000 / (2 * p * N);
        if (lift_try(&cand, p, N, steps, until) && cand.n > best->n && is_valid(&cand))
            copy_graph(best, &cand);
    }
}

/* ------------------------------------------------------------------ grow by two */

/* Add one vertex per side (degree d) to a copy of best, then anneal edge swaps.
 * Returns 1 if the result is valid with best->n + 2 vertices. */
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
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
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

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    double t0 = now();
    t_end = t0 + limit * 0.9;

    if (d < 1 || D < 1 || d > MAXD) { printf("0 0\n"); return 0; }

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && d >= 2) {
        long moore = moore_bound();
        if (best.n < moore) {
            double span = t_end - t0;
            long before = best.n;
            cayley_phase(&best, t0 + span * 0.55);
            if (best.n == before) lift_search(&best, t0 + span * 0.65);
            if (best.n > 0) grow_search(&best, t_end);
        }
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if D <= 1:
        return (2, [(0, 1)])                            # K_2 is the Moore graph for D = 1
    start = known_start(d, D)
    if start is None:
        start = lib.haar_graph(d, range(d))             # K_{d,d}, diameter 2
    best = start
    if best[0] >= lib.moore_bound(d, D) or d < 2 or D < 2 or d > 32:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=start, timeout=budget + 10)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass   # keep the valid fallback
    return best
