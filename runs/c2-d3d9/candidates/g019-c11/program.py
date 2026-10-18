"""Bold variant for the weakest parent (d3D9): add non-metacyclic bi-Cayley search.

New C stage: bi-Cayley graphs (p = 1 lifts with d darts) over groups
G = (Z_m semidirect Z_k) x Z_s. Those groups are not metacyclic when gcd(k, s) > 1, so they
are a different family from the Z_m semidirect Z_k lifts of the old search. Python passes a
list of group parameters (m prime, k | m-1, s >= 1) with orders just above goal/2. Voltages are
found by simulated annealing on the number of bad pairs. The old lift search and the
grow-by-two annealing run before and after it, so a valid graph is always kept.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit [goal [m k r s]...]   < start_graph
 * stdin:   "n m" then m lines "u v": a known-valid starting graph, or "0 0" for none.
 * goal:    optional known record order.
 * m k r s: optional groups G = (Z_m semidirect_r Z_k) x Z_s, given as quadruples.
 *          Each gives bi-Cayley graphs (p = 1 lifts with d darts) of order 2*m*k*s.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Stages:
 *   1. Voltage lifts over semidirect groups Z_m x| Z_k with hill-climbing.
 *   2. Bi-Cayley annealing over the given (possibly non-metacyclic) groups.
 *   3. Grow by two: insert one vertex per side, then anneal edge swaps.
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
#define MAXG 128

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN]; /* 0 = part A, 1 = part B */
} Graph;

static int d, D;
static double t_end;
static long goal_n = 0;

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
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

/* ------------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN]; /* badv[v] = vertices farther than D from v, after bad_pairs() */

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
        badv[v] = n - c;
        total += n - c;
    }
    return total / 2;
}

/* Full validity check: simple, bipartite (by side labels), degree <= d, diameter <= D. */
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

/* Read "n m" + edges from stdin; 2-colour it. Leaves g->n = 0 if absent or invalid. */
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

/* K_{d,d}: always valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ groups */

/* G = (Z_m semidirect_r Z_k) x Z_s. Element x = ((a*k + b)*s + c), with a in Z_m, b in Z_k,
 * c in Z_s. Product: (a,b)(a',b') = (a + r^b a', b + b'), and c adds mod s. */
typedef struct {
    int m, k, r, s, N;
    int rp[MAXN]; /* rp[b] = r^b mod m */
} Grp;

static int grp_init(Grp *G, int m, int k, int r, int s) {
    if (m < 1 || k < 1 || s < 1) return 0;
    long N = (long)m * k * s;
    if (N < 2 || N > MAXN) return 0;
    r = ((r % m) + m) % m;
    if (m > 1 && gcd(r, m) != 1) return 0;
    if (powmod(r, k, m) != 1 % m) return 0;
    G->m = m; G->k = k; G->r = r; G->s = s; G->N = (int)N;
    G->rp[0] = 1 % m;
    for (int b = 1; b < k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * r % m);
    return 1;
}

static int gmul(const Grp *G, int x, int y) {
    int c1 = x % G->s, x1 = x / G->s;
    int c2 = y % G->s, y1 = y / G->s;
    int a = x1 / G->k, b = x1 % G->k;
    int c = y1 / G->k, e = y1 % G->k;
    int na = (int)(((long)a + (long)G->rp[b] * c) % G->m);
    int nb = (b + e) % G->k;
    int ns = (c1 + c2) % G->s;
    return (na * G->k + nb) * G->s + ns;
}

/* Pick a uniformly random semidirect (m, k, r) with m*k = N (s = 1). */
static int random_group(int N, Grp *G) {
    long count = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)(count < 2000000000L ? count : 2000000000L)) == 0) {
                bm = m; bk = k; br = r;
            }
        }
    }
    if (!count) return 0;
    return grp_init(G, bm, bk, br, 1);
}

/* ------------------------------------------------------------------ voltage lifts */

typedef struct { int i, j, g; } Dart;

/* Random d-regular bipartite base multigraph with p vertices per side, connected. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) { int j = rndint(i + 1); int s = perm[i]; perm[i] = perm[j]; perm[j] = s; }
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

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static int lift_try(Graph *g, int p, int N, const Grp *G, int steps) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i; dt[nd].j = j;
                dt[nd].g = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(g, p, N, G, dt, nd);
    long bad = bad_pairs(g);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 15) == 0 && now() > t_end) return 0;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, G, dt, nd);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < 0.01) bad = nb;
        else dt[t].g = old;
    }
    if (bad != 0) return 0;
    return 1;
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        int r = rndint(10);
        int p = r < 4 ? 1 : r < 7 ? 2 : r < 9 ? 3 : 4;
        long target = best->n + 2;
        if (goal_n > target && rndint(2) == 0) target = goal_n;
        if (target > moore) return;
        int base_N = (int)((target + 2 * p - 1) / (2 * p));
        int jitter = 2 + base_N / 16;
        int N = base_N + rndint(jitter);
        if (best->n == 0) N = d + rndint(3);
        if (N < d || 2L * p * N > moore || 2 * p * N > MAXN) {
            if (++fails > 1000) return;
            continue;
        }
        if (!random_group(N, &G)) continue;
        int steps = 200 + 400000 / (2 * p * N);
        if (lift_try(&cand, p, N, &G, steps) && cand.n > best->n && is_valid(&cand))
            copy_graph(best, &cand);
    }
}

/* ------------------------------------------------------------------ bi-Cayley search */

static Grp groups[MAXG];

/* Bi-Cayley graph: a_x ~ b_{x * g_t} for x in G and each voltage g_t, t < nd. */
static void build_bicayley(Graph *g, const Grp *G, const int *gv, int nd) {
    int N = G->N;
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, x, N + gmul(G, x, gv[t]));
}

/* Anneal distinct voltages (gv[0] = identity WLOG) on group G until the bi-Cayley graph has
 * diameter <= D. On success copies it into out (which must be smaller) and returns 1. */
static int bicayley_try(Graph *out, const Grp *G, double until) {
    static Graph cand;
    int N = G->N, nd = d;
    int gv[MAXD];
    if (nd < 2 || nd > MAXD || nd > N || 2L * N > moore_bound()) return 0;
    while (now() < until) {
        gv[0] = 0;
        for (int t = 1; t < nd; t++) {
            for (;;) {
                int g = rndint(N), ok = 1;
                for (int j = 0; j < t; j++) if (gv[j] == g) { ok = 0; break; }
                if (ok) { gv[t] = g; break; }
            }
        }
        build_bicayley(&cand, G, gv, nd);
        long bad = bad_pairs(&cand);
        double T = 1.0;
        for (long it = 0; it < 20000 && bad > 0; it++) {
            if ((it & 31) == 0 && now() > until) return 0;
            int t = 1 + rndint(nd - 1), old = gv[t], g;
            for (;;) {
                g = rndint(N);
                int ok = 1;
                for (int j = 0; j < nd; j++) if (gv[j] == g) { ok = 0; break; }
                if (ok) break;
            }
            gv[t] = g;
            build_bicayley(&cand, G, gv, nd);
            long nb = bad_pairs(&cand);
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
                bad = nb;
            } else {
                gv[t] = old;
                build_bicayley(&cand, G, gv, nd);
            }
            T *= 0.9995;
            if (T < 0.05) T = 1.0;
        }
        if (bad == 0 && 2L * N > out->n && is_valid(&cand)) {
            copy_graph(out, &cand);
            return 1;
        }
    }
    return 0;
}

static int group_eligible(const Graph *best, const Grp *G) {
    long o = 2L * G->N;
    return o > best->n && o <= moore_bound();
}

static void group_search(Graph *best, int ng, double until) {
    while (now() < until) {
        int any = 0;
        for (int i = 0; i < ng; i++) if (group_eligible(best, &groups[i])) { any = 1; break; }
        if (!any) return;
        int i = rndint(ng);
        if (!group_eligible(best, &groups[i])) continue;
        bicayley_try(best, &groups[i], until);
    }
}

/* ------------------------------------------------------------------ grow by two */

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

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [goal [m k r s]...] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    goal_n = argc > 5 ? atol(argv[5]) : 0;

    int ng = 0;
    for (int a = 6; a + 3 < argc && ng < MAXG; a += 4) {
        if (grp_init(&groups[ng], atoi(argv[a]), atoi(argv[a + 1]),
                     atoi(argv[a + 2]), atoi(argv[a + 3])))
            ng++;
    }

    double t0 = now();
    t_end = t0 + limit * 0.92;
    double span = t_end - t0;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    int had_start = best.n > 0;

    if (D >= 2 && best.n < moore_bound()) {
        lift_search(&best, t0 + span * (had_start ? 0.3 : 0.45));
        if (ng > 0) group_search(&best, ng, t0 + span * 0.85);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''

# Known record orders, passed to the C engine as a search goal.
RECORD_GOAL = {(3, 9): 506}
MAX_GROUPS = 60


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def _prime_factors(n):
    f, p = set(), 2
    while p * p <= n:
        while n % p == 0:
            f.add(p)
            n //= p
        p += 1
    if n > 1:
        f.add(n)
    return f


def _primitive_root(q):
    fac = _prime_factors(q - 1)
    for g in range(2, q):
        if all(pow(g, (q - 1) // p, q) != 1 for p in fac):
            return g
    return 1


def group_params(goal, d):
    """Quadruples (m, k, r, s) for G = (Z_m semidirect_r Z_k) x Z_s with m prime, k | m-1, r of
    order k, so that 2|G| > goal. Orders are kept just above goal/2 (smaller first)."""
    if goal <= 0 or d < 2:
        return []
    lo = goal // 2 + 1
    hi = lo + 60
    found = []
    for q in range(3, hi + 1):
        if any(q % p == 0 for p in range(2, int(q ** 0.5) + 1)):
            continue
        g = _primitive_root(q)
        for k in range(2, q):
            if (q - 1) % k:
                continue
            r = pow(g, (q - 1) // k, q)
            for s in range(1, hi // (q * k) + 1):
                N = q * k * s
                if lo <= N <= hi:
                    found.append((N, q, k, r, s))
    found.sort()
    return [(q, k, r, s) for N, q, k, r, s in found]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: always valid
    if not lib.is_valid(*best, d, D):
        best = lib.haar_graph(d, range(d))

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        goal = RECORD_GOAL.get((d, D), 0)
        args = [d, D, seed, round(budget, 2), goal]
        for q, k, r, s in group_params(goal, d)[:MAX_GROUPS]:
            args += [q, k, r, s]
        try:
            text = lib.run_c(C_SOURCE, args, stdin_graph=start, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(*out, d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
