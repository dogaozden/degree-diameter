"""Bold variant: ladder search over bi-Cayley (p=1) and small voltage lifts (p=2,3).

Instead of sweeping group orders downward from the Moore limit, C climbs a ladder:
the per-side target is always (best valid graph's side size) + 1, and each attempt
picks a random metacyclic group of order near that target and a random base size p.
p=1 uses bi-Cayley graphs with a fast 2-BFS cost (exact for vertex-transitive sides).
p>=2 uses random d-regular base multigraphs with Z_N-style voltages on a metacyclic
group, annealed with full bad-pair counts. Python supplies a valid fallback and keeps
the best graph C returns, after checking it with lib.is_valid.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter ladder search.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0".
 * stdout:  "n m" then m lines "u v": the best valid graph found.
 *
 * Ladder: per-side target T = best_side + 1. Pick p in {1,2,3} and a group order N
 * near T/p. Pick a random metacyclic group Z_m x|_r Z_k of order N.
 *   p = 1: bi-Cayley graph, connection set S (|S| = d, identity WLOG), annealed on the
 *          count of vertices missed within distance D from A_e and B_e (exact).
 *   p >= 2: voltage lift over a random d-regular base with p vertices per side, annealed
 *          on the full bad-pair count.
 * Any valid graph with more vertices replaces the current best.
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
#define CAYN 1100

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int i, j, g; } Dart;

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

/* K_{1,1}: valid for D >= 1. */
static void trivial_graph(Graph *g) {
    g->n = 2;
    g->deg[0] = g->deg[1] = 0;
    g->side[0] = 0;
    g->side[1] = 1;
    add_edge(g, 0, 1);
}

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k, element (a,b) = a*k+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k). */
static int cmul[CAYN * CAYN];
static int cinv[CAYN];
static int cN = 0;

static void build_group(int m, int k, int r) {
    int N = m * k;
    static int rp[CAYN];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            cmul[x * N + y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++) {
        cinv[x] = 0;
        for (int y = 0; y < N; y++)
            if (cmul[x * N + y] == 0) { cinv[x] = y; break; }
    }
    cN = N;
}

/* Uniformly random metacyclic (m, k, r) with m*k = N, gcd(r,m) = 1, r^k = 1 mod m. */
static int pick_group(int N, int *pm, int *pk, int *pr) {
    long cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            cnt++;
            if (rndint((int)cnt) == 0) { *pm = 1; *pk = k; *pr = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { *pm = m; *pk = k; *pr = r; }
        }
    }
    return cnt > 0;
}

/* ------------------------------------------------------------------ bi-Cayley (p = 1) */

static int cS[MAXD], cSi[MAXD];
static int cdist[2 * CAYN], cq[2 * CAYN];

/* Vertices missed within distance D from A_e and from B_e (0 means valid). */
static long cay_cost(void) {
    int N = cN, V = 2 * N;
    long miss = 0;
    for (int i = 0; i < d; i++) cSi[i] = cinv[cS[i]];
    for (int src = 0; src < 2; src++) {
        int s0 = src ? N : 0;
        for (int v = 0; v < V; v++) cdist[v] = -1;
        int head = 0, tail = 0;
        cdist[s0] = 0;
        cq[tail++] = s0;
        while (head < tail) {
            int v = cq[head++];
            if (cdist[v] >= D) continue;
            if (v < N) {
                const int *row = cmul + v * N;
                for (int i = 0; i < d; i++) {
                    int u = N + row[cS[i]];
                    if (cdist[u] < 0) { cdist[u] = cdist[v] + 1; cq[tail++] = u; }
                }
            } else {
                const int *row = cmul + (v - N) * N;
                for (int i = 0; i < d; i++) {
                    int u = row[cSi[i]];
                    if (cdist[u] < 0) { cdist[u] = cdist[v] + 1; cq[tail++] = u; }
                }
            }
        }
        miss += V - tail;
    }
    return miss;
}

/* Anneal the connection set over the current group. Returns 1 with cS valid. */
static int cay_sa(long steps, double until) {
    int N = cN;
    cS[0] = 0;
    for (int c = 1; c < d;) {
        int x = 1 + rndint(N - 1), dup = 0;
        for (int i = 0; i < c; i++)
            if (cS[i] == x) { dup = 1; break; }
        if (!dup) cS[c++] = x;
    }
    long cur = cay_cost();
    for (long s = 0; s < steps && cur > 0; s++) {
        if ((s & 127) == 0 && now() > until) return 0;
        double T = 1.5 * (1.0 - (double)s / (double)steps) + 0.1;
        int i = 1 + rndint(d - 1), x, dup;
        do {
            x = 1 + rndint(N - 1);
            dup = 0;
            for (int j = 0; j < d; j++)
                if (cS[j] == x) { dup = 1; break; }
        } while (dup);
        int old = cS[i];
        cS[i] = x;
        long c2 = cay_cost();
        if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) cur = c2;
        else cS[i] = old;
    }
    return cur == 0;
}

static void cay_graph(Graph *g) {
    int N = cN;
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) add_edge(g, x, N + cmul[x * N + cS[i]]);
}

/* ------------------------------------------------------------------ voltage lifts (p >= 2) */

/* Random d-regular bipartite base multigraph, p vertices per side, connected. */
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

/* A voltage not used by another dart between the same base pair. */
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
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + cmul[x * N + dt[t].g]);
}

/* Anneal voltages over the current group (cN = N). On success out holds a lift with 2pN vertices. */
static int lift_sa(int p, long steps, double until, Graph *out) {
    int N = cN;
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(out, p, N, dt, nd);
    long bad = bad_pairs(out);
    for (long s = 0; s < steps && bad > 0; s++) {
        if ((s & 15) == 0 && now() > until) return 0;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(out, p, N, dt, nd);
        long nb = bad_pairs(out);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
    }
    if (bad != 0) return 0;
    build_lift(out, p, N, dt, nd);
    return 1;
}

/* ------------------------------------------------------------------ ladder */

static void ladder(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    while (now() < until) {
        long T = best->n / 2 + 1;   /* per-side target */
        int r = rndint(10);
        int p = r < 5 ? 1 : (r < 8 ? 2 : 3);
        long Nl = (T + p - 1) / p;
        long Nl2 = Nl + rndint(3);
        if (Nl2 <= d || Nl2 >= CAYN) continue;
        int N = (int)Nl2;
        if ((long)2 * p * N > moore || 2 * p * N > MAXN) continue;
        int m, k, rr;
        if (!pick_group(N, &m, &k, &rr)) continue;
        build_group(m, k, rr);
        double cap = now() + (p == 1 ? 3.0 : 6.0);
        if (cap > until) cap = until;
        int ok;
        if (p == 1) {
            ok = cay_sa(40000, cap);
            if (ok) cay_graph(&cand);
        } else {
            ok = lift_sa(p, 3000, cap, &cand);
        }
        if (ok && cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
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
    if (d < 1 || D < 1 || d > MAXD) {
        trivial_graph(&best);
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    if (best.n == 0) {
        if (D >= 2) complete_bipartite(&best);
        else trivial_graph(&best);
    }
    if (D >= 2 && d >= 2 && best.n < moore_bound()) ladder(&best, t_end);
    if (!is_valid(&best)) {
        if (D >= 2) complete_bipartite(&best);
        if (!is_valid(&best)) trivial_graph(&best);
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


def _fallback(d, D):
    """A valid graph that needs no C engine (checked with lib.is_valid)."""
    candidates = []
    s = known_start(d, D)
    if s is not None:
        candidates.append(s)
    candidates.append(lib.haar_graph(d, range(d)))   # K_{d,d}
    candidates.append((2, [(0, 1)]))                  # K_{1,1}
    for g in candidates:
        if lib.is_valid(g[0], g[1], d, D):
            return g
    return (2, [(0, 1)])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    best = _fallback(d, D)
    if best[0] >= lib.moore_bound(d, D) or d < 2 or D < 2:
        return best   # Moore graph, or nothing for the engine to improve
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError, OSError):
        pass   # keep the valid fallback
    return best
