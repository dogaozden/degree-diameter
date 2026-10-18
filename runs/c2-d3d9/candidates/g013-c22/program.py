"""Bold variant: one C engine with two new search modes, both over voltage lifts.

Mode 1 (descending): for each even order n from the Moore limit down, sample random
voltage lifts (base of p vertices per side, group Z_m x|_r Z_k of order n/(2p)).
Diameter is checked from one representative per fibre, which is exact because left
multiplication by the group is an automorphism transitive on each fibre.

Mode 2 (ascending): simulated annealing on the voltages, minimising the number of
(fibre representative, vertex) pairs at distance > D, aiming at order best + 2.

The start graph from Python (or K_{d,d}) is always kept as the valid fallback.
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
#define MAXD 16
#define MAXW (MAXN / 64)
#define MAXP 6
#define GCAP 20000

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN]; /* 0 = part A, 1 = part B */
} Graph;

static int d, D;

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

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * (size_t)src->deg[v]);
    }
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance > D. */
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

/* Full validity check: simple, bipartite by side labels, degree <= d, diameter <= D. */
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

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a, b) is the int a*k + b; (a,b)(c,e) = (a + r^b c, b + e). */
typedef struct {
    int m, k, r;
    int rp[MAXN]; /* rp[b] = r^b mod m */
} Grp;

static Grp G;

static void set_group(Grp *g, int m, int k, int r) {
    g->m = m;
    g->k = k;
    g->r = r;
    g->rp[0] = 1 % m;
    for (int b = 1; b < k; b++) g->rp[b] = (int)((long)g->rp[b - 1] * r % m);
}

static int gmul(const Grp *g, int x, int y) {
    int a = x / g->k, b = x % g->k, c = y / g->k, e = y % g->k;
    int aa = (int)((a + (long)g->rp[b] * c) % g->m);
    return aa * g->k + (b + e) % g->k;
}

/* All (m, k, r) with m*k = N, gcd(r, m) = 1, r^k = 1 mod m. Includes direct products (r = 1). */
static int GL_m[GCAP], GL_k[GCAP], GL_r[GCAP];
static int cur_list_N = -1, cur_list_c = 0;

static int list_groups(int N) {
    int c = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (c < GCAP) { GL_m[c] = 1; GL_k[c] = k; GL_r[c] = 0; c++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (c < GCAP) { GL_m[c] = m; GL_k[c] = k; GL_r[c] = r; c++; }
        }
    }
    return c;
}

static int groups_for(int N) {
    if (N != cur_list_N) {
        cur_list_c = list_groups(N);
        cur_list_N = N;
    }
    return cur_list_c;
}

/* ------------------------------------------------------------ voltage lifts */

typedef struct { int i, j, g; } Dart; /* base A-vertex i -> base B-vertex j, voltage g */

/* Random d-regular bipartite base multigraph on p + p vertices: sum of d random permutations.
 * M[i][j] = number of darts i -> j. Retried until connected. */
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

/* A voltage not used by another dart between the same base pair (needs N > d). */
static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Random base and random voltages. Returns the number of darts (= d * p). */
static int fill_darts(int p, int N, Dart *dt) {
    int M[MAXP][MAXP];
    make_base(p, M);
    int nd = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    return nd;
}

/* Lift: fibre f occupies vertices f*N .. f*N+N-1; A fibres 0..p-1, B fibres p..2p-1. */
static void build_lift(Graph *g, int p, int N, const Grp *gr, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(gr, x, dt[t].g));
}

/* Left multiplication is an automorphism that is transitive on each fibre, so the diameter
 * is at most D iff every fibre representative reaches all vertices within D steps. */
static int dist_buf[MAXN], queue_buf[MAXN];

static long reach_fail(const Graph *g, int s) {
    int n = g->n;
    for (int v = 0; v < n; v++) dist_buf[v] = -1;
    int head = 0, tail = 0;
    dist_buf[s] = 0;
    queue_buf[tail++] = s;
    while (head < tail) {
        int v = queue_buf[head++];
        if (dist_buf[v] >= D) continue;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (dist_buf[u] < 0) {
                dist_buf[u] = dist_buf[v] + 1;
                queue_buf[tail++] = u;
            }
        }
    }
    return n - tail;
}

/* Zero iff the lift has diameter <= D. */
static long lift_energy(const Graph *g, int p, int N) {
    long E = 0;
    for (int f = 0; f < 2 * p; f++) E += reach_fail(g, f * N);
    return E;
}

/* ------------------------------------------------------------ mode 1: random sampling, descending */

/* Try random lifts of order n = 2pN with the given n. Returns 1 and updates best on success. */
static int try_size(Graph *best, long n, double end) {
    static Graph cand;
    long half = n / 2;
    int cp[MAXP], cc = 0;
    for (int p = 1; p <= MAXP; p++)
        if (half % p == 0 && half / p > d) cp[cc++] = p;
    if (cc == 0) return 0;
    while (now() < end) {
        int p = cp[rndint(cc)];
        int N = (int)(half / p);
        int gc = groups_for(N);
        if (gc == 0) return 0;
        int gi = rndint(gc);
        set_group(&G, GL_m[gi], GL_k[gi], GL_r[gi]);
        Dart dt[MAXD * MAXP];
        int nd = fill_darts(p, N, dt);
        build_lift(&cand, p, N, &G, dt, nd);
        if (lift_energy(&cand, p, N) == 0 && is_valid(&cand)) {
            if (cand.n > best->n) copy_graph(best, &cand);
            return 1;
        }
    }
    return 0;
}

static void search_descending(Graph *best, double until, long moore) {
    long hi = moore & ~1L;
    if (hi > MAXN) hi = MAXN;
    long lo = best->n + 2;
    if (lo < 2L * d + 2) lo = 2L * d + 2;
    if (lo & 1) lo++;
    if (lo > hi) return;
    long count = (hi - lo) / 2 + 1;
    double total = until - now();
    if (total <= 0) return;
    double slice = total / (double)count;
    if (slice < 0.005) slice = 0.005;
    for (long n = hi; n >= lo; n -= 2) {
        double tnow = now();
        if (tnow >= until) break;
        double end = tnow + slice;
        if (end > until) end = until;
        if (try_size(best, n, end)) return;
    }
}

/* ------------------------------------------------------------ mode 2: annealing, ascending */

/* Anneal the voltages of a random base and group of order N until the lift has diameter <= D. */
static int sa_lift(Graph *out, int p, int N, const Grp *gr, double until) {
    static Graph cur;
    Dart dt[MAXD * MAXP];
    int nd = fill_darts(p, N, dt);
    build_lift(&cur, p, N, gr, dt, nd);
    long E = lift_energy(&cur, p, N);
    for (long it = 0; E > 0; it++) {
        if ((it & 63) == 0 && now() > until) return 0;
        double T = 0.3 + 2.0 * exp(-(double)(it % 5000) / 800.0);
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(&cur, p, N, gr, dt, nd);
        long nE = lift_energy(&cur, p, N);
        if (nE <= E || rnd01() < exp(-(double)(nE - E) / T)) E = nE;
        else dt[t].g = old;
    }
    copy_graph(out, &cur);
    return 1;
}

static void search_ascending(Graph *best, double until, long moore) {
    static Graph out;
    while (now() < until) {
        long n = best->n + 2;
        if (n > moore || n > MAXN) return;
        long half = n / 2;
        int cp[MAXP], cc = 0;
        for (int p = 1; p <= MAXP; p++)
            if (half % p == 0 && half / p > d) cp[cc++] = p;
        if (cc == 0) return;
        int p = cp[rndint(cc)];
        int N = (int)(half / p);
        int gc = groups_for(N);
        if (gc == 0) return;
        int gi = rndint(gc);
        set_group(&G, GL_m[gi], GL_k[gi], GL_r[gi]);
        double end = now() + 5.0;
        if (end > until) end = until;
        if (sa_lift(&out, p, N, &G, end) && is_valid(&out) && out.n > best->n)
            copy_graph(best, &out);
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
    double t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    long moore = moore_bound();
    if (D >= 2 && d >= 2 && best.n < moore) {
        search_descending(&best, t0 + (t_end - t0) * 0.4, moore);
        search_ascending(&best, t_end, moore);
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
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget], stdin_graph=start,
                             timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(*out, d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
