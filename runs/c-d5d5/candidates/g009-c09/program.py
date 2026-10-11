"""Bold variant: bi-Cayley lifts over k-vertex-per-side base graphs with arbitrary
semidirect groups, searched by simulated annealing on darts. The engine tracks the
exact diameter cost by BFS from one representative per side (translation symmetry)
and climbs the order in steps of two. Falls back to K_{d,d} or the known start."""
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley lift annealer.
 * Usage: prog d D seed time_limit   (stdin: start graph, ignored apart from consumption)
 * Vertices: left (i,g) -> i*N+g, right (j,h) -> (k+j)*N+h, group Z_m x|_r Z_k2 of order N.
 * Darts t: left i = t/d, right j = DJ[t], voltage s = DS[t]; edge (i,g)-(j, g*s).
 * Cost: 1e6 * duplicate darts + unreached (representative, vertex) pairs within D.
 * Translation by the group is an automorphism, so BFS from the 2k representatives
 * decides the diameter exactly.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1024
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXG 512
#define MAXK 3
#define MAXKD (MAXK * MAXD)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static long moore;
static Graph best;

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

static long compute_moore(void) {
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

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
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

/* Z_m x|_r Z_k2 with element (a,b) = a*k2+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int GN;
static int RP[MAXG];
static int MT[MAXG * MAXG];
static int INV[MAXG];

static void set_group(int N, int m, int k2, int r) {
    GN = N;
    RP[0] = 1 % m;
    for (int b = 1; b < k2; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < N; y++) {
            int c = y / k2, e = y % k2;
            MT[x * N + y] = (int)(((long)a + (long)RP[b] * c) % m) * k2 + (b + e) % k2;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INV[x] = y; break; }
}

/* Uniform choice among all semidirect groups of order N. */
static void random_group(int N) {
    int cnt = 0, bm = 1, bk = N, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k2 = N / m;
        for (int r = 0; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k2, m) != 1 % m) continue;
            cnt++;
            if (rndint(cnt) == 0) { bm = m; bk = k2; br = r; }
        }
    }
    set_group(N, bm, bk, br);
}

/* ------------------------------------------------------------ lifts */

static int Kc, Nc;
static int DI[MAXKD], DJ[MAXKD], DS[MAXKD];
static int vis[MAXN], qq[MAXN];
static int stampC = 0;

static void randomize_darts(void) {
    int k = Kc, N = Nc, kd = k * d;
    int arr[MAXKD];
    for (int t = 0; t < kd; t++) {
        DI[t] = t / d;
        DS[t] = rndint(N);
        arr[t] = t % k;          /* every right vertex gets exactly d darts */
    }
    for (int i = kd - 1; i > 0; i--) {
        int j = rndint(i + 1), s = arr[i];
        arr[i] = arr[j];
        arr[j] = s;
    }
    for (int t = 0; t < kd; t++) DJ[t] = arr[t];
}

static long lift_cost(void) {
    int k = Kc, N = Nc, kd = k * d, V = 2 * k * N;
    long pen = 0;
    for (int t = 0; t < kd; t++)
        for (int u = 0; u < t; u++)
            if (DI[t] == DI[u] && DJ[t] == DJ[u] && DS[t] == DS[u]) pen++;
    int rc[MAXK], rl[MAXK][MAXD];
    for (int j = 0; j < k; j++) rc[j] = 0;
    for (int t = 0; t < kd; t++) { int j = DJ[t]; rl[j][rc[j]++] = t; }

    long unreached = 0;
    for (int r = 0; r < 2 * k; r++) {
        stampC++;
        int src = r * N, head = 0, tail = 0;
        vis[src] = stampC;
        qq[tail++] = src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = qq[head++];
                if (u < k * N) {
                    int i = u / N, g = u % N;
                    for (int l = 0; l < d; l++) {
                        int t = i * d + l;
                        int v = (k + DJ[t]) * N + MT[g * N + DS[t]];
                        if (vis[v] != stampC) { vis[v] = stampC; qq[tail++] = v; }
                    }
                } else {
                    int x = u - k * N, j = x / N, h = x % N;
                    for (int l = 0; l < rc[j]; l++) {
                        int t = rl[j][l];
                        int v = DI[t] * N + MT[h * N + INV[DS[t]]];
                        if (vis[v] != stampC) { vis[v] = stampC; qq[tail++] = v; }
                    }
                }
            }
        }
        unreached += V - tail;
    }
    return pen * 1000000L + unreached;
}

static void build_lift(Graph *g) {
    int k = Kc, N = Nc, kd = k * d;
    g->n = 2 * k * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= k * N; }
    for (int t = 0; t < kd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, DI[t] * N + x, (k + DJ[t]) * N + MT[x * N + DS[t]]);
}

/* Simulated annealing on one (group, darts) instance. Returns 1 if cost reaches 0. */
static int anneal(long steps, double until) {
    int kd = Kc * d;
    long c = lift_cost();
    for (long s = 0; s < steps && c > 0; s++) {
        if ((s & 1023) == 0 && now() > until) break;
        double T = 2.0 * pow(0.025, (double)s / (double)steps);
        if (rnd01() < 0.5) {
            int t = rndint(kd), old = DS[t], ns = rndint(Nc);
            if (ns == old) continue;
            DS[t] = ns;
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) c = c2;
            else DS[t] = old;
        } else {
            int t1 = rndint(kd), t2 = rndint(kd);
            if (DJ[t1] == DJ[t2]) continue;
            int tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp;
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) c = c2;
            else { tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp; }
        }
    }
    return c == 0;
}

static Graph cand;

static void lift_phase(double until) {
    int fails = 0;
    while (now() < until && best.n < moore && fails < 100000) {
        int k = 1 + rndint(MAXK);
        long target = best.n + 2;
        long N = (target + 2 * k - 1) / (2 * k) + rndint(2);
        if (N < d || N > MAXG || 2 * k * N > moore || 2 * k * N > MAXN) {
            fails++;
            continue;
        }
        Kc = k;
        Nc = (int)N;
        random_group(Nc);
        randomize_darts();
        if (anneal(120000, until)) {
            build_lift(&cand);
            if (cand.n > best.n && is_valid(&cand)) copy_graph(&best, &cand);
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
    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    /* Consume the start graph (not needed by this search). */
    int sn, sm;
    if (scanf("%d %d", &sn, &sm) == 2) {
        for (int e = 0; e < sm; e++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) break;
        }
    }

    double t0 = now();
    double t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    moore = compute_moore();

    complete_bipartite(&best);
    if (best.n < moore) lift_phase(t_end);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _known_start(d, D):
    """Best directly constructible graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record family 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return (1, [])
    if D == 1:
        return (2, [(0, 1)])

    best = lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand

    start = _known_start(d, D)
    if start is not None:
        consider(start)

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5)
        consider(lib.parse_graph_text(text))
    except (RuntimeError, ValueError):
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
