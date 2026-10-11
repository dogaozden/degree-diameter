import random
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley lift search with Metropolis annealing over random semidirect groups.
 *
 * Usage:  prog d D seed time_limit   < start_graph
 * stdin:  "n m" + m edge lines (valid start), or "0 0".
 * stdout: "n m" + m edge lines, the largest valid graph found.
 *
 * Model: k vertices per side, group G = Z_m x| Z_k2 of order N.
 * Layer l is a permutation perm_l of {0..k-1}; dart t = (l, i) joins
 *   A_{i,g} ~ B_{perm_l(i), g * s_t}   for all g in G.
 * Left multiplication by G is an automorphism, so diameter <= D reduces to
 * BFS from the 2k representatives A_{i,e}, B_{j,e}.
 * Cost = unreached (rep, vertex) pairs + DUP_PEN * duplicate darts.
 * Moves: change one voltage, or swap two targets inside one layer.
 * Each attempt uses a fresh random group and random darts, then anneals.
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
#define MAXG 512
#define MAXK 3
#define MAXT (MAXD * MAXK)
#define DUP_PEN 100000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static long moore;
static Graph best;

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

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
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

/* Z_m x|_r Z_k2: element (a,b) = a*k2+b; (a,b)(c,e) = (a + r^b c mod m, b+e mod k2). */
static int RP[MAXG];
static int MT[MAXG * MAXG];

static void set_group(int N, int m, int k2, int r) {
    RP[0] = 1 % m;
    for (int b = 1; b < k2; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < N; y++) {
            int c = y / k2, e = y % k2;
            MT[x * N + y] = (int)(((long)a + (long)RP[b] * c) % m) * k2 + (b + e) % k2;
        }
    }
}

static void random_group(int N) {
    long cnt = 0;
    int bm = 1, bk = N, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k2 = N / m;
        for (int r = 0; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k2, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { bm = m; bk = k2; br = r; }
        }
    }
    set_group(N, bm, bk, br);
}

/* ------------------------------------------------------------ lifts */

static int K_, N_, ND_;
static int DI[MAXT], DJ[MAXT], DS[MAXT];

static int adjL[MAXN][MAXD];
static int degL[MAXN];
static int visL[MAXN];
static int qL[MAXN];
static int stampL = 0;

static long lift_cost(void) {
    int k = K_, N = N_, n = 2 * k * N;
    long dup = 0;
    for (int t = 0; t < ND_; t++)
        for (int u = 0; u < t; u++)
            if (DI[t] == DI[u] && DJ[t] == DJ[u] && DS[t] == DS[u]) dup++;
    for (int v = 0; v < n; v++) degL[v] = 0;
    for (int t = 0; t < ND_; t++)
        for (int g = 0; g < N; g++) {
            int a = DI[t] * N + g;
            int b = (k + DJ[t]) * N + MT[g * N + DS[t]];
            adjL[a][degL[a]++] = b;
            adjL[b][degL[b]++] = a;
        }
    long unreached = 0;
    for (int r = 0; r < 2 * k; r++) {
        int src = (r < k) ? r * N : (k + (r - k)) * N;
        stampL++;
        int head = 0, tail = 0;
        visL[src] = stampL;
        qL[tail++] = src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = qL[head++];
                for (int i = 0; i < degL[u]; i++) {
                    int v = adjL[u][i];
                    if (visL[v] != stampL) { visL[v] = stampL; qL[tail++] = v; }
                }
            }
        }
        unreached += n - tail;
    }
    return dup * DUP_PEN + unreached;
}

static void build_lift(Graph *g) {
    int k = K_, N = N_;
    g->n = 2 * k * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= k * N; }
    for (int t = 0; t < ND_; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, DI[t] * N + x, (k + DJ[t]) * N + MT[x * N + DS[t]]);
}

static void random_darts(void) {
    int k = K_, N = N_;
    ND_ = d * k;
    int perm[MAXK];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1), s = perm[i];
            perm[i] = perm[j];
            perm[j] = s;
        }
        for (int i = 0; i < k; i++) {
            int t = l * k + i;
            DI[t] = i;
            DJ[t] = perm[i];
            DS[t] = rndint(N);
        }
    }
}

/* Simulated annealing on the darts of the current group. Returns final cost. */
static long sa_run(long steps, double until) {
    int k = K_, N = N_;
    long c = lift_cost();
    const double T0 = 1.0, T1 = 0.03;
    for (long s = 0; s < steps && c > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        double T = T0 * pow(T1 / T0, (double)s / (double)steps);
        if (k > 1 && rnd01() < 0.25) {
            int l = rndint(d), a = rndint(k), b = rndint(k);
            if (a == b) continue;
            int t1 = l * k + a, t2 = l * k + b;
            int tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp;
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < exp((double)(c - c2) / T)) c = c2;
            else { tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp; }
        } else {
            int t = rndint(ND_);
            int old = DS[t];
            DS[t] = rndint(N);
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < exp((double)(c - c2) / T)) c = c2;
            else DS[t] = old;
        }
    }
    return c;
}

/* Repeated short annealing runs over fresh random groups, aiming just above the best order. */
static void search(double until) {
    static const int kc[7] = {1, 1, 1, 1, 2, 2, 3};
    static Graph cand;
    int fails = 0;
    while (now() < until && best.n < moore && fails < 200000) {
        int k = kc[rndint(7)];
        long Nmin = best.n / (2 * k) + 1;
        long N = Nmin + rndint(3);
        if (N < 1 || N > MAXG || 2 * k * N > moore || 2 * k * N > MAXN) {
            fails++;
            continue;
        }
        K_ = k;
        N_ = (int)N;
        random_group(N_);
        random_darts();
        long c = sa_run(30000, until);
        if (c == 0) {
            build_lift(&cand);
            if (cand.n > best.n && is_valid(&cand)) best = cand;
        }
    }
}

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
    double t0 = now();
    t_end = t0 + limit * 0.96;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    moore = compute_moore();

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (best.n < moore) search(t_end);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _known_start(d, D):
    """Best directly constructible graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def _haar_fallback(d, D, best, deadline, seed):
    """Pure-Python fallback if the C engine fails: random cyclic Haar graphs, N ascending."""
    rng = random.Random(seed)
    moore = lib.moore_bound(d, D)
    N = max(best[0] // 2 + 1, d)
    while time.monotonic() < deadline and 2 * N <= moore:
        found = None
        for _ in range(20):
            if time.monotonic() > deadline:
                break
            S = rng.sample(range(N), d)
            n, edges = lib.haar_graph(N, S)
            if lib.is_valid(n, edges, d, D):
                found = (n, edges)
                break
        if found is None:
            break
        if found[0] > best[0]:
            best = found
        N += 1
    return best


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

    budget = 0.93 * time_limit - (time.monotonic() - t0) - 1.5
    c_ok = False
    if budget >= 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 3)
            consider(lib.parse_graph_text(text))
            c_ok = True
        except (RuntimeError, ValueError, OSError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    if not c_ok:
        deadline = t0 + 0.95 * time_limit
        cand = _haar_fallback(d, D, best, deadline, seed)
        if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
    return best
