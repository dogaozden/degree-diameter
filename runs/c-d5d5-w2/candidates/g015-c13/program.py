"""Bold variant: a fixed-size annealing engine replaces the old grow-by-two phase.

Phase 1 runs a short bi-Cayley lift search (semidirect-product voltages, orbit-reduced cost)
to get a first large valid graph. Phase 2 grows that graph by two vertices at a time. Each
growth step keep the graph d-regular and bipartite, then anneals degree-preserving
cross-side double swaps to remove all bad pairs. Every accepted state is re-checked with a
full validity test. Python gives C about 85% of the per-case budget and keeps a valid
K_{d,d} or known-construction fallback.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter engine, variant: lift start + fixed-size annealing growth.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1: random bi-Cayley lifts over Z_m x| Z_k2 (k vertices per side), hill-climbed on
 *          unreached (representative, vertex) pairs. Stops early on stall.
 * Phase 2: from the current best (d-regular, bipartite) add two vertices by stealing edges,
 *          then Metropolis-anneal double swaps across sides until bad pairs = 0.
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

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static long moore;
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
static int badv[MAXN];

/* Unordered pairs at distance > D, via bitset reachability over D rounds. */
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

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k2: element (a,b) = a*k2+b; (a,b)(c,e) = (a + r^b c mod m, b+e mod k2). */
static int GM, GK, GR;
static int RP[MAXG];
static int MT[MAXG * MAXG];

static void set_group(int N, int m, int k2, int r) {
    GM = m; GK = k2; GR = r;
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

/* Uniform random (m, k2, r) with m*k2 = N, gcd(r,m) = 1, r^k2 = 1 mod m. */
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

/* ------------------------------------------------------------------ lifts */

static int K_, N_, nd_;
static int dI[MAXD * MAXK], dJ[MAXD * MAXK], dS[MAXD * MAXK];

static int adjL[MAXN][MAXD];
static int degL[MAXN];
static int visL[MAXN];
static int qL[MAXN];
static int stampL = 0;

/* Cost = 1e6 * duplicate darts + total unreached (representative, vertex) pairs. */
static long lift_cost(void) {
    int k = K_, N = N_, n = 2 * k * N;
    long pen = 0;
    for (int t = 0; t < nd_; t++)
        for (int u = 0; u < t; u++)
            if (dI[t] == dI[u] && dJ[t] == dJ[u] && dS[t] == dS[u]) pen++;
    for (int v = 0; v < n; v++) degL[v] = 0;
    for (int t = 0; t < nd_; t++)
        for (int g = 0; g < N; g++) {
            int a = dI[t] * N + g;
            int b = (k + dJ[t]) * N + MT[g * N + dS[t]];
            adjL[a][degL[a]++] = b;
            adjL[b][degL[b]++] = a;
        }
    long unreached = 0;
    int reps[2 * MAXK], nr = 0;
    for (int i = 0; i < k; i++) reps[nr++] = i * N;
    for (int j = 0; j < k; j++) reps[nr++] = (k + j) * N;
    for (int r = 0; r < nr; r++) {
        stampL++;
        int head = 0, tail = 0;
        int src = reps[r];
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
    return pen * 1000000L + unreached;
}

static void build_lift(Graph *g) {
    int k = K_, N = N_;
    g->n = 2 * k * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= k * N; }
    for (int t = 0; t < nd_; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dI[t] * N + x, (k + dJ[t]) * N + MT[x * N + dS[t]]);
}

/* Hill-climb the darts of a fresh random lift. Returns 1 if cost reaches 0. */
static int lift_attempt(int steps, double until) {
    int k = K_, N = N_;
    nd_ = d * k;
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
            dI[t] = i;
            dJ[t] = perm[i];
            dS[t] = rndint(N);
        }
    }
    long c = lift_cost();
    for (int s = 0; s < steps && c > 0; s++) {
        if ((s & 255) == 0 && now() > until) break;
        if (k > 1 && rnd01() < 0.15) {
            int l = rndint(d), a = rndint(k), b = rndint(k);
            if (a == b) continue;
            int t1 = l * k + a, t2 = l * k + b;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < 0.01) c = c2;
            else { tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp; }
        } else {
            int t = rndint(nd_);
            int old = dS[t];
            dS[t] = rndint(N);
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < 0.01) c = c2;
            else dS[t] = old;
        }
    }
    return c == 0;
}

static void lift_phase(Graph *best, double until) {
    static Graph cand;
    double start = now();
    double stall = 0.5 * (until - start);
    double last_gain = start;
    int fails = 0;
    while (now() < until && best->n < moore) {
        if (now() - last_gain > stall) return;
        int k = (rndint(3) == 0) ? 2 : 1;
        long target = best->n + 2;
        long Nl = (target + 2 * k - 1) / (2 * k) + rndint(3);
        if (Nl < 1 || Nl > MAXG || 2 * k * Nl > moore || 2 * k * Nl > MAXN) {
            if (++fails > 5000) return;
            continue;
        }
        K_ = k;
        N_ = (int)Nl;
        random_group(N_);
        if (lift_attempt(20000, until)) {
            build_lift(&cand);
            if (cand.n > best->n && is_valid(&cand)) {
                copy_graph(best, &cand);
                last_gain = now();
            }
        }
    }
}

/* ------------------------------------------------------------------ grow + anneal */

/* Add two vertices x (side 0), y (side 1) joined to each other; steal d-1 edges
   a-b (a side 0, b side 1) and rewire to x-b and y-a. Stays d-regular and bipartite. */
static int grow_start(const Graph *base, Graph *w) {
    int n = base->n;
    if (n + 2 > moore || n + 2 > MAXN) return 0;
    copy_graph(w, base);
    int x = n, y = n + 1;
    w->n = n + 2;
    w->deg[x] = w->deg[y] = 0;
    w->side[x] = 0;
    w->side[y] = 1;
    add_edge(w, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (w->side[a] != 0 || used[a] == stamp || w->deg[a] == 0) continue;
        int b = w->adj[a][rndint(w->deg[a])];
        if (b >= n || used[b] == stamp) continue;
        del_edge(w, a, b);
        add_edge(w, x, b);
        add_edge(w, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
    return k == d - 1;
}

/* Metropolis on bad pairs with cross-side double swaps (regularity preserved). */
static int anneal(Graph *g, double until) {
    long bad = bad_pairs(g);
    double T = 0.5;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(g->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(g->n);
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
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(g, v, t);
            del_edge(g, s, u);
            add_edge(g, v, u);
            add_edge(g, s, t);
        }
        T *= 0.9995;
        if (T < 0.08) T = 0.5;
    }
    return is_valid(g);
}

static void grow_loop(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore && best->n + 2 <= MAXN) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_start(best, &work) && anneal(&work, now() + slice))
            copy_graph(best, &work);
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
    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    moore = compute_moore();

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (best.n < moore) {
        lift_phase(&best, t0 + (t_end - t0) * 0.35);
        grow_loop(&best, t_end);
    }
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

    # Compile time counts against time_limit too, so C gets 85% minus a margin.
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 3)
        consider(lib.parse_graph_text(text))
    except (RuntimeError, ValueError):
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
