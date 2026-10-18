"""Lift-annealing program: quotient-based search over voltage lifts of small base graphs.

Compared with the parent, the core search is different:
  * Candidates are regular lifts of a random d-regular bipartite base with p vertices per
    side, over a metacyclic group Z_m x|_r Z_k of order N (total order 2pN).
  * A lift is evaluated on the quotient: left multiplication by the group is an automorphism
    that acts transitively on each fibre, so only 2p BFS runs (one per base vertex) are needed.
    Each evaluation costs O(p * d * 2pN) instead of a full bitset closure.
  * Simulated annealing moves voltages and, occasionally, swaps base endpoints, with a
    time-based temperature schedule. Restarts draw new base graphs and groups.
  * Growth is by two: the target is always best.n + 2, and any success is accepted.
  * The parent's bitset repair and tabu search are removed, and so is the Cayley-only phase.
    The p = 1 case is still covered, since it is a bipartite Cayley graph with distinct voltages.

Safety: C output is re-validated with lib.is_valid, any C failure keeps the valid fallback,
and the fallback is the best Python construction (or K_{d,d}).
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
#define MAXP 4
#define MAXV 1100
#define MAXG 1100
#define MAXDART (MAXD * MAXP)

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

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

/* ------------------------------------------------------------------ full validity check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

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
        badv[v] = n - c;
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

static Graph best;

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element a*k+b is (a,b); (a,b)(c,e) = (a + r^b c mod m, b+e mod k). */
static int gmt[MAXG * MAXG];   /* gmt[x*N+y] = x*y */
static int ginv[MAXG];
static int rp_tab[MAXG];
static int gN = 0;

static int build_group(int m, int k, int r) {
    int N = m * k;
    if (N < 1 || N > MAXG || k < 1) return 0;
    for (int b = 0; b < k; b++) rp_tab[b] = (int)powmod(r, b, m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            gmt[x * N + y] = (int)((a + (long)rp_tab[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++) {
        ginv[x] = -1;
        for (int y = 0; y < N; y++)
            if (gmt[x * N + y] == 0) { ginv[x] = y; break; }
        if (ginv[x] < 0) return 0;
    }
    gN = N;
    return 1;
}

/* Uniform random (m, k, r) with m*k = N, gcd(r,m)=1, r^k = 1 mod m. */
static int random_group(int N) {
    long count = 0;
    int bm = 1, bk = N, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            count++;
            if (rnd() % (uint64_t)count == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rnd() % (uint64_t)count == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (!count) return 0;
    return build_group(bm, bk, br);
}

/* ------------------------------------------------------------------ base graph and voltages */

static int nd;                      /* number of darts = p * d */
static int p_cur, N_cur;
static int dm_i[MAXDART], dm_j[MAXDART], dm_g[MAXDART];
static int idx_i[MAXP][MAXD], idx_j[MAXP][MAXD];

static int base_connected(int p) {
    int reach[2 * MAXP];
    for (int v = 0; v < 2 * p; v++) reach[v] = 0;
    reach[0] = 1;
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int t = 0; t < nd; t++) {
            int a = dm_i[t], b = p + dm_j[t];
            if (reach[a] != reach[b]) { reach[a] = 1; reach[b] = 1; changed = 1; }
        }
    }
    for (int v = 0; v < 2 * p; v++) if (!reach[v]) return 0;
    return 1;
}

/* d-regular bipartite base: sum of d random permutations on p + p vertices. */
static int gen_base(int p) {
    for (int tries = 0; tries < 1000; tries++) {
        nd = 0;
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1), s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
            for (int i = 0; i < p; i++) {
                dm_i[nd] = i;
                dm_j[nd] = perm[i];
                dm_g[nd] = -1;
                nd++;
            }
        }
        if (base_connected(p)) return 1;
    }
    return 0;
}

static void build_index(void) {
    int ci[MAXP], cj[MAXP];
    for (int v = 0; v < MAXP; v++) { ci[v] = 0; cj[v] = 0; }
    for (int t = 0; t < nd; t++) {
        int i = dm_i[t], j = dm_j[t];
        idx_i[i][ci[i]++] = t;
        idx_j[j][cj[j]++] = t;
    }
}

/* True if dart t shares its base pair and voltage with another dart. */
static int conflict(int t) {
    for (int s = 0; s < nd; s++)
        if (s != t && dm_i[s] == dm_i[t] && dm_j[s] == dm_j[t] && dm_g[s] == dm_g[t])
            return 1;
    return 0;
}

/* A voltage for dart t that no other dart on the same base pair uses. -1 on failure. */
static int fresh_g(int t) {
    for (int tries = 0; tries < 2000; tries++) {
        int g = rndint(N_cur), clash = 0;
        for (int s = 0; s < nd; s++)
            if (s != t && dm_i[s] == dm_i[t] && dm_j[s] == dm_j[t] && dm_g[s] == g) {
                clash = 1;
                break;
            }
        if (!clash) return g;
    }
    return -1;
}

/* ------------------------------------------------------------------ quotient evaluation */

static int dist_[MAXV], bq[MAXV];

/* Neighbour k of vertex v in the lift. A_{i,x} ~ B_{j, x*g} for each dart (i,j,g).
 * Vertex index: A_{i,x} = i*N + x; B_{j,y} = P + j*N + y, with P = p*N. */
static int nbr(int v, int k) {
    int N = N_cur, P = p_cur * N_cur;
    if (v < P) {
        int i = v / N, x = v - i * N;
        int t = idx_i[i][k];
        return P + dm_j[t] * N + gmt[x * N + dm_g[t]];
    } else {
        int w = v - P;
        int j = w / N, y = w - j * N;
        int t = idx_j[j][k];
        return dm_i[t] * N + gmt[y * N + ginv[dm_g[t]]];
    }
}

/* Left multiplication is an automorphism transitive on each fibre, so it is enough to run
 * BFS from A_{i,e} and B_{j,e}. Cost = sum over sources of vertices at distance > D. */
static long eval_cost(void) {
    int N = N_cur, P = p_cur * N_cur, T = 2 * P;
    long cost = 0;
    for (int s = 0; s < 2 * p_cur; s++) {
        int src = s < p_cur ? s * N : P + (s - p_cur) * N;
        for (int v = 0; v < T; v++) dist_[v] = -1;
        int head = 0, tail = 0, reached = 1;
        dist_[src] = 0;
        bq[tail++] = src;
        while (head < tail) {
            int v = bq[head++];
            if (dist_[v] >= D) continue;
            for (int k = 0; k < d; k++) {
                int u = nbr(v, k);
                if (dist_[u] < 0) {
                    dist_[u] = dist_[v] + 1;
                    bq[tail++] = u;
                    reached++;
                }
            }
        }
        cost += T - reached;
    }
    return cost;
}

/* Materialise the current lift into g and return whether it is fully valid. */
static int to_graph(Graph *g) {
    int N = N_cur, P = p_cur * N_cur;
    g->n = 2 * P;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= P; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dm_i[t] * N + x, P + dm_j[t] * N + gmt[x * N + dm_g[t]]);
    return is_valid(g);
}

/* One annealing attempt on a random base and voltages for the current group.
 * Returns 1 and fills out with a valid lift of order 2pN on success. */
static int lift_attempt(int p, int N, double until, Graph *out) {
    p_cur = p;
    N_cur = N;
    if (!gen_base(p)) return 0;
    for (int t = 0; t < nd; t++) {
        int g = fresh_g(t);
        if (g < 0) return 0;
        dm_g[t] = g;
    }
    build_index();
    long cur = eval_cost();
    double t_start = now();
    double span = until - t_start;
    if (span <= 0) return 0;
    long it = 0;
    while (cur > 0) {
        if ((++it & 31) == 0 && now() > until) break;
        double frac = (now() - t_start) / span;
        if (frac > 1.0) frac = 1.0;
        double temp = 2.0 * pow(0.05, frac) + 1e-9;
        if (nd >= 2 && rnd01() < 0.1) {
            /* base move: swap the B endpoints of two darts (keeps regularity) */
            int t1 = rndint(nd), t2 = rndint(nd);
            if (dm_i[t1] == dm_i[t2] || dm_j[t1] == dm_j[t2]) continue;
            int j1 = dm_j[t1], j2 = dm_j[t2];
            dm_j[t1] = j2;
            dm_j[t2] = j1;
            build_index();
            if (conflict(t1) || conflict(t2)) {
                dm_j[t1] = j1;
                dm_j[t2] = j2;
                build_index();
                continue;
            }
            long nw = eval_cost();
            if (nw <= cur || rnd01() < exp(-(double)(nw - cur) / temp)) {
                cur = nw;
            } else {
                dm_j[t1] = j1;
                dm_j[t2] = j2;
                build_index();
            }
        } else {
            /* voltage move */
            int t = rndint(nd);
            int old = dm_g[t];
            int g = fresh_g(t);
            if (g < 0 || g == old) continue;
            dm_g[t] = g;
            long nw = eval_cost();
            if (nw <= cur || rnd01() < exp(-(double)(nw - cur) / temp)) {
                cur = nw;
            } else {
                dm_g[t] = old;
            }
        }
    }
    if (cur != 0) return 0;
    return to_graph(out);
}

/* Repeated attempts over base sizes p = 1..4 and groups of order near the target.
 * Target is always best.n + 2. */
static void search(double until) {
    static Graph cand;
    long moore = moore_bound();
    int skips = 0;
    while (now() < until) {
        long T = (long)best.n + 2;
        if (T > moore || T > MAXV) break;
        int p = 1 + rndint(MAXP);
        long N = (T + 2 * p - 1) / (2 * p);
        if (N < d) N = d;
        if (rndint(3) == 0) N++;
        if (2L * p * N > MAXV || 2L * p * N > moore || N > MAXG / 2) {
            if (++skips > 100000) break;
            continue;
        }
        if (!random_group((int)N)) continue;
        double slice = 0.6 + 0.6 * (double)T / 500.0;
        double ue = now() + slice;
        if (ue > until) ue = until;
        if (lift_attempt(p, (int)N, ue, &cand) && cand.n > best.n && is_valid(&cand))
            copy_graph(&best, &cand);
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

    if (d < 1 || D < 1 || d > MAXD) {
        printf("1 0\n");
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (D >= 2 && best.n < moore_bound()) search(t_end);
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
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: always valid
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget], stdin_graph=start,
                             timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except (RuntimeError, ValueError):
            pass   # keep the valid fallback
    return best
