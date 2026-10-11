"""Degree-diameter search: annealed voltage lifts over semidirect groups, then a grow-by-two polish.

build() always returns a valid graph: the best of the known construction, the C result, and a fallback.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1 (lift annealing): pick a random d-regular base multigraph with p <= 6 vertices per
 *   side and a random semidirect product group Z_m x| Z_k of order N. Give each dart a voltage
 *   and anneal the voltages. Left multiplication is an automorphism of the lift, so the cost
 *   (number of vertices unreached within D steps) is computed from only 2p BFS roots.
 * Phase 2 (grow by two): insert one vertex per side and anneal degree-preserving swaps.
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
#define MAXP 6

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN]; /* 0 = part A, 1 = part B */
} Graph;

static int d, D;
static double t_end;
static long moore;

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
static int badv[MAXN];

/* Number of unordered pairs at distance > D (0 means diameter <= D). Bitset reachability. */
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

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a, b) is the int a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct {
    int m, k, r;
    int rp[MAXN]; /* rp[b] = r^b mod m */
} Grp;

static Grp GG; /* the group used by the current lift */

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Uniform random (m, k, r) with m*k = N, gcd(r, m) = 1 and r^k = 1 mod m. */
static int random_group(int N, Grp *G) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)(count < 2000000000L ? count : 2000000000L)) == 0) {
                G->m = m; G->k = k; G->r = r;
            }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* ------------------------------------------------------------------ lift annealing */

/* Random d-regular bipartite base multigraph with p vertices per side (sum of d random
 * permutation matrices), retried until connected. */
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

typedef struct {
    int i, j, g;   /* dart from base A-vertex i to base B-vertex j with voltage g */
    int si, sj;    /* slot of this dart among the darts leaving i / entering j */
} Dart;

static int P_, N_;                 /* current base size and group order */
static int nd_;                    /* number of darts = p*d */
static Dart dts[MAXP * MAXD];
static int nbr[MAXN][MAXD];        /* lifted adjacency, every vertex has exactly d entries */

/* Rewrite the lifted edges of dart t from its current voltage.
 * A vertex i*N+x joins B vertex p*N + j*N + x*g. */
static void update_dart(int t) {
    int p = P_, N = N_;
    int i = dts[t].i, j = dts[t].j, g = dts[t].g;
    int ra = i * N, rb = p * N + j * N;
    for (int x = 0; x < N; x++) {
        int y = gmul(&GG, x, g);
        nbr[ra + x][dts[t].si] = rb + y;
        nbr[rb + y][dts[t].sj] = ra + x;
    }
}

static int vis_[MAXN], vstamp_ = 0, q_[MAXN];

/* Sum over base roots of the number of vertices not reached within D steps.
 * Left multiplication by the group is an automorphism, so the 2p roots (i*N and p*N+j*N) suffice.
 * Zero means every pair is within D (the lift is connected too). */
static long root_cost(void) {
    int n = 2 * P_ * N_;
    long cost = 0;
    for (int r = 0; r < 2 * P_; r++) {
        int root = r < P_ ? r * N_ : P_ * N_ + (r - P_) * N_;
        vstamp_++;
        int head = 0, tail = 0;
        q_[tail++] = root;
        vis_[root] = vstamp_;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int v = q_[head++];
                for (int k = 0; k < d; k++) {
                    int u = nbr[v][k];
                    if (vis_[u] != vstamp_) { vis_[u] = vstamp_; q_[tail++] = u; }
                }
            }
        }
        cost += n - tail;
    }
    return cost;
}

static void lift_to_graph(Graph *out) {
    int n = 2 * P_ * N_;
    out->n = n;
    for (int v = 0; v < n; v++) {
        out->deg[v] = d;
        for (int k = 0; k < d; k++) out->adj[v][k] = nbr[v][k];
        out->side[v] = v >= P_ * N_;
    }
}

/* Random base and voltages in group GG (already set), then simulated annealing on voltages.
 * On success writes the valid lift into out and returns 1. */
static int anneal_lift(int p, int N, int steps, double until, Graph *out) {
    int M[MAXP][MAXP];
    P_ = p;
    N_ = N;
    make_base(p, M);
    nd_ = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                Dart *t = &dts[nd_];
                t->i = i;
                t->j = j;
                t->g = 0;
                t->si = 0;
                t->sj = 0;
                for (int s = 0; s < nd_; s++) {
                    if (dts[s].i == i) t->si++;
                    if (dts[s].j == j) t->sj++;
                }
                for (;;) {
                    int g = rndint(N), clash = 0;
                    for (int s = 0; s < nd_; s++)
                        if (dts[s].i == i && dts[s].j == j && dts[s].g == g) { clash = 1; break; }
                    if (!clash) { t->g = g; break; }
                }
                nd_++;
            }
    for (int t = 0; t < nd_; t++) update_dart(t);
    long cost = root_cost();
    double T0 = 2.0, T1 = 0.15;
    for (int s = 0; s < steps && cost > 0; s++) {
        if ((s & 255) == 0 && now() > until) return 0;
        double T = T0 * pow(T1 / T0, (double)s / steps);
        int t = rndint(nd_);
        int i = dts[t].i, j = dts[t].j, old = dts[t].g;
        int ng = rndint(N);
        if (ng == old) continue;
        int clash = 0;
        for (int s2 = 0; s2 < nd_; s2++)
            if (s2 != t && dts[s2].i == i && dts[s2].j == j && dts[s2].g == ng) { clash = 1; break; }
        if (clash) continue;
        dts[t].g = ng;
        update_dart(t);
        long nc = root_cost();
        if (nc <= cost || rnd01() < exp((double)(cost - nc) / T)) {
            cost = nc;
        } else {
            dts[t].g = old;
            update_dart(t);
        }
    }
    if (cost != 0) return 0;
    lift_to_graph(out);
    return is_valid(out);
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    int fails = 0;
    while (now() < until) {
        int r = rndint(12);
        int p = r < 2 ? 1 : r < 4 ? 2 : r < 6 ? 3 : r < 8 ? 4 : r < 10 ? 5 : 6;
        long target = best->n + 2;
        int N = (int)((target + 2 * p - 1) / (2 * p)) + rndint(3);
        if (N < d) N = d + rndint(2);
        if (2L * p * N > moore || 2 * p * N > MAXN) {
            if (++fails > 1000) return;
            continue;
        }
        if (!random_group(N, &GG)) continue;
        if (anneal_lift(p, N, 30000, until, &cand) && cand.n > best->n)
            copy_graph(best, &cand);
    }
}

/* ------------------------------------------------------------------ grow by two */

static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore || n + 2 > MAXN) return 0;
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
    while (now() < until && best->n + 2 <= moore) {
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
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (D == 1) { printf("2 1\n0 1\n"); return 0; }
    moore = moore_bound();

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (best.n < moore) {
        lift_search(&best, t0 + (t_end - t0) * 0.75);
        if (best.n < moore) grow_search(&best, t_end);
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


def _fallback(d, D):
    """Always-valid simple graph for (d, D): K_{d,d} when D >= 2, a single edge when D = 1."""
    if D >= 2 and d >= 1:
        cand = lib.haar_graph(d, range(d))
    elif d >= 1 and D >= 1:
        cand = (2, [(0, 1)])
    else:
        cand = (1, [])
    if lib.is_valid(*cand, d, D):
        return cand
    return (1, [])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    if start is not None and not lib.is_valid(*start, d, D):
        start = None
    best = start if start is not None else _fallback(d, D)
    if best[0] >= lib.moore_bound(d, D):
        return best   # already a Moore graph: nothing can beat it
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=start, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(*out, d, D):
                best = out
        except (RuntimeError, ValueError):
            pass   # keep the valid fallback
    return best
