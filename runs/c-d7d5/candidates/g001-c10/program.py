"""Combined program: Python builds the best known start graph; C searches from it.

C search, in order:
  1. Bi-Cayley lifts over semidirect products Z_m x| Z_k, k base vertices per side.
     Simulated annealing on the voltages and layer permutations. The cost counts
     unreached (representative, vertex) pairs, using the 2k orbit representatives,
     plus a duplicate-dart penalty.
  2. Grow by two from the best graph: add one vertex per side, then anneal
     degree-preserving edge swaps until the diameter is <= D.
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
#define MAXK 4
#define MAXT (MAXD * MAXK)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

/* ---------------------------------------------------------------- utilities */

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

/* ---------------------------------------------------------------- graph basics */

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

/* ---------------------------------------------------------------- distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

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

/* ---------------------------------------------------------------- input / output */

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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ---------------------------------------------------------------- groups */

/* Z_m x|_r Z_k: element (a, b) is the int a*k + b. */
typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

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

/* ---------------------------------------------------------------- bi-Cayley lifts */

/* Base: k vertices per side, d layers. Layer L is a permutation j = p_L(i), so dart
 * t = L*k + i joins A_{i,g} to B_{dj[t], g*ds[t]} for all g. Every vertex has degree d. */
static int bc_k, bc_N, bc_nd;
static int bc_dj[MAXT], bc_ds[MAXT];
static int bc_adj[MAXN][MAXD];
static int bc_deg[MAXN];
static int bc_vis[MAXN];
static int bc_stamp = 0;
static int bc_q[MAXN];

static void bc_build(const Grp *G) {
    int k = bc_k, N = bc_N, V = 2 * k * N;
    for (int v = 0; v < V; v++) bc_deg[v] = 0;
    for (int t = 0; t < bc_nd; t++) {
        int i = t % k, j = bc_dj[t], s = bc_ds[t];
        for (int g = 0; g < N; g++) {
            int a = i * N + g, b = (k + j) * N + gmul(G, g, s);
            bc_adj[a][bc_deg[a]++] = b;
            bc_adj[b][bc_deg[b]++] = a;
        }
    }
}

/* Unreached (orbit representative, vertex) pairs + 1000 * duplicate darts. Zero = valid. */
static long bc_cost(const Grp *G) {
    int k = bc_k, N = bc_N, V = 2 * k * N;
    bc_build(G);
    long dup = 0;
    for (int t = 0; t < bc_nd; t++)
        for (int u = 0; u < t; u++)
            if (t % k == u % k && bc_dj[t] == bc_dj[u] && bc_ds[t] == bc_ds[u]) dup++;
    long total = 0;
    for (int r = 0; r < 2 * k; r++) {
        int src = r * N;
        bc_stamp++;
        int head = 0, tail = 0;
        bc_vis[src] = bc_stamp;
        bc_q[tail++] = src;
        for (int lvl = 0; lvl < D && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int v = bc_q[head++];
                for (int e = 0; e < bc_deg[v]; e++) {
                    int u = bc_adj[v][e];
                    if (bc_vis[u] != bc_stamp) { bc_vis[u] = bc_stamp; bc_q[tail++] = u; }
                }
            }
        }
        total += V - tail;
    }
    return total + 1000L * dup;
}

static void bc_random_init(void) {
    int k = bc_k;
    for (int L = 0; L < d; L++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1), s = perm[i];
            perm[i] = perm[j];
            perm[j] = s;
        }
        for (int i = 0; i < k; i++) bc_dj[L * k + i] = perm[i];
    }
    for (int t = 0; t < bc_nd; t++) bc_ds[t] = rndint(bc_N);
}

static void emit_lift(Graph *best, const Grp *G) {
    static Graph cand;
    int k = bc_k, N = bc_N, V = 2 * k * N;
    cand.n = V;
    for (int v = 0; v < V; v++) {
        cand.deg[v] = 0;
        cand.side[v] = v >= k * N;
    }
    for (int t = 0; t < bc_nd; t++) {
        int i = t % k, j = bc_dj[t], s = bc_ds[t];
        for (int g = 0; g < N; g++)
            add_edge(&cand, i * N + g, (k + j) * N + gmul(G, g, s));
    }
    if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
}

/* Simulated annealing over the voltages and layer targets. Returns 1 if cost reached 0. */
static int bc_anneal(const Grp *G, long iters, double until) {
    bc_random_init();
    long cost = bc_cost(G);
    for (long it = 0; it < iters && cost > 0; it++) {
        if ((it & 127) == 0 && now() > until) break;
        double temp = 2.0 * (1.0 - (double)it / (double)iters) + 0.05;
        int mv = rndint(5);
        if (mv < 4 || bc_k == 1) {
            int t = rndint(bc_nd);
            int old = bc_ds[t];
            int nw = rndint(bc_N);
            if (nw == old) continue;
            bc_ds[t] = nw;
            long c2 = bc_cost(G);
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / temp)) cost = c2;
            else bc_ds[t] = old;
        } else {
            int L = rndint(d), i1 = rndint(bc_k), i2 = rndint(bc_k);
            if (i1 == i2) continue;
            int a = L * bc_k + i1, b = L * bc_k + i2;
            int tmp = bc_dj[a];
            bc_dj[a] = bc_dj[b];
            bc_dj[b] = tmp;
            long c2 = bc_cost(G);
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / temp)) cost = c2;
            else {
                tmp = bc_dj[a];
                bc_dj[a] = bc_dj[b];
                bc_dj[b] = tmp;
            }
        }
    }
    return cost == 0;
}

static void bicayley_search(Graph *best, double until) {
    static Grp G;
    long moore = moore_bound();
    static const int ks[] = {1, 2, 2, 3, 4};
    int fails = 0;
    while (now() < until) {
        int k = ks[rndint(5)];
        long target = best->n + 2;
        long N = (target + 2 * k - 1) / (2 * k) + rndint(3);
        long V = 2 * k * N;
        if (V > moore || V > MAXN || N < 1) {
            if (++fails > 2000) return;
            continue;
        }
        if (!random_group((int)N, &G)) continue;
        bc_k = k;
        bc_N = (int)N;
        bc_nd = d * k;
        double slice = now() + 3.0;
        if (slice > until) slice = until;
        if (bc_anneal(&G, 30000, slice)) emit_lift(best, &G);
    }
}

/* ---------------------------------------------------------------- grow by two */

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

/* ---------------------------------------------------------------- main */

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

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && best.n < moore_bound()) {
        bicayley_search(&best, t0 + (t_end - t0) * 0.55);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best exact construction Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    import itertools
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q <= min(d - 1, 9), or None."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])

    best = lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand

    if D >= 3:
        try:
            consider(known_start(d, D))
        except Exception:
            pass
        if D == 3 and lib.is_prime_power(d - 1):
            return best   # Moore graph: nothing to search for

    if D == 4 and d - 1 <= 9:
        try:
            gq = _best_gq(d)
            consider(gq)
            if lib.is_prime_power(d - 1):
                return best   # generalized quadrangle: optimal
        except Exception:
            pass

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.5:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5)
        consider(lib.parse_graph_text(text))
    except Exception:
        pass   # keep the best valid construction already found

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
