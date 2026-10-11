import itertools
import time

import lib

C_SOURCE = r'''
/* Combined bipartite degree-diameter search.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1 (lift search, first LIFT_FRAC of the time): base with k vertices per side
 *   and d darts per base vertex (one dart per layer, layers are permutations, so the
 *   lift is d-regular). Dart (i, j, s) joins A_{i,g} to B_{j,g*s} in the group
 *   Z_m x| Z_k2. Left multiplication is an automorphism, so diameter <= D iff a BFS of
 *   depth D from each of the 2k class representatives reaches everything. Voltages and
 *   layer swaps are annealed on the number of unreached pairs. The target order adapts.
 * Phase 2 (grow by two, remaining time): add one vertex per side, rewire by stealing
 *   edges, then anneal degree-preserving swaps on the number of bad pairs.
 * Every returned graph is checked with is_valid (bipartite, simple, degree, diameter).
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXK 4
#define MAXT (MAXD * MAXK)
#define MAXG 1024
#define BIGC 1000000000L
#define LIFT_FRAC 0.5

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double LIFT_END = 0.0;

/* ------------------------------------------------------------ utilities */

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd64(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return k <= 0 ? 0 : (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod_i(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* Upper bound on the order of a bipartite graph with max degree d and diameter D. */
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

/* ------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D. Zero means diameter <= D. */
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

/* ------------------------------------------------------------ input / output */

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

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k2: element a*k2+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k2). */
static int GM[MAXG * MAXG];
static int GO = 0;

static void build_group(int m, int k2, int r) {
    int G = m * k2;
    int pw[16];
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e2 = y % k2;
            int aa = (int)(((long long)a + (long long)pw[b] * c) % m);
            GM[x * G + y] = aa * k2 + (b + e2) % k2;
        }
    }
    GO = G;
}

static int choose_group(int G) {
    int cand[12], nc = 0;
    for (int k2 = 1; k2 <= 12; k2++)
        if (G % k2 == 0 && G / k2 >= 2) cand[nc++] = k2;
    if (nc == 0) return 0;
    int k2 = cand[rndint(nc)];
    int m = G / k2;
    int r = 1;
    if (k2 > 1) {
        for (int t = 0; t < 200; t++) {
            int c = 1 + rndint(m - 1);
            if (gcd_i(c, m) == 1 && powmod_i(c, k2, m) == 1 % m) { r = c; break; }
        }
    }
    build_group(m, k2, r);
    return 1;
}

/* ------------------------------------------------------------ voltage lifts */

static int DI[MAXT], DJ[MAXT], DS[MAXT];
static int ADJL[MAXN * MAXD];
static int CNTL[MAXN];
static int VIS[MAXN];
static int QU[MAXN];
static int STAMP = 0;

static void random_darts(int k, int dd) {
    int perm[MAXK];
    for (int l = 0; l < dd; l++) {
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        for (int i = 0; i < k; i++) {
            int t = l * k + i;
            DI[t] = i;
            DJ[t] = perm[i];
            DS[t] = rndint(GO);
        }
    }
}

/* Unreached (representative, vertex) pairs over the 2k class representatives. */
static long eval_cost(int k, int dd) {
    int G = GO, N = 2 * k * G, T = k * dd;
    if (N > MAXN) return BIGC;
    for (int a = 0; a < T; a++)
        for (int b = a + 1; b < T; b++)
            if (DI[a] == DI[b] && DJ[a] == DJ[b] && DS[a] == DS[b]) return BIGC;
    for (int v = 0; v < N; v++) CNTL[v] = 0;
    for (int t = 0; t < T; t++) {
        int i = DI[t], j = DJ[t], s = DS[t];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (k + j) * G + GM[g * G + s];
            if (CNTL[a] >= dd || CNTL[b] >= dd) return BIGC;
            ADJL[a * MAXD + CNTL[a]++] = b;
            ADJL[b * MAXD + CNTL[b]++] = a;
        }
    }
    for (int v = 0; v < N; v++) if (CNTL[v] != dd) return BIGC;

    long total = 0;
    for (int rep = 0; rep < 2 * k; rep++) {
        int src = rep * G;
        STAMP++;
        if (STAMP == 0x7fffffff) { memset(VIS, 0, sizeof(VIS)); STAMP = 1; }
        int head = 0, tail = 0;
        QU[tail++] = src;
        VIS[src] = STAMP;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            for (; head < end; head++) {
                int u = QU[head];
                for (int c = 0; c < dd; c++) {
                    int v = ADJL[u * MAXD + c];
                    if (VIS[v] != STAMP) { VIS[v] = STAMP; QU[tail++] = v; }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static long anneal(int k, int dd, long iters) {
    int G = GO, T = k * dd;
    long cur = eval_cost(k, dd);
    double temp0 = 0.5 * G + 1.0;
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 1023) == 0 && now() > LIFT_END) break;
        double frac = (double)it / (double)iters;
        double temp = temp0 * (1.0 - frac) + 0.3;
        if (rndint(2) == 0) {
            int t = rndint(T);
            int old = DS[t];
            int ns = rndint(G);
            if (ns == old) continue;
            DS[t] = ns;
            long c2 = eval_cost(k, dd);
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / temp)) cur = c2;
            else DS[t] = old;
        } else {
            if (k < 2) continue;
            int l = rndint(dd);
            int i1 = rndint(k), i2 = rndint(k);
            if (i1 == i2) continue;
            int t1 = l * k + i1, t2 = l * k + i2;
            int tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp;
            long c2 = eval_cost(k, dd);
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / temp)) cur = c2;
            else { tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp; }
        }
    }
    return cur;
}

/* Build the full lift of the current darts into g (valid only when cost is zero). */
static void build_lift(Graph *g, int k, int dd) {
    int G = GO, N = 2 * k * G, T = k * dd;
    g->n = N;
    for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = v >= k * G; }
    for (int t = 0; t < T; t++)
        for (int x = 0; x < G; x++)
            add_edge(g, DI[t] * G + x, (k + DJ[t]) * G + GM[x * G + DS[t]]);
}

static void lift_phase(Graph *best, double until) {
    static const int KCH[6] = {1, 1, 2, 2, 3, 4};
    static Graph cand;
    long moore = moore_bound();
    int step = 16, fails = 0;
    LIFT_END = until;
    while (now() < until) {
        if (best->n + 2 > moore) break;
        int k = KCH[rndint(6)];
        int nmin = best->n + step;
        int gmin = (nmin + 2 * k - 1) / (2 * k);
        if (gmin < 2) gmin = 2;
        int G = gmin + rndint(1 + gmin / 12);
        long gcap = MAXN / (2 * k);
        if (gcap > MAXG) gcap = MAXG;
        long gm2 = moore / (2 * k);
        if (gcap > gm2) gcap = gm2;
        if (G > gcap) G = (int)gcap;
        if (G < 2) { fails++; continue; }
        if (!choose_group(G)) { fails++; continue; }
        random_darts(k, d);
        long c = anneal(k, d, 20000);
        if (c == 0) {
            build_lift(&cand, k, d);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
            fails = 0;
            step *= 2;
            int cap = 16 + best->n / 8;
            if (step > cap) step = cap;
        } else if (++fails >= 4) {
            fails = 0;
            step /= 2;
            if (step < 2) step = 2;
        }
    }
}

/* ------------------------------------------------------------ grow by two */

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
    while (now() < until && best->n + 2 <= moore_bound() && best->n + 2 <= MAXN) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
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
    for (int i = 0; i < 10; i++) rnd64();

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (d == 1 || D < 2) { printf("2 1\n0 1\n"); return 0; }

    static Graph best, start;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    copy_graph(&start, &best);

    if (best.n < moore_bound()) {
        lift_phase(&best, t0 + (t_end - t0) * LIFT_FRAC);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) copy_graph(&best, &start);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, degree q+1."""
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


def known_start(d, D):
    """Best known construction Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    if D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q) and q + 1 <= d:
                return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    try:
        start = known_start(d, D)
    except Exception:
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
