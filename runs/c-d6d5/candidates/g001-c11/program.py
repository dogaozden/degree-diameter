import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phases (alternated in main):
 *   1. Voltage lifts over semidirect groups Z_m x| Z_k with a base of p A- and p B-vertices
 *      and d layers of permutation darts. Simulated annealing on voltages and layer
 *      permutations. Cost = unreached (orbit representative, vertex) pairs at depth D.
 *      Left multiplication is an automorphism, so only 2p BFS roots are needed.
 *   2. Grow by two: insert one vertex per side from the spare degree of d-1 removed edges,
 *      then anneal degree-preserving swaps until diameter <= D.
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
#define MAXDART (MAXP * MAXD)

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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a, b) is a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static Grp GG;

static int gmul(int x, int y) {
    int a = x / GG.k, b = x % GG.k, c = y / GG.k, e = y % GG.k;
    return (int)(((long)a + (long)GG.rp[b] * c) % GG.m) * GG.k + (b + e) % GG.k;
}

/* Uniform random (m, k, r) with m*k = N, gcd(r, m) = 1, r^k = 1 mod m. */
static int random_group(int N) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { GG.m = m; GG.k = k; GG.r = r; }
        }
    }
    if (!count) return 0;
    GG.rp[0] = 1 % GG.m;
    for (int b = 1; b < GG.k; b++) GG.rp[b] = (int)((long)GG.rp[b - 1] * GG.r % GG.m);
    return 1;
}

/* ------------------------------------------------------------------ voltage lifts */

/* Dart t: A-vertex dI[t] -> B-vertex dJ[t] with voltage dS[t].
 * Layer L holds darts L*p .. L*p+p-1; dJ within a layer is a permutation of 0..p-1,
 * so every base vertex has degree exactly d. */
static int P_, NN_, nd;
static int dI[MAXDART], dJ[MAXDART], dS[MAXDART];
static int LA[MAXN][MAXD];
static int vis[MAXN], vstamp = 0, bq[MAXN];

static int dup_free(void) {
    for (int a = 0; a < nd; a++)
        for (int b = a + 1; b < nd; b++)
            if (dI[a] == dI[b] && dJ[a] == dJ[b] && dS[a] == dS[b]) return 0;
    return 1;
}

static void random_state(int p) {
    nd = p * d;
    do {
        for (int L = 0; L < d; L++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1), s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
            for (int i = 0; i < p; i++) {
                dI[L * p + i] = i;
                dJ[L * p + i] = perm[i];
                dS[L * p + i] = rndint(NN_);
            }
        }
    } while (!dup_free());
}

/* Sum over the 2p orbit representatives of vertices not reached within D steps.
 * Zero means the lift has diameter <= D. */
static long lift_cost(void) {
    int p = P_, N = NN_, V = 2 * p * N;
    static int cnt[MAXN];
    memset(cnt, 0, sizeof(int) * (size_t)V);
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++) {
            int a = dI[t] * N + x;
            int b = p * N + dJ[t] * N + gmul(x, dS[t]);
            LA[a][cnt[a]++] = b;
            LA[b][cnt[b]++] = a;
        }
    long cost = 0;
    for (int rep = 0; rep < 2 * p; rep++) {
        int src = rep < p ? rep * N : p * N + (rep - p) * N;
        vstamp++;
        int head = 0, tail = 0;
        vis[src] = vstamp;
        bq[tail++] = src;
        for (int lvl = 0; lvl < D && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int u = bq[head++];
                for (int i = 0; i < d; i++) {
                    int w = LA[u][i];
                    if (vis[w] != vstamp) {
                        vis[w] = vstamp;
                        bq[tail++] = w;
                    }
                }
            }
        }
        cost += V - tail;
    }
    return cost;
}

/* Annealing over voltages and layer permutations. On success the state is left in dI/dJ/dS. */
static int lift_sa(int p, int N, int iters, double until) {
    static int bJ[MAXDART], bS[MAXDART], sJ[MAXDART], sS[MAXDART];
    P_ = p;
    NN_ = N;
    random_state(p);
    long cur = lift_cost();
    long best = cur;
    memcpy(bJ, dJ, sizeof(int) * nd);
    memcpy(bS, dS, sizeof(int) * nd);
    for (int it = 0; it < iters && best > 0; it++) {
        if (now() > until) break;
        double T = 2.0 * (1.0 - (double)it / iters) + 0.05;
        memcpy(sJ, dJ, sizeof(int) * nd);
        memcpy(sS, dS, sizeof(int) * nd);
        if (p >= 2 && rnd01() < 0.2) {
            int L = rndint(d), i = rndint(p), i2 = rndint(p);
            if (i == i2) continue;
            int x = L * p + i, y = L * p + i2, tmp = dJ[x];
            dJ[x] = dJ[y];
            dJ[y] = tmp;
        } else {
            dS[rndint(nd)] = rndint(N);
        }
        if (!dup_free()) {
            memcpy(dJ, sJ, sizeof(int) * nd);
            memcpy(dS, sS, sizeof(int) * nd);
            continue;
        }
        long nc = lift_cost();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
            if (cur < best) {
                best = cur;
                memcpy(bJ, dJ, sizeof(int) * nd);
                memcpy(bS, dS, sizeof(int) * nd);
            }
        } else {
            memcpy(dJ, sJ, sizeof(int) * nd);
            memcpy(dS, sS, sizeof(int) * nd);
        }
    }
    if (best > 0) return 0;
    memcpy(dJ, bJ, sizeof(int) * nd);
    memcpy(dS, bS, sizeof(int) * nd);
    return 1;
}

static void build_lift_graph(Graph *g, int p, int N) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= p * N;
    }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dI[t] * N + x, p * N + dJ[t] * N + gmul(x, dS[t]));
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        int r = rndint(10);
        int p = r < 3 ? 1 : r < 6 ? 2 : r < 8 ? 3 : 4;
        long target = best->n + 2;
        if (target > moore) return;
        int N = (int)((target + 2 * p - 1) / (2 * p)) + rndint(3);
        if (best->n == 0) N = d + rndint(3);
        if (N < d) N = d;
        if (2L * p * N > moore || 2 * p * N > MAXN) {
            if (++fails > 1000) return;
            continue;
        }
        random_group(N);
        if (lift_sa(p, N, 3000, until)) {
            build_lift_graph(&cand, p, N);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
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
    int had_start = best.n > 0;

    if (D >= 2 && best.n < moore_bound()) {
        double span = t_end - t0;
        lift_search(&best, t0 + span * (had_start ? 0.35 : 0.5));
        if (best.n > 0) grow_search(&best, t0 + span * 0.7);
        lift_search(&best, t0 + span * 0.85);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (degree q + 1 <= d)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in __import__("itertools").product(range(q), repeat=4)
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
    """W(q) for the largest prime power q <= min(d - 1, 9)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _starts(d, D):
    """Valid known constructions for (d, D), each checked with lib.is_valid."""
    makers = []
    if D >= 3:
        makers.append(lambda: _best_pg(d))
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            makers.append(lambda: lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        makers.append(lambda: _best_gq(d))
    out = []
    for make in makers:
        try:
            g = make()
            if g is None:
                continue
            n, e = g
            if lib.is_valid(n, e, d, D):
                out.append((n, e))
        except Exception:
            continue
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))          # K_{d,d}: valid for D >= 2
    for cand in _starts(d, D):
        if cand[0] > best[0]:
            best = cand
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 8)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except Exception:
        pass
    return best
