"""Combined program: group voltage lifts (fast orbit-based evaluation) plus grow-by-two annealing.

Python builds a few valid starting graphs (projective planes, Araujo-Pardo-Lopez, generalized
quadrangles, K_{d,d}) and keeps the best. The C engine starts from that graph, searches voltage
lifts over semidirect products Z_m x| Z_k with k base vertices per side (each candidate is checked
by BFS from only 2k orbit representatives), then grows the best graph by two vertices at a time
with edge-swap annealing. Every returned graph is checked with lib.is_valid.

Change in this version: the lift hill-climb accepts worse voltage/permutation moves with a
simulated-annealing probability instead of a fixed 2% chance, and the lift phase gets a larger
share of the time, since lifts are what produced the record-level orders.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1 (lift search): a lift over a group G of order N with k base vertices per side has
 *   2kN vertices. A_{i,g} ~ B_{j,g*s} for each dart (i, j, s). Layers are permutations, so every
 *   vertex has degree d. Left multiplication is an automorphism, so the diameter is <= D iff a BFS
 *   of depth D from each of the 2k representatives A_{i,e}, B_{j,e} reaches everything.
 *   Simulated annealing over the voltages s and the layer permutations until cost 0.
 * Phase 2 (grow by two): add one vertex per side using spare degree from d-1 deleted edges,
 *   then anneal degree-preserving edge swaps until the diameter bound holds.
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
#define MAXK 4
#define LBIG (1L << 40)

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

/* Z_m x|_r Z_k: element (a, b) is the int a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Pick a random (m, k, r) with m*k = N, gcd(r, m) = 1 and r^k = 1 mod m. */
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

/* ------------------------------------------------------------------ voltage lifts */

typedef struct {
    int k, G;
    int pi[MAXD][MAXK];  /* layer t: A-vertex i joins B-vertex pi[t][i] */
    int s[MAXD][MAXK];   /* voltage of that dart */
} Lift;

static void lift_init(Lift *L, int k, int G) {
    L->k = k;
    L->G = G;
    for (int t = 0; t < d; t++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < k; i++) {
            L->pi[t][i] = perm[i];
            L->s[t][i] = rndint(G);
        }
    }
}

static int lk_adj[MAXN][MAXD];
static int lk_deg[MAXN];
static int lk_vis[MAXN];
static int lk_dist[MAXN];
static int lk_q[MAXN];
static int lk_stamp = 0;

/* Sum over the 2k representatives of vertices not reached within D. Zero means valid. */
static long lift_cost(const Lift *L, const Grp *Gp) {
    int k = L->k, G = L->G, n = 2 * k * G;
    for (int i = 0; i < k; i++)
        for (int t1 = 0; t1 < d; t1++)
            for (int t2 = t1 + 1; t2 < d; t2++)
                if (L->pi[t1][i] == L->pi[t2][i] && L->s[t1][i] == L->s[t2][i]) return LBIG;
    for (int v = 0; v < n; v++) lk_deg[v] = 0;
    for (int t = 0; t < d; t++)
        for (int i = 0; i < k; i++) {
            int j = L->pi[t][i], s = L->s[t][i];
            for (int x = 0; x < G; x++) {
                int a = i * G + x, b = (k + j) * G + gmul(Gp, x, s);
                lk_adj[a][lk_deg[a]++] = b;
                lk_adj[b][lk_deg[b]++] = a;
            }
        }
    long total = 0;
    int nr = 0, reps[2 * MAXK];
    for (int i = 0; i < k; i++) reps[nr++] = i * G;
    for (int j = 0; j < k; j++) reps[nr++] = (k + j) * G;
    for (int r = 0; r < nr; r++) {
        int src = reps[r];
        lk_stamp++;
        int qh = 0, qt = 0;
        lk_q[qt++] = src;
        lk_vis[src] = lk_stamp;
        lk_dist[src] = 0;
        while (qh < qt) {
            int v = lk_q[qh++];
            if (lk_dist[v] >= D) continue;
            for (int e = 0; e < lk_deg[v]; e++) {
                int u = lk_adj[v][e];
                if (lk_vis[u] != lk_stamp) {
                    lk_vis[u] = lk_stamp;
                    lk_dist[u] = lk_dist[v] + 1;
                    lk_q[qt++] = u;
                }
            }
        }
        total += n - qt;
    }
    return total;
}

static void lift_build(const Lift *L, const Grp *Gp, Graph *g) {
    int k = L->k, G = L->G, n = 2 * k * G;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = v >= k * G; }
    for (int t = 0; t < d; t++)
        for (int i = 0; i < k; i++) {
            int j = L->pi[t][i], s = L->s[t][i];
            for (int x = 0; x < G; x++)
                add_edge(g, i * G + x, (k + j) * G + gmul(Gp, x, s));
        }
}

/* Simulated annealing on one lift. Returns the final cost (0 means a valid lift).
 * Worse moves are accepted with probability exp(-delta / T), T falling linearly to a floor. */
static long lift_climb(Lift *L, const Grp *Gp, int steps, double until) {
    long cost = lift_cost(L, Gp);
    for (int it = 0; it < steps && cost > 0; it++) {
        if ((it & 63) == 0 && now() > until) break;
        double T = 1.5 * (1.0 - (double)it / steps) + 0.05;
        int t = rndint(d), i = rndint(L->k);
        if (rndint(2) == 0) {
            int old = L->s[t][i];
            L->s[t][i] = rndint(L->G);
            long c2 = lift_cost(L, Gp);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else L->s[t][i] = old;
        } else {
            int i2 = rndint(L->k);
            if (i2 == i) continue;
            int tmp = L->pi[t][i];
            L->pi[t][i] = L->pi[t][i2];
            L->pi[t][i2] = tmp;
            long c2 = lift_cost(L, Gp);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else {
                tmp = L->pi[t][i];
                L->pi[t][i] = L->pi[t][i2];
                L->pi[t][i2] = tmp;
            }
        }
    }
    return cost;
}

static void lift_search(Graph *best, double until) {
    static Lift L;
    static Grp Gp;
    static Graph cand;
    static const int kch[8] = {1, 1, 1, 2, 2, 2, 3, 4};
    long moore = moore_bound();
    while (now() < until) {
        if (best->n >= moore) return;
        int k = kch[rndint(8)];
        int base = best->n / (2 * k);
        int G = base + 1 + rndint(base / 8 + 3);
        if (G < 2) G = 2;
        long n2 = 2L * k * G;
        if (n2 > moore || n2 > MAXN || n2 <= best->n) continue;
        if (!random_group(G, &Gp)) continue;
        lift_init(&L, k, G);
        if (lift_climb(&L, &Gp, 3000, until) == 0) {
            lift_build(&L, &Gp, &cand);
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
    while (now() < until && best->n + 2 <= moore_bound() && best->n + 2 <= MAXN) {
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
    if (d < 1 || d > MAXD || D < 1) {
        best.n = 1;
        best.deg[0] = 0;
        best.side[0] = 0;
        print_graph(&best);
        return 0;
    }
    if (D == 1) {
        best.n = 2;
        best.deg[0] = best.deg[1] = 0;
        best.side[0] = 0;
        best.side[1] = 1;
        add_edge(&best, 0, 1);
        print_graph(&best);
        return 0;
    }

    read_start(&best);
    int had_start = best.n > 0;
    if (best.n == 0) complete_bipartite(&best);

    long moore = moore_bound();
    if (best.n < moore) {
        double span = t_end - t0;
        double lift_until = t0 + span * (had_start ? 0.8 : 0.85);
        lift_search(&best, lift_until);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions (valid starting points; the C engine only ever improves them).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_lopez(d):
    """Araujo-Pardo and Lopez record family for d = q + 2, q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 5 for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _candidates(d, D):
    """Valid constructions for (d, D). Each builder is guarded so one failure cannot break the rest."""
    builders = []
    if D >= 3:
        builders.append(lambda: _best_pg(d))
        builders.append(lambda: _araujo_lopez(d))
    if D >= 4:
        builders.append(lambda: _best_gq(d))
    out = []
    for b in builders:
        try:
            r = b()
        except Exception:
            r = None
        if r is not None:
            out.append(r)
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for D >= 2 and serves as the fallback.
    best = lib.haar_graph(d, range(d))
    for n, e in _candidates(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    budget = 0.88 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the engine

    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 5)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except (RuntimeError, ValueError):
            pass   # keep the valid Python-built fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
