"""Combined degree-diameter search.

Python builds the best known start graph (projective planes, Araujo-Pardo-Lopez,
generalized quadrangle W(q), or K_{d,d}). The C engine then runs simulated annealing
over group voltage lifts (semidirect products Z_m x| Z_k, orbit-BFS cost), followed
by a grow-by-two annealing phase. Every returned graph is checked with lib.is_valid,
and the baseline is kept if anything fails.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v" (valid start graph), or "0 0".
 * stdout:  "n m" then m lines "u v" for the best valid graph found.
 *
 * Phase 1: simulated annealing over voltage lifts. A base with k vertices per side,
 *          d layers (each a permutation of the k B-vertices), voltages in a group of order N.
 *          Left multiplication is an automorphism, so the cost is the number of vertices
 *          not reached within D steps from the 2k class representatives.
 * Phase 2: grow by two, adding one vertex per side and annealing degree-preserving swaps.
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
#define BIGC 1000000000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

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

/* Z_gm x|_gr Z_gk: element (a, b) is coded a*gk + b. */
typedef struct {
    int gm, gk, gr;
    int rp[MAXN]; /* rp[b] = gr^b mod gm */
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->gk, b = x % G->gk, c = y / G->gk, e = y % G->gk;
    return (int)((a + (long)G->rp[b] * c) % G->gm) * G->gk + (b + e) % G->gk;
}

/* Uniformly random (m, k, r) with m*k = N, gcd(r, m) = 1, r^k = 1 mod m. */
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
            if (rndint((int)count) == 0) { G->gm = m; G->gk = k; G->gr = r; }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->gm;
    for (int b = 1; b < G->gk; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->gr % G->gm);
    return 1;
}

/* ------------------------------------------------------------ voltage lifts */

typedef struct {
    int k, N;
    int perm[MAXD][MAXK]; /* layer t: A_i joins B_perm[t][i] */
    int sv[MAXD][MAXK];   /* voltage of dart (t, i) */
} Lift;

static int ladj[MAXN][MAXD];
static int ldeg[MAXN];
static int vis[MAXN];
static int visstamp = 0;
static int bq[MAXN];

/* Vertices: A_i,x = i*N + x and B_j,x = (k+j)*N + x. Dart (t,i) joins A_i,x to B_j,x*s. */
static void lift_adj(const Lift *L, const Grp *G) {
    int k = L->k, N = L->N, nv = 2 * k * N;
    for (int v = 0; v < nv; v++) ldeg[v] = 0;
    for (int t = 0; t < d; t++)
        for (int i = 0; i < k; i++) {
            int j = L->perm[t][i], s = L->sv[t][i];
            for (int x = 0; x < N; x++) {
                int a = i * N + x, b = (k + j) * N + gmul(G, x, s);
                ladj[a][ldeg[a]++] = b;
                ladj[b][ldeg[b]++] = a;
            }
        }
}

/* Count of (class representative, vertex) pairs at distance > D. Zero means valid.
 * Duplicate darts (same i, same j, same voltage) give BIGC. */
static long lift_cost(const Lift *L, const Grp *G) {
    int k = L->k, N = L->N, nv = 2 * k * N;
    for (int i = 0; i < k; i++)
        for (int t1 = 0; t1 < d; t1++)
            for (int t2 = t1 + 1; t2 < d; t2++)
                if (L->perm[t1][i] == L->perm[t2][i] && L->sv[t1][i] == L->sv[t2][i])
                    return BIGC;
    lift_adj(L, G);
    long total = 0;
    for (int r = 0; r < 2 * k; r++) {
        int src = r * N;
        visstamp++;
        int head = 0, tail = 0;
        bq[tail++] = src;
        vis[src] = visstamp;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int lend = tail;
            while (head < lend) {
                int u = bq[head++];
                for (int x = 0; x < d; x++) {
                    int v = ladj[u][x];
                    if (vis[v] != visstamp) { vis[v] = visstamp; bq[tail++] = v; }
                }
            }
        }
        total += nv - tail;
    }
    return total;
}

static void lift_build(Graph *g, const Lift *L, const Grp *G) {
    int k = L->k, N = L->N;
    g->n = 2 * k * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= k * N; }
    for (int t = 0; t < d; t++)
        for (int i = 0; i < k; i++) {
            int j = L->perm[t][i], s = L->sv[t][i];
            for (int x = 0; x < N; x++)
                add_edge(g, i * N + x, (k + j) * N + gmul(G, x, s));
        }
}

/* Simulated annealing over voltages (and occasionally the layer permutations). */
static long anneal_lift(Lift *L, const Grp *G, long iters, double until) {
    int k = L->k, N = L->N;
    for (int t = 0; t < d; t++) {
        int p[MAXK];
        for (int i = 0; i < k; i++) p[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1), s = p[i];
            p[i] = p[j];
            p[j] = s;
        }
        for (int i = 0; i < k; i++) {
            L->perm[t][i] = p[i];
            L->sv[t][i] = rndint(N);
        }
    }
    long cost = lift_cost(L, G);
    Lift bestL = *L;
    long bestc = cost;
    for (long it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && now() > until) break;
        double T = 2.0 * (1.0 - (double)it / (double)iters) + 0.05;
        Lift old = *L;
        int t = rndint(d);
        if (k == 1 || rndint(10) < 8) {
            int i = rndint(k);
            L->sv[t][i] = rndint(N);
        } else {
            int a = rndint(k), b = rndint(k);
            int s = L->perm[t][a];
            L->perm[t][a] = L->perm[t][b];
            L->perm[t][b] = s;
        }
        long c2 = lift_cost(L, G);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost < bestc) { bestc = cost; bestL = *L; }
        } else {
            *L = old;
        }
    }
    *L = bestL;
    return bestc;
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    static Lift L;
    long moore = moore_bound();
    if (moore > MAXN) moore = MAXN;
    while (now() < until) {
        if (best->n + 2 > moore) return;
        int r = rndint(10);
        int k = r < 4 ? 1 : (r < 8 ? 2 : 3);
        int base = best->n / (2 * k);
        int N = base + 1 + rndint(base / 8 + 3);
        if (N * k < d) N = (d + k - 1) / k;
        if (2L * k * N > moore) continue;
        if (!random_group(N, &G)) continue;
        L.k = k;
        L.N = N;
        long c = anneal_lift(&L, &G, 6000, until);
        if (c == 0) {
            lift_build(&cand, &L, &G);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
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
    while (now() < until && best->n + 2 <= moore_bound()) {
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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (best.n < moore_bound()) {
        double ts = now();
        double span = t_end - ts;
        if (span > 0.5) {
            lift_search(&best, ts + span * 0.7);
            if (best.n > 0) grow_search(&best, t_end);
        }
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python baselines
# ----------------------------------------------------------------------------

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


def _baselines(d, D):
    """Largest valid known construction among the cheap families (always at least K_{d,d})."""
    best = lib.haar_graph(d, range(d))

    def attempt(make):
        nonlocal best
        try:
            n, e = make()
        except Exception:
            return
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                attempt(lambda q=q: lib.projective_plane_incidence(q))
                break
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            attempt(lambda: lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        for q in range(min(d - 1, 9), 1, -1):
            if lib.is_prime_power(q):
                attempt(lambda q=q: _gq_w(q))
                break
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _baselines(d, D)
    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 8.0)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
