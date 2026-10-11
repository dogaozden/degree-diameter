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
 * Phase 1 (lift search): voltage lifts of a d-regular base multigraph with k vertices per
 *   side over a semidirect product Z_m x| Z_k2 of order G. The lift has 2kG vertices and is
 *   d-regular and bipartite. Simulated annealing over voltages and layer pairings. The cost is
 *   the number of (representative, vertex) pairs not reached within D steps, plus a penalty
 *   for duplicate darts. Left multiplication is an automorphism, so BFS from the 2k
 *   representatives is exact.
 * Phase 2 (grow by two): add one vertex per side using spare slots of d-1 deleted edges,
 *   then anneal degree-preserving edge swaps with a bitset distance check.
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
#define MAXDART (MAXD * MAXK)
#define BIGPEN 1000000L

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

static void grp_set(Grp *G, int m, int k, int r) {
    G->m = m;
    G->k = k;
    G->r = r;
    G->rp[0] = 1 % m;
    for (int b = 1; b < k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * r % m);
}

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    int aa = (int)(((long)a + (long)G->rp[b] * c) % G->m);
    return aa * G->k + (b + e) % G->k;
}

/* Uniform random semidirect product of order N (reservoir over all valid (m, r)). */
static int random_group(int N, Grp *out) {
    int count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k2 = N / m;
        if (m == 1) {
            count++;
            if (rndint(count) == 0) grp_set(out, 1, k2, 0);
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k2, m) != 1 % m) continue;
            count++;
            if (rndint(count) == 0) grp_set(out, m, k2, r);
        }
    }
    return count > 0;
}

/* ------------------------------------------------------------------ voltage lifts */

static int LA[MAXN][MAXD];
static int LD[MAXN];
static int vis[MAXN];
static int vstamp = 0;
static int qbuf[MAXN];

/* Darts t: A-vertex di[t] -> B-vertex dj[t] with voltage ds[t].
 * A-vertex (i, g) is i*G + g; B-vertex (j, h) is k*G + j*G + h. */
static void lift_build(int k, int G, int nd, const int *di, const int *dj, const int *ds,
                       const Grp *Gr) {
    int N = 2 * k * G;
    for (int v = 0; v < N; v++) LD[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < G; x++) {
            int a = di[t] * G + x;
            int b = k * G + dj[t] * G + gmul(Gr, x, ds[t]);
            LA[a][LD[a]++] = b;
            LA[b][LD[b]++] = a;
        }
}

static long lift_cost(int k, int G, int nd, const int *di, const int *dj, const int *ds,
                      const Grp *Gr) {
    long pen = 0;
    for (int t = 0; t < nd; t++)
        for (int u = 0; u < t; u++)
            if (di[t] == di[u] && dj[t] == dj[u] && ds[t] == ds[u]) pen += BIGPEN;
    lift_build(k, G, nd, di, dj, ds, Gr);
    int N = 2 * k * G;
    long total = 0;
    for (int s = 0; s < 2 * k; s++) {
        int src = s < k ? s * G : k * G + (s - k) * G;
        vstamp++;
        int head = 0, tail = 0;
        vis[src] = vstamp;
        qbuf[tail++] = src;
        for (int lvl = 0; lvl < D; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int v = qbuf[head++];
                for (int q = 0; q < LD[v]; q++) {
                    int w = LA[v][q];
                    if (vis[w] != vstamp) {
                        vis[w] = vstamp;
                        qbuf[tail++] = w;
                    }
                }
            }
        }
        total += N - tail;
    }
    return total + pen;
}

static void lift_to_graph(int k, int G, int nd, const int *di, const int *dj, const int *ds,
                          const Grp *Gr, Graph *g) {
    int N = 2 * k * G;
    g->n = N;
    for (int v = 0; v < N; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= k * G;
    }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < G; x++) {
            int a = di[t] * G + x;
            int b = k * G + dj[t] * G + gmul(Gr, x, ds[t]);
            add_edge(g, a, b);
        }
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp Gr;
    int di[MAXDART], dj[MAXDART], ds[MAXDART];
    static const int ks[] = {1, 1, 2, 2, 2, 3, 3, 4};
    long mb = moore_bound();
    while (now() < until) {
        if (best->n + 2 > mb || best->n + 2 > MAXN) return;
        int k = ks[rndint(8)];
        int nd = k * d;
        if (nd > MAXDART) continue;
        long G = (best->n + 2 + 2L * k - 1) / (2L * k);
        if (G < d) G = d;
        G += rndint(3);
        if (2L * k * G > mb || 2L * k * G > MAXN) continue;
        if (!random_group((int)G, &Gr)) continue;

        for (int l = 0; l < d; l++) {
            int perm[MAXK];
            for (int i = 0; i < k; i++) perm[i] = i;
            for (int i = k - 1; i > 0; i--) {
                int j = rndint(i + 1), s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
            for (int i = 0; i < k; i++) {
                int t = l * k + i;
                di[t] = i;
                dj[t] = perm[i];
                ds[t] = rndint((int)G);
            }
        }

        long cost = lift_cost(k, (int)G, nd, di, dj, ds, &Gr);
        const long steps = 20000;
        for (long s = 0; s < steps && cost > 0; s++) {
            if ((s & 255) == 0 && now() > until) break;
            double T = 2.0 * (1.0 - (double)s / steps) + 0.05;
            if (rndint(4) == 0) {
                /* swap two targets inside one layer (keeps each layer a permutation) */
                int l = rndint(d), i1 = rndint(k), i2 = rndint(k);
                if (i1 == i2) continue;
                int t1 = l * k + i1, t2 = l * k + i2;
                int tmp = dj[t1];
                dj[t1] = dj[t2];
                dj[t2] = tmp;
                long c2 = lift_cost(k, (int)G, nd, di, dj, ds, &Gr);
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    tmp = dj[t1];
                    dj[t1] = dj[t2];
                    dj[t2] = tmp;
                }
            } else {
                /* change one voltage */
                int t = rndint(nd);
                int old = ds[t];
                int nv = rndint((int)G);
                if (nv == old) continue;
                ds[t] = nv;
                long c2 = lift_cost(k, (int)G, nd, di, dj, ds, &Gr);
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else ds[t] = old;
            }
        }
        if (cost == 0) {
            lift_to_graph(k, (int)G, nd, di, dj, ds, &Gr, &cand);
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
    if (d < 1 || D < 1 || d > MAXD) {
        complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (D >= 2 && best.n < moore_bound()) {
        double share = (2L * best.n < moore_bound()) ? 0.7 : 0.4;
        lift_search(&best, t0 + (t_end - t0) * share);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


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
    """W(q) for the largest prime power q with q + 1 <= d (small q only, for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def known_start(d, D):
    """Best known construction Python can build directly for (d, D), or None."""
    if D == 3:
        if lib.is_prime_power(d - 1):
            return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    if D == 4 and d >= 3:
        return _best_gq(d)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + 0.8 * time_limit - 2.0

    if D <= 1:
        out = (2, [(0, 1)]) if d >= 1 else (1, [])
        return out if lib.is_valid(out[0], out[1], d, D) else (1, [])
    if d < 1:
        return (1, [])

    # Always-valid fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    try:
        start = known_start(d, D)
    except Exception:
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    budget = end - time.monotonic()
    if best[0] < lib.moore_bound(d, D) and budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 3)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
