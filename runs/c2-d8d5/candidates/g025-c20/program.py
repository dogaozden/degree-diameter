"""Lift search with orbit-representative cost: a voltage-lift annealer over Z_m x| Z_k bi-Cayley base graphs, then grow-by-two."""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact and small constructions (calibration cases return immediately).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C engine.
# Lifts: base graph on P+P vertices, d darts per block (d permutation matrices),
# voltages in a semidirect group Z_m x| Z_k of order N. The lift has 2PN vertices.
# Cost = number of (block representative, vertex) pairs at distance > D. Left
# multiplication by group elements is an automorphism, so only the 2P block
# representatives need BFS. Zero cost means the lift has diameter <= D.
# Then grow-by-two adds vertices to the best valid graph.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid start), or "0 0".
 * stdout: "n m" + edge lines, the largest valid graph found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXW (MAXN / 64)
#define MAXD 32
#define MAXP 4
#define MAXH 2048
#define MAXDART (MAXD * MAXP)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

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

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D. Fills badv[v] = number of bad partners of v. */
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

/* ---------------- group and lift state ---------------- */

static unsigned short MT[MAXH][MAXH];   /* MT[x][y] = x*y in the group */
static int INVG[MAXH];
static int GM, GK, NG, P;
static int rp[MAXH];                    /* rp[b] = r^b mod m */
static int perm[MAXD][MAXP];            /* base: d permutations of P */
static int dv[MAXDART], ia[MAXDART], ja[MAXDART];
static int listA[MAXP][MAXD], listB[MAXP][MAXD];
static int ND;

static int queue_[MAXN], depth_[MAXN], vis_[MAXN];
static int stampc = 0;

/* Z_m x|_r Z_k: element (a,b) = a*k+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k). */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    return (int)(((long)a + (long)rp[b] * c) % GM) * GK + (b + e) % GK;
}

static void setup_group(int N) {
    int dvs[MAXH], nd = 0;
    for (int x = 1; x <= N; x++)
        if (N % x == 0) dvs[nd++] = x;
    int m = dvs[rndint(nd)], k = N / m;
    int r = 1 % m;
    if (m > 2) {
        for (int tries = 0; tries < 400; tries++) {
            int c = 2 + rndint(m - 2);
            if (gcd(c, m) == 1 && powmod(c, k, m) == 1 % m) { r = c; break; }
        }
    }
    GM = m; GK = k; NG = N;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) MT[x][y] = (unsigned short)gmul(x, y);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x][y] == 0) { INVG[x] = y; break; }
}

static void make_base(void) {
    for (;;) {
        for (int t = 0; t < d; t++) {
            for (int i = 0; i < P; i++) perm[t][i] = i;
            for (int i = P - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[t][i]; perm[t][i] = perm[t][j]; perm[t][j] = s;
            }
        }
        int am[MAXP][MAXP];
        memset(am, 0, sizeof am);
        for (int t = 0; t < d; t++)
            for (int i = 0; i < P; i++) am[i][perm[t][i]] = 1;
        int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, cnt = 1;
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            if (v < P) {
                for (int j = 0; j < P; j++)
                    if (am[v][j] && !seen[P + j]) { seen[P + j] = 1; cnt++; stack[top++] = P + j; }
            } else {
                int j = v - P;
                for (int i = 0; i < P; i++)
                    if (am[i][j] && !seen[i]) { seen[i] = 1; cnt++; stack[top++] = i; }
            }
        }
        if (cnt == 2 * P) return;
    }
}

static void index_base(void) {
    ND = d * P;
    for (int t = 0; t < d; t++)
        for (int i = 0; i < P; i++) {
            int idx = t * P + i;
            ia[idx] = i;
            ja[idx] = perm[t][i];
        }
    for (int i = 0; i < P; i++)
        for (int t = 0; t < d; t++) listA[i][t] = t * P + i;
    for (int t = 0; t < d; t++)
        for (int i = 0; i < P; i++) listB[perm[t][i]][t] = t * P + i;
}

/* True if giving dart idx voltage g would duplicate another dart with the same block pair. */
static int clash(int idx, int g) {
    for (int k = 0; k < ND; k++)
        if (k != idx && ia[k] == ia[idx] && ja[k] == ja[idx] && dv[k] == g) return 1;
    return 0;
}

static void init_voltages(void) {
    for (int idx = 0; idx < ND; idx++) dv[idx] = -1;
    for (int idx = 0; idx < ND; idx++) {
        int g;
        do { g = rndint(NG); } while (clash(idx, g));
        dv[idx] = g;
    }
}

/* Neighbours of lift vertex v. A-block i vertex x ~ B-block j vertex x*g. */
static int nbrs(int v, int *out) {
    int PN = P * NG;
    int c = 0;
    if (v < PN) {
        int i = v / NG, x = v % NG;
        for (int t = 0; t < d; t++) {
            int idx = listA[i][t];
            out[c++] = PN + ja[idx] * NG + MT[x][dv[idx]];
        }
    } else {
        int y0 = v - PN;
        int j = y0 / NG, y = y0 % NG;
        for (int t = 0; t < d; t++) {
            int idx = listB[j][t];
            out[c++] = ia[idx] * NG + MT[y][INVG[dv[idx]]];
        }
    }
    return c;
}

/* Sum over the 2P block representatives of vertices not within distance D. Zero iff valid. */
static long lift_cost(void) {
    int n2 = 2 * P * NG;
    long total = 0;
    int out[MAXD];
    for (int b = 0; b < 2 * P; b++) {
        int src = b * NG;
        stampc++;
        int head = 0, tail = 0;
        queue_[tail++] = src;
        vis_[src] = stampc;
        depth_[src] = 0;
        while (head < tail) {
            int v = queue_[head++];
            if (depth_[v] >= D) continue;
            int c = nbrs(v, out);
            for (int k = 0; k < c; k++) {
                int w = out[k];
                if (vis_[w] != stampc) {
                    vis_[w] = stampc;
                    depth_[w] = depth_[v] + 1;
                    queue_[tail++] = w;
                }
            }
        }
        total += n2 - tail;
    }
    return total;
}

static int anneal(long steps) {
    long cur = lift_cost();
    const double T0 = 2.0;
    for (long s = 0; s < steps && cur > 0; s++) {
        if ((s & 127) == 0 && now() > t_end) return 0;
        int idx = rndint(ND);
        int old = dv[idx];
        int g;
        do { g = rndint(NG); } while (g == old || clash(idx, g));
        dv[idx] = g;
        long nc = lift_cost();
        double T = T0 * (1.0 - (double)s / (double)steps) + 0.05;
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) cur = nc;
        else dv[idx] = old;
    }
    return cur == 0;
}

static void build_full(Graph *g) {
    int PN = P * NG;
    g->n = 2 * PN;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= PN; }
    for (int idx = 0; idx < ND; idx++) {
        int i = ia[idx], j = ja[idx], gg = dv[idx];
        for (int x = 0; x < NG; x++)
            add_edge(g, i * NG + x, PN + j * NG + MT[x][gg]);
    }
}

static void lift_phase(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        int r = rndint(10);
        P = r < 3 ? 1 : r < 6 ? 2 : r < 8 ? 3 : 4;
        int N = best->n / (2 * P) + 1 + rndint(2);
        if (N < d + 1) N = d + 1;
        if (2L * P * N > moore || 2 * P * N > MAXN || N > MAXH) {
            if (++fails > 500) break;
            continue;
        }
        make_base();
        index_base();
        setup_group(N);
        init_voltages();
        if (anneal(20000)) {
            build_full(&cand);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ---------------- grow-by-two ---------------- */

static int bad_list[MAXN];
static int badsave[MAXN];

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
        int nbad = 0;
        for (int w = 0; w < work->n; w++)
            if (badv[w] > 0) bad_list[nbad++] = w;
        int v = nbad ? bad_list[rndint(nbad)] : rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (work->side[s] != work->side[v] || s == v || work->deg[s] == 0) continue;
        int t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
        memcpy(badsave, badv, sizeof(int) * work->n);
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
            memcpy(badv, badsave, sizeof(int) * work->n);
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
    if (d < 1 || D < 1 || d > MAXD) { printf("0 0\n"); return 0; }
    read_start(&best);
    int had_start = best.n > 0;
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && best.n < moore_bound()) {
        double share = had_start ? 0.7 : 0.85;
        lift_phase(&best, t0 + (t_end - t0) * share);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Replace the best graph if (n, e) is a larger valid graph."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Lift and grow search in C, starting from the best graph so far.
    if D >= 2 and time.monotonic() < end - 1.0:
        c_budget = end - time.monotonic() - 0.5
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                             stdin_graph=best, timeout=c_budget + 8)
            out = lib.parse_graph_text(text)
            consider(out[0], out[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
