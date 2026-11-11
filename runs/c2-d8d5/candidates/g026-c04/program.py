"""Bold variant: a fast C annealer over bi-Cayley voltage lifts with base sizes up to 8 per side.

The C core scores each candidate lift by bitset reachability from the base representatives, so
one evaluation is O(N * d * D). Python handles the exact constructions and the fallback.
"""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions (calibration cases return immediately).
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
# C engine: simulated annealing over bi-Cayley lifts with base size k <= 8 per side,
# group Z_m x| Z_k2, scored by bitset reachability. Every success is re-checked
# on the explicit graph before it replaces the incumbent.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bipartite degree-diameter search: bi-Cayley lift annealing.
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
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXK 16
#define PEN 100

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

/* Z_m x|_r Z_k2 : element (a,b) = a*k2+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k2). */
typedef struct {
    int m, k2, r, G;
    int rp[MAXN];
} Grp;

/* Bi-Cayley lift: A block i = vertices i*G..i*G+G-1, B block j = (k+j)*G..
 * dart (l,i): A_{i,x} ~ B_{layer[l][i], x*volt[l][i]} for all x.
 * layer[l] is a permutation, so every vertex has exactly dl neighbours. */
typedef struct {
    int k, dl, G, N;
    unsigned char layer[MAXD][MAXK];
    int volt[MAXD][MAXK];
    int nbr[MAXD][MAXN];
} Lift;

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

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

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
            memcpy(dst, src, sizeof(uint64_t) * W);
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

static int gmul(const Grp *g, int x, int y) {
    int a = x / g->k2, b = x % g->k2, c = y / g->k2, e = y % g->k2;
    return (int)(((long)a + (long)g->rp[b] * c) % g->m) * g->k2 + (b + e) % g->k2;
}

/* Random semidirect group with order >= target. r = 1 (direct product) is always valid. */
static void make_group(Grp *g, int target) {
    static const int ks[12] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 16};
    int k2 = ks[rndint(12)];
    int m = (target + k2 - 1) / k2;
    if (m < 2) m = 2;
    if (rndint(3) == 0) m += rndint(3);
    int r = 1 % m;
    if (k2 > 1 && m > 2 && rndint(2)) {
        for (int tries = 0; tries < 200; tries++) {
            int c = 2 + rndint(m - 2);
            if (gcd(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
        }
    }
    g->m = m;
    g->k2 = k2;
    g->r = r;
    g->G = m * k2;
    g->rp[0] = 1 % m;
    for (int b = 1; b < k2; b++) g->rp[b] = (int)((long)g->rp[b - 1] * r % m);
}

static void set_dart(Lift *L, const Grp *g, int l, int i) {
    int j = L->layer[l][i], s = L->volt[l][i], G = L->G, k = L->k;
    int *na = L->nbr[l];
    for (int x = 0; x < G; x++) {
        int y = gmul(g, x, s);
        na[i * G + x] = (k + j) * G + y;
        na[(k + j) * G + y] = i * G + x;
    }
}

/* Repeated (i, j, voltage) triples across layers would create multi-edges. */
static long dupcount(const Lift *L) {
    long c = 0;
    for (int i = 0; i < L->k; i++)
        for (int l = 1; l < L->dl; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (L->layer[l][i] == L->layer[l2][i] && L->volt[l][i] == L->volt[l2][i]) c++;
    return c;
}

/* Sum over base representatives b of the number of vertices at distance > D from rep_b.
 * Zero exactly when the lift has diameter <= D (left action makes the graph vertex-transitive per block). */
static long lift_cost(const Lift *L) {
    static uint64_t bufA[MAXN], bufB[MAXN];
    int N = L->N, dl = L->dl, nb = 2 * L->k, G = L->G;
    uint64_t *cur = bufA, *nxt = bufB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < nb; b++) cur[b * G] = 1ULL << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t r = cur[v];
            for (int l = 0; l < dl; l++) r |= cur[L->nbr[l][v]];
            nxt[v] = r;
            changed |= (r != cur[v]);
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    long un = 0;
    for (int v = 0; v < N; v++) un += nb - __builtin_popcountll(cur[v]);
    return un;
}

/* Random start, then annealing on the cost. Returns 1 if the lift has diameter <= D. */
static int anneal(Lift *L, const Grp *g, long iters, long patience) {
    int k = L->k, dl = L->dl, G = L->G;
    for (int l = 0; l < dl; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1), t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < k; i++) {
            L->layer[l][i] = (unsigned char)perm[i];
            L->volt[l][i] = rndint(G);
        }
    }
    for (int l = 0; l < dl; l++)
        for (int i = 0; i < k; i++) set_dart(L, g, l, i);

    long cost = lift_cost(L) + PEN * dupcount(L);
    double c0 = cost > 0 ? (double)cost : 1.0;
    long best = cost, last = 0;
    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 127) == 0 && now() > t_end) break;
        if (t - last > patience) break;
        double temp = 0.5 + 0.02 * c0 * (1.0 - (double)t / (double)iters);
        long c2;
        if (k >= 2 && rndint(4) == 0) {
            int l = rndint(dl), i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            unsigned char tmp = L->layer[l][i1];
            L->layer[l][i1] = L->layer[l][i2];
            L->layer[l][i2] = tmp;
            set_dart(L, g, l, i1);
            set_dart(L, g, l, i2);
            c2 = lift_cost(L) + PEN * dupcount(L);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                tmp = L->layer[l][i1];
                L->layer[l][i1] = L->layer[l][i2];
                L->layer[l][i2] = tmp;
                set_dart(L, g, l, i1);
                set_dart(L, g, l, i2);
            }
        } else {
            int l = rndint(dl), i = rndint(k);
            int old = L->volt[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            L->volt[l][i] = nw;
            set_dart(L, g, l, i);
            c2 = lift_cost(L) + PEN * dupcount(L);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                L->volt[l][i] = old;
                set_dart(L, g, l, i);
            }
        }
        if (cost < best) { best = cost; last = t; }
    }
    return cost == 0;
}

static void build_full(Graph *g, const Lift *L, const Grp *gr) {
    int k = L->k, G = L->G;
    g->n = L->N;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= k * G);
    }
    for (int l = 0; l < L->dl; l++)
        for (int i = 0; i < k; i++) {
            int j = L->layer[l][i], s = L->volt[l][i];
            for (int x = 0; x < G; x++)
                add_edge(g, i * G + x, (k + j) * G + gmul(gr, x, s));
        }
}

static void lift_search(Graph *best, double until) {
    static Lift L;
    static Grp g;
    static Graph cand;
    static const int kset[9] = {1, 1, 2, 2, 2, 3, 4, 6, 8};
    long moore = moore_bound();
    int fails = 0;
    while (now() < until && fails < 3000) {
        int k = kset[rndint(9)];
        long nbest = best->n;
        long Gmin = nbest / (2L * k) + 1 + rndint(3);
        if (Gmin < 2) Gmin = 2;
        make_group(&g, (int)Gmin);
        long N = 2L * k * g.G;
        if (N > MAXN || N > moore || N <= nbest) { fails++; continue; }
        L.k = k;
        L.dl = d;
        L.G = g.G;
        L.N = (int)N;
        if (anneal(&L, &g, 30000, 6000)) {
            build_full(&cand, &L, &g);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
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

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (D >= 2 && best.n < moore_bound() && best.n < MAXN) lift_search(&best, t_end);
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
        """Adopt (n, e) if it is a larger valid graph."""
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

    # Bold phase: C annealing over bi-Cayley lifts, seeded by the best graph so far.
    if D >= 2 and d <= 32:
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=best, timeout=c_budget + 8)
                out = lib.parse_graph_text(text)
                consider(out[0], out[1])
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
