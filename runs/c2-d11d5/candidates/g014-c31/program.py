"""Combined program: a C bi-Cayley voltage-lift annealer over semidirect groups Z_m x| Z_k2,
followed by a C grow-by-two engine that inserts vertices into the best graph found (only while
the graph is small enough for the C repair step to finish in its slice).

Every returned graph is checked with lib.is_valid. K_{d,d} (or a known construction) is the fallback.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
/* Grow-by-two search core.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid bipartite start), or "0 0".
 * stdout: "n m" + edges of the best valid graph found (never worse than the input).
 *
 * Each step inserts one vertex on each side, using the spare degree freed by d-1 deleted
 * edges, then anneals degree-preserving edge swaps until every pair is within distance D.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 32
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static uint64_t rng_state = 88172645463325252ULL;
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

/* Number of unordered pairs at distance > D; also sets badv[v]. */
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

static double t_end;
static Graph gbest, gwork;
static int used[MAXN];
static int stamp = 0;

/* One grow-by-two attempt starting from best; on success work holds n+2 valid vertices. */
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

static void grow_search(double until) {
    while (now() < until && gbest.n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(&gbest, &gwork, now() + slice)) copy_graph(&gbest, &gwork);
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
    t_end = t0 + limit * 0.9 - 0.2;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    read_start(&gbest);
    if (gbest.n == 0) { printf("0 0\n"); return 0; }
    grow_search(t_end);
    if (!is_valid(&gbest)) { printf("0 0\n"); return 0; }
    print_graph(&gbest);
    return 0;
}
'''


LIFT_C_SOURCE = r'''
/* Bi-Cayley voltage-lift annealer over the semidirect group Z_m x| Z_k2.
 * Usage: prog d D k m k2 r seed budget patience
 * Base graph: k A-blocks and k B-blocks. Layer l pairs A_i with B_{perm[l][i]} through
 * voltage s = sv[l][i]: A_{i,g} ~ B_{p,g*s}. Element (a,b) is coded as a*k2+b with
 * (a,b)(c,e) = (a + r^b c, b+e). Every layer is a permutation, so every vertex has degree d.
 * Output: "n m" + edges of a valid lift, or "0 0" when none was found within the budget.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 40
#define MAXK 8
#define MAXG 4096
#define MAXN (2 * MAXK * MAXG)
#define PEN 1000L
#define SCHED 4000

static int d, D, k, m, k2, G, N;
static int pw[MAXG];
static int nbr[MAXD][MAXN];
static int perm[MAXD][MAXK];
static int sv[MAXD][MAXK], isv[MAXD][MAXK];
static uint16_t cur[MAXN], cand[MAXN], nxt[MAXN];
static uint16_t fullmask;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gmul(int x, int y) {
    int a = x / k2, b = x - a * k2;
    int c = y / k2, e = y - c * k2;
    long long t = ((long long)a + (long long)pw[b] * c) % m;
    return (int)(t * k2 + (b + e) % k2);
}

static int ginv(int x) {
    int a = x / k2, b = x - a * k2;
    int nb = (k2 - b) % k2;
    long long t = (m - ((long long)pw[nb] * a) % m) % m;
    return (int)(t * k2 + nb);
}

/* Write layer l's darts for base A-block i (and its paired B-block). */
static void set_dart(int l, int i) {
    int j = perm[l][i], s = sv[l][i], is = isv[l][i];
    int A0 = i * G, B0 = (k + j) * G;
    for (int g = 0; g < G; g++) {
        nbr[l][A0 + g] = B0 + gmul(g, s);
        nbr[l][B0 + g] = A0 + gmul(g, is);
    }
}

static int find_i(int l, int j) {
    for (int i = 0; i < k; i++)
        if (perm[l][i] == j) return i;
    return 0;
}

static void random_init(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) perm[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = t;
        }
        for (int i = 0; i < k; i++) {
            sv[l][i] = rndint(G);
            isv[l][i] = ginv(sv[l][i]);
            set_dart(l, i);
        }
    }
}

static void swap_perm(int l, int i1, int i2) {
    int t = perm[l][i1];
    perm[l][i1] = perm[l][i2];
    perm[l][i2] = t;
}

/* Bit v of reach[w] is set when the representative of block v is within distance D of w.
 * Returns the number of (vertex, block) pairs left unreached; result is left in cand. */
static long eval_cand(void) {
    for (int v = 0; v < N; v++) cand[v] = 0;
    for (int b = 0; b < 2 * k; b++) cand[b * G] = (uint16_t)(1u << b);
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint16_t x = cand[v];
            for (int l = 0; l < d; l++) x |= cand[nbr[l][v]];
            nxt[v] = x;
            changed |= (x != cand[v]);
        }
        memcpy(cand, nxt, sizeof(uint16_t) * N);
        if (!changed) break;
    }
    long cnt = 0;
    for (int v = 0; v < N; v++) cnt += __builtin_popcount(cand[v]);
    return 2L * k * N - cnt;
}

/* Number of repeated darts (same A-block, same B-block, same voltage in two layers). */
static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1][i] == perm[l2][i] && sv[l1][i] == sv[l2][i]) c++;
    return c;
}

static void output_graph(void) {
    long E = (long)k * G * d;
    printf("%d %ld\n", N, E);
    for (int u = 0; u < k * G; u++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", u, nbr[l][u]);
}

int main(int argc, char **argv) {
    if (argc < 10) {
        fprintf(stderr, "usage: %s d D k m k2 r seed budget patience\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    k = atoi(argv[3]);
    m = atoi(argv[4]);
    k2 = atoi(argv[5]);
    int r = atoi(argv[6]);
    long seed = atol(argv[7]);
    double budget = atof(argv[8]);
    long patience = atol(argv[9]);

    if (d < 1 || d > MAXD || D < 2 || k < 1 || k > MAXK || m < 2 || k2 < 1) {
        printf("0 0\n");
        return 0;
    }
    if ((long)m * k2 > MAXG) { printf("0 0\n"); return 0; }
    G = m * k2;
    N = 2 * k * G;
    if (N > MAXN) { printf("0 0\n"); return 0; }

    r %= m;
    if (r < 0) r += m;
    long long chk = 1 % m;
    for (int i = 0; i < k2; i++) chk = chk * r % m;
    if (chk != 1 % m) { printf("0 0\n"); return 0; }
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    fullmask = (uint16_t)((1u << (2 * k)) - 1);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double deadline = now() + budget;
    int found = 0;
    while (!found && now() < deadline) {
        random_init();
        long cost = eval_cand() + PEN * dupcount();
        memcpy(cur, cand, sizeof(uint16_t) * N);
        double c0 = cost > 1 ? (double)cost : 1.0;
        long best = cost, last = 0;
        int expired = 0;
        for (long t = 0; cost > 0; t++) {
            if ((t & 31) == 0 && now() > deadline) { expired = 1; break; }
            if (t - last > patience || t >= SCHED) break;
            double temp = 0.01 * c0 * (1.0 - (double)t / SCHED);
            if (temp < 0.5) temp = 0.5;
            double x = rnd01();

            if (k >= 2 && x < 0.25) {
                int ls = rndint(d);
                int i1 = rndint(k), i2 = rndint(k - 1);
                if (i2 >= i1) i2++;
                swap_perm(ls, i1, i2);
                set_dart(ls, i1);
                set_dart(ls, i2);
                long c2 = eval_cand() + PEN * dupcount();
                if (c2 <= cost || rnd01() < exp((double)(cost - c2) / temp)) {
                    cost = c2;
                    memcpy(cur, cand, sizeof(uint16_t) * N);
                    if (cost < best) { best = cost; last = t; }
                } else {
                    swap_perm(ls, i1, i2);
                    set_dart(ls, i1);
                    set_dart(ls, i2);
                }
                continue;
            }

            int l = 0, i = 0, picked = 0;
            if (rnd01() < 0.4) {
                int v = -1;
                for (int tr = 0; tr < 50; tr++) {
                    int w = rndint(N);
                    if (cur[w] != fullmask) { v = w; break; }
                }
                if (v >= 0) {
                    int block = v / G;
                    l = rndint(d);
                    i = (block < k) ? block : find_i(l, block - k);
                    picked = 1;
                }
            }
            if (!picked) {
                l = rndint(d);
                i = rndint(k);
            }
            int old = sv[l][i], oldi = isv[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            sv[l][i] = nw;
            isv[l][i] = ginv(nw);
            set_dart(l, i);
            long c2 = eval_cand() + PEN * dupcount();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / temp)) {
                cost = c2;
                memcpy(cur, cand, sizeof(uint16_t) * N);
                if (cost < best) { best = cost; last = t; }
            } else {
                sv[l][i] = old;
                isv[l][i] = oldi;
                set_dart(l, i);
            }
        }
        if (cost == 0) found = 1;
        if (expired) break;
    }

    if (found) output_graph();
    else printf("0 0\n");
    return 0;
}
'''


_PATIENCE = 1200
_LIFT_SLICE = 4.0
_GROW_MAX_N = 1500
_KS = (1, 2, 3, 4, 6)


# ----------------------------------------------------------------------------
# Small exact constructions.
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


# ----------------------------------------------------------------------------
# Group sampling and the C lift search.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _lift_c(d, D, k, m, k2, r, seed, budget):
    """Run the C voltage-lift annealer for one group. Returns (n, edges) or None."""
    text = lib.run_c(LIFT_C_SOURCE, [d, D, k, m, k2, r, seed, round(budget, 2), _PATIENCE],
                     timeout=budget + 15.0)
    n, edges = lib.parse_graph_text(text)
    return (n, edges) if n > 0 else None


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total
    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Phase 1: C lift search with a bandit over base sizes k. The order goal is ratcheted:
    # a success jumps the goal above the new graph, failures ease it back toward the best.
    # While the best graph is small, 25% of the time is kept for the C grow phase; once the
    # lifts are large, the grow phase is skipped and the lift search keeps the full budget.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    goal = float(best_n) * 1.05

    def lift_end():
        return t0 + (0.75 if best_n <= _GROW_MAX_N else 1.0) * total

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    broken = False
    while not broken:
        left = lift_end() - time.monotonic()
        if left < 0.5:
            break
        k = pick_k()
        target = max(2, int(goal // (2 * k)) + rng.randrange(0, 3))
        g = _sample_group(target, rng)
        if g is None:
            goal = max(float(best_n) * 1.02, goal * 0.99)
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best_n:
            goal = max(goal, best_n * 1.02)
            continue
        trials[k] += 1
        try:
            res = _lift_c(d, D, k, m, k2, r, rng.randrange(1 << 31), min(left, _LIFT_SLICE))
        except Exception:
            res = None
            broken = True
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])
            goal = max(goal, res[0] * 1.04)
        else:
            goal = max(float(best_n) * 1.02, goal * 0.99)

    # Phase 2: C grow-by-two from the best graph, using the remaining time (small graphs only).
    remaining = final - time.monotonic() - 2.0
    if best_n <= _GROW_MAX_N and remaining > 2.0 and best_n > 2 * d:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 10)
            out = lib.parse_graph_text(text)
            consider(out[0], out[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
