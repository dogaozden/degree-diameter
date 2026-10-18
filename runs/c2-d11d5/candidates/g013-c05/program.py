"""Combined program: a C bi-Cayley voltage-lift annealer over semidirect groups Z_m x| Z_k2,
followed by a C grow-by-two engine that inserts vertices into the best graph found.

New in this version: the lift search runs entirely in C. Each group is checked with a bitmask
reach propagation that is exact for left-regular lifts, so the annealer does thousands of
evaluations per second instead of a few hundred. Every returned graph is checked with lib.is_valid,
and K_{d,d} (or a known construction) is the fallback.
"""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: bi-Cayley lift annealer over Z_m x| Z_k2 (new in this version).
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h, with G = m*k2.
# Layer l joins A_i to B_{lay[l][i]} with voltage S[l][i]: A_{i,g} ~ B_{p, g*s}.
# Each layer is a permutation of blocks, so every vertex gets degree d.
# Left multiplication by the group is an automorphism, so the diameter is at most D iff
# every block representative reaches every vertex within D steps. This is checked with
# bitmask propagation over the 2k representatives.
# ----------------------------------------------------------------------------

LIFT_C = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Usage: prog d D k m k2 r seed time_limit
 * Prints the first lift with zero bad pairs as "n m" + edges, or "0 0" on timeout. */

#define MAXD 24
#define MAXK 8
#define PEN 50L
#define PATIENCE 3000L

static int d, D, k, m, k2, r, G, N;
static int powr[256];
static int *nbr;
static int lay[MAXD][MAXK];
static int S[MAXD][MAXK];
static uint32_t *bufA, *bufB, *lastr;
static uint32_t fullmask;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

/* Semidirect product: (a,b)*(c,e) = (a + r^b c, b + e), element coded a*k2 + b. */
static int gmul(int x, int y) {
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long long t = (long long)a + (long long)powr[b] * c;
    return (int)(t % m) * k2 + (b + e) % k2;
}

/* Inverse of (a,b) is (-r^(-b) a, -b), and r^(-b) = r^(k2-b). */
static int ginv(int x) {
    int a = x / k2, b = x % k2;
    int nb = (k2 - b) % k2;
    long long t = (-((long long)powr[nb] * a)) % m;
    if (t < 0) t += m;
    return (int)t * k2 + nb;
}

static void set_dart(int l, int i) {
    int j = lay[l][i], s = S[l][i], si = ginv(s);
    int *nb = nbr + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        nb[i * G + g] = (k + j) * G + gmul(g, s);
        nb[(k + j) * G + g] = i * G + gmul(g, si);
    }
}

static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (lay[l1][i] == lay[l2][i] && S[l1][i] == S[l2][i]) c++;
    return c;
}

/* Sum over vertices of unreached representatives after D propagation rounds. */
static long eval_cost(void) {
    int nb2 = 2 * k;
    memset(bufA, 0, sizeof(uint32_t) * (size_t)N);
    for (int b = 0; b < nb2; b++) bufA[(size_t)b * G] = 1u << b;
    uint32_t *cur = bufA, *nxt = bufB;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[(size_t)l * N + v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint32_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    long cost = 0;
    for (int v = 0; v < N; v++) cost += nb2 - __builtin_popcount(cur[v]);
    lastr = cur;
    return cost;
}

static long total_cost(void) { return eval_cost() + PEN * dupcount(); }

static void randomize(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) lay[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        for (int i = 0; i < k; i++) S[l][i] = rndint(G);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) set_dart(l, i);
}

static int anneal(double deadline) {
    randomize();
    long cost = total_cost();
    long bestc = cost, last = 0, t = 0;
    double c0 = (double)(cost > 1 ? cost : 1);
    while (1) {
        if (cost == 0) return 1;
        if ((t & 31) == 0 && now() > deadline) return 0;
        t++;
        if (t - last > PATIENCE) {
            randomize();
            cost = total_cost();
            bestc = cost;
            last = t;
            c0 = (double)(cost > 1 ? cost : 1);
            continue;
        }
        double frac = (double)(PATIENCE - (t - last)) / (double)PATIENCE;
        double temp = 0.3 + 0.01 * c0 * frac;

        if (k >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int tmp = lay[l][i1];
            lay[l][i1] = lay[l][i2];
            lay[l][i2] = tmp;
            set_dart(l, i1);
            set_dart(l, i2);
            long c2 = total_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                tmp = lay[l][i1];
                lay[l][i1] = lay[l][i2];
                lay[l][i2] = tmp;
                set_dart(l, i1);
                set_dart(l, i2);
            }
            continue;
        }

        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            /* Guided move: pick a vertex that is not yet fully reached and touch its dart. */
            for (int tries = 0; tries < 20 && l < 0; tries++) {
                int v = rndint(N);
                if (lastr[v] != fullmask) {
                    int blk = v / G;
                    l = rndint(d);
                    if (blk < k) {
                        i = blk;
                    } else {
                        for (int q = 0; q < k; q++)
                            if (lay[l][q] == blk - k) i = q;
                    }
                }
            }
        }
        if (l < 0) {
            l = rndint(d);
            i = rndint(k);
        }
        int old = S[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        S[l][i] = nw;
        set_dart(l, i);
        long c2 = total_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < bestc) { bestc = cost; last = t; }
        } else {
            S[l][i] = old;
            set_dart(l, i);
        }
    }
    return 0;
}

static void print_graph(void) {
    long cnt = (long)k * G * d;
    printf("%d %ld\n", N, cnt);
    for (int v = 0; v < k * G; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nbr[(size_t)l * N + v]);
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: %s d D k m k2 r seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    k = atoi(argv[3]);
    m = atoi(argv[4]);
    k2 = atoi(argv[5]);
    r = atoi(argv[6]);
    long seed = atol(argv[7]);
    double limit = atof(argv[8]);
    double deadline = now() + limit * 0.92 - 0.15;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || k < 1 || k > MAXK || m < 2 || k2 < 1 || k2 > 255 || D < 1) {
        printf("0 0\n");
        return 0;
    }
    r %= m;
    if (r < 0) r += m;
    powr[0] = 1 % m;
    for (int t = 1; t < k2; t++) powr[t] = (int)((long long)powr[t - 1] * r % m);
    if ((long long)powr[k2 - 1] * r % m != 1 % m) {
        printf("0 0\n");
        return 0;
    }
    G = m * k2;
    N = 2 * k * G;
    if (N > 2000000) {
        printf("0 0\n");
        return 0;
    }
    nbr = malloc(sizeof(int) * (size_t)d * N);
    bufA = malloc(sizeof(uint32_t) * (size_t)N);
    bufB = malloc(sizeof(uint32_t) * (size_t)N);
    if (!nbr || !bufA || !bufB) {
        printf("0 0\n");
        return 0;
    }
    fullmask = (1u << (2 * k)) - 1;
    lastr = bufA;

    while (now() < deadline) {
        if (anneal(deadline)) {
            print_graph();
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}
'''


# ----------------------------------------------------------------------------
# C engine 2: grow-by-two search core (unchanged from the parent).
# ----------------------------------------------------------------------------

GROW_C = r'''
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
#define CANDS 6

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

static Graph gbest, gwork, gtry;
static int used[MAXN];
static int stamp = 0;

static void make_candidate(const Graph *best, Graph *w) {
    int n = best->n;
    copy_graph(w, best);
    int x = n, y = n + 1;
    w->n = n + 2;
    w->deg[x] = w->deg[y] = 0;
    w->side[x] = 0;
    w->side[y] = 1;
    add_edge(w, x, y);
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (w->side[a] != 0 || used[a] == stamp || w->deg[a] == 0) continue;
        int b = w->adj[a][rndint(w->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(w, a, b);
        add_edge(w, x, b);
        add_edge(w, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
}

static void choose_candidate(const Graph *best, Graph *work) {
    long bestbad = -1;
    for (int c = 0; c < CANDS; c++) {
        make_candidate(best, &gtry);
        long b = bad_pairs(&gtry);
        if (bestbad < 0 || b < bestbad) {
            bestbad = b;
            copy_graph(work, &gtry);
        }
        if (b == 0) break;
    }
}

static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    choose_candidate(best, work);
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
    double t_end = now() + limit * 0.9 - 0.2;
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
# Group sampling and the C lift driver.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4)


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


def _c_lift(d, D, k, m, k2, r, seed, budget):
    """Run the C lift annealer for one group. Returns (n, edges) or None."""
    text = lib.run_c(LIFT_C, [d, D, k, m, k2, r, seed, round(budget, 2)],
                     timeout=budget + 15)
    n, edges = lib.parse_graph_text(text)
    if n <= 0 or not edges:
        return None
    return n, edges


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
            return True
        return False

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

    # Phase 1: C bi-Cayley lift annealing over semidirect groups, with a bandit over block counts k.
    # The order goal is ratcheted by successes and eased back on failures.
    if d >= 2 and D >= 2:
        lift_deadline = t0 + 0.75 * total
        lift_total = max(1.0, lift_deadline - time.monotonic())
        per_trial = max(1.0, min(2.5, lift_total / 6.0))
        trials = {k: 0 for k in _KS}
        wins = {k: 0 for k in _KS}
        goal = float(best_n) * 1.05
        ntrial = 0
        guard = 0

        def pick_k():
            if rng.random() < 0.2:
                return rng.choice(_KS)
            return max(_KS, key=lambda kk: (wins[kk] + 1) / (trials[kk] + 2) + 0.02 * rng.random())

        while True:
            guard += 1
            left = lift_deadline - time.monotonic()
            if left < 0.8 or guard > 20000:
                break
            k = pick_k()
            target = max(2, int(goal // (2 * k)) + rng.randrange(0, 3))
            g = _sample_group(target, rng)
            if g is None:
                goal = max(float(best_n) * 1.02, goal * 0.99)
                continue
            m, k2, r = g
            G = m * k2
            if 2 * k * G <= best_n:
                goal = max(goal, best_n * 1.02)
                continue
            ntrial += 1
            trials[k] += 1
            budget = min(per_trial, left)
            try:
                res = _c_lift(d, D, k, m, k2, r,
                              (seed * 1000003 + ntrial) % 2147483647, budget)
            except Exception:
                res = None
            if res is not None and consider(res[0], res[1]):
                wins[k] += 1
                goal = max(goal, res[0] * 1.04)
            else:
                goal = max(float(best_n) * 1.02, goal * 0.99)

    # Phase 2: C grow-by-two from the best graph, using the remaining time.
    remaining = final - time.monotonic() - 2.0
    if remaining > 2.0 and best_n > 2 * d:
        try:
            text = lib.run_c(GROW_C, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 10)
            out = lib.parse_graph_text(text)
            consider(out[0], out[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
