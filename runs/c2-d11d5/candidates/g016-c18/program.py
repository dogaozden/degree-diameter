"""Bi-Cayley lift search in C, then grow-by-two, with a Python fallback.

New in this version: the voltage-lift annealer runs in C (lift_search). Each candidate is scored
with a representative-only reach bitmask (every vertex's ball covers all 2k block representatives),
which is exact for these lifts and runs roughly 10-100x faster than the numpy version. A bandit over
the base size k and a ratcheted order goal are kept. The C grow-by-two phase is reused when the
best graph is small enough.

Every returned graph is checked with lib.is_valid. K_{d,d} (or an exact construction) is the fallback.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


C_SOURCE = r'''
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
#define MAXK 4
#define MAXK2 64
#define GROW_MAX 1500
#define PEN 1000L

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

static Graph gbest, gwork, glift;
static int used[MAXN];
static int stamp = 0;

/* ---------------- semidirect groups Z_m x| Z_k2 ---------------- */
static const int K2_CHOICES[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
static int gm, gk2, gG;
static long gpw[MAXK2];
static int ginv[MAXN];

static long lgcd(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static long lpowmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Element x = a*k2 + b means (a, b). Product (a,b)*(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / gk2, b = x % gk2, c = y / gk2, e = y % gk2;
    long t = ((long)a + gpw[b] * (long)c) % gm;
    return (int)(t * gk2 + (b + e) % gk2);
}

static int ginvel(int x) {
    int a = x / gk2, b = x % gk2;
    int nb = (gk2 - b) % gk2;
    long t = (-(gpw[nb] * (long)a)) % gm;
    if (t < 0) t += gm;
    return (int)(t * gk2 + nb);
}

static void set_group(int m, int k2, int r) {
    gm = m;
    gk2 = k2;
    gG = m * k2;
    gpw[0] = 1 % m;
    for (int b = 1; b < k2; b++) gpw[b] = gpw[b - 1] * r % m;
    for (int x = 0; x < gG; x++) ginv[x] = ginvel(x);
}

static int sample_group(int target, int *om, int *ok2, int *orr) {
    for (int att = 0; att < 200; att++) {
        int k2 = K2_CHOICES[rndint(20)];
        long mm = ((long)target + k2 - 1) / k2;
        if (mm < 2) mm = 2;
        long r = -1;
        if (k2 == 1) {
            r = 1 % mm;
        } else if (k2 == 2 && rnd01() < 0.3) {
            long c = mm - 1;
            if (lgcd(c, mm) == 1 && (c * c) % mm == 1 % mm) r = c;
        } else {
            for (int t = 0; t < 60; t++) {
                long c = (mm > 2) ? 2 + rndint((int)(mm - 2)) : 1;
                if (lgcd(c, mm) == 1 && lpowmod(c, k2, mm) == 1 % mm) { r = c; break; }
            }
        }
        if (r >= 0) {
            *om = (int)mm;
            *ok2 = k2;
            *orr = (int)r;
            return 1;
        }
    }
    return 0;
}

/* ---------------- bi-Cayley lift state ---------------- */
/* Vertices: A_{i,g} = i*G + g (i < k), B_{p,h} = (k+p)*G + h.
 * Layer l sends A_{i,g} to B_{layers[l][i], g*s} with s = lS[l][i].
 * Every layer is a perfect matching, so the graph is d-regular when there are no duplicates. */
static int lk, lN;
static int layers[MAXD][MAXK];
static int lS[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static uint32_t reach_a[MAXN], reach_b[MAXN], reach_c[MAXN], reach_s[MAXN];
static int trials_k[MAXK + 1], wins_k[MAXK + 1];
static double goal;
static long lift_iters = 20000, lift_patience = 3000;

static void swap_int(int *a, int *b) {
    int t = *a;
    *a = *b;
    *b = t;
}

static void set_dart(int l, int i) {
    int G = gG, p = layers[l][i], s = lS[l][i], si = ginv[s];
    int A = i * G, B = (lk + p) * G;
    for (int g = 0; g < G; g++) {
        nbr[l][A + g] = B + gmul(g, s);
        nbr[l][B + g] = A + gmul(g, si);
    }
}

/* reach_a[v] bit b is set when block representative b is within distance D of v.
 * Representatives suffice because left multiplication by the group is an automorphism. */
static void compute_reach(void) {
    int N = lN, G = gG, k = lk;
    uint32_t *cur = reach_b, *nxt = reach_c;
    memset(cur, 0, sizeof(uint32_t) * (size_t)N);
    for (int b = 0; b < 2 * k; b++) cur[(size_t)b * G] = 1u << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint32_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    memcpy(reach_a, cur, sizeof(uint32_t) * (size_t)N);
}

static long missing_count(void) {
    long miss = 0;
    int full_bits = 2 * lk;
    for (int v = 0; v < lN; v++) miss += full_bits - __builtin_popcount(reach_a[v]);
    return miss;
}

static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < lk; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (layers[l1][i] == layers[l2][i] && lS[l1][i] == lS[l2][i]) c++;
    return c;
}

static long cost_now(void) { return missing_count() + PEN * dup_count(); }

/* Simulated annealing over layer permutations and voltages. Returns 1 when the lift is valid;
 * the state in layers/lS/nbr is then the valid lift. */
static int lift_search(long iters, long patience, double deadline) {
    int k = lk, G = gG, N = lN;
    uint32_t full = (1u << (2 * k)) - 1;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) layers[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            swap_int(&layers[l][i], &layers[l][j]);
        }
        for (int i = 0; i < k; i++) lS[l][i] = rndint(G);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) set_dart(l, i);
    compute_reach();
    long cost = cost_now();
    long best_cost = cost;
    double c0 = cost > 1 ? (double)cost : 1.0;
    long last = 0;

    for (long t = 0; t < iters; t++) {
        if (cost == 0) break;
        if (t - last > patience) break;
        if ((t & 63) == 0 && now() > deadline) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;
        memcpy(reach_s, reach_a, sizeof(uint32_t) * (size_t)N);

        if (k >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            swap_int(&layers[l][i1], &layers[l][i2]);
            set_dart(l, i1);
            set_dart(l, i2);
            compute_reach();
            long c2 = cost_now();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < best_cost) { best_cost = cost; last = t; }
            } else {
                swap_int(&layers[l][i1], &layers[l][i2]);
                set_dart(l, i1);
                set_dart(l, i2);
                memcpy(reach_a, reach_s, sizeof(uint32_t) * (size_t)N);
            }
            continue;
        }

        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            int u = -1;
            for (int tries = 0; tries < 30; tries++) {
                int v = rndint(N);
                if (reach_a[v] != full) { u = v; break; }
            }
            if (u >= 0) {
                int block = u / G;
                int ll = rndint(d);
                if (block < k) {
                    l = ll;
                    i = block;
                } else {
                    for (int j = 0; j < k; j++)
                        if (layers[ll][j] == block - k) { l = ll; i = j; break; }
                }
            }
        }
        if (l < 0) {
            l = rndint(d);
            i = rndint(k);
        }
        int old = lS[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        lS[l][i] = nw;
        set_dart(l, i);
        compute_reach();
        long c2 = cost_now();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < best_cost) { best_cost = cost; last = t; }
        } else {
            lS[l][i] = old;
            set_dart(l, i);
            memcpy(reach_a, reach_s, sizeof(uint32_t) * (size_t)N);
        }
    }
    return cost == 0;
}

static int build_lift_graph(Graph *g) {
    int N = lN, k = lk, G = gG;
    g->n = N;
    for (int v = 0; v < N; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= k * G ? 1 : 0);
    }
    for (int u = 0; u < k * G; u++)
        for (int l = 0; l < d; l++) add_edge(g, u, nbr[l][u]);
    return is_valid(g);
}

static int pick_k(void) {
    if (rnd01() < 0.2) return 1 + rndint(MAXK);
    int bk = 1;
    double bv = -1.0;
    for (int k = 1; k <= MAXK; k++) {
        double v = (wins_k[k] + 1.0) / (trials_k[k] + 2.0) + 0.02 * rnd01();
        if (v > bv) { bv = v; bk = k; }
    }
    return bk;
}

/* Ratcheted search: a success moves the order goal above the new graph, failures ease it back. */
static void lift_loop(double until) {
    long mb = moore_bound();
    while (now() < until) {
        if (goal > (double)mb) goal = (double)mb;
        int k = pick_k();
        int target = (int)(goal / (2.0 * k)) + rndint(3);
        if (target < 2) target = 2;
        int m, k2, r;
        if (!sample_group(target, &m, &k2, &r)) {
            goal = fmax((double)gbest.n * 1.02, goal * 0.99);
            continue;
        }
        long Nc = 2L * k * m * k2;
        if (Nc <= gbest.n) {
            goal = fmax(goal, gbest.n * 1.02);
            continue;
        }
        if (Nc > MAXN || Nc > mb) {
            goal = fmax((double)gbest.n * 1.02, goal * 0.99);
            continue;
        }
        set_group(m, k2, r);
        lk = k;
        lN = (int)Nc;
        trials_k[k]++;
        int ok = lift_search(lift_iters, lift_patience, until);
        if (ok) {
            wins_k[k]++;
            if (build_lift_graph(&glift) && lN > gbest.n) copy_graph(&gbest, &glift);
            goal = fmax(goal, lN * 1.04);
        } else {
            goal = fmax((double)gbest.n * 1.02, goal * 0.99);
        }
    }
}

/* ---------------- grow-by-two (inherited) ---------------- */
static double t_end;

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
    t_end = t0 + limit * 0.97 - 0.3;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    read_start(&gbest);
    goal = gbest.n > 0 ? gbest.n * 1.05 : 2.0 * d + 2.0;

    double span = t_end - now();
    if (span < 0.0) span = 0.0;
    lift_loop(now() + 0.75 * span);
    if (gbest.n > 0 && gbest.n <= GROW_MAX) grow_search(t_end);
    else lift_loop(t_end);

    if (gbest.n == 0 || !is_valid(&gbest)) { printf("0 0\n"); return 0; }
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
# Python fallback for the bi-Cayley search (used only if the C engine cannot run).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
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


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) with Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(k, N, reach):
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing over one bi-Cayley lift. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))
    best_cost = cost
    last_improve = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last_improve > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last_improve = cost, t
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
            if cost < best_cost:
                best_cost, last_improve = cost, t
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


def _py_lift(d, D, rng, best_n, final, consider):
    """Python fallback: bi-Cayley lifts with a ratcheted order goal, until the deadline."""
    goal = float(best_n) * 1.05
    while time.monotonic() < final:
        k = rng.choice(_KS)
        target = max(2, int(goal // (2 * k)) + rng.randrange(0, 3))
        g = _sample_group(target, rng)
        if g is None or 2 * k * g[0] * g[1] > 1500:
            goal = max(float(best_n) * 1.02, goal * 0.99)
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            goal = max(goal, best_n * 1.02)
            continue
        res = _search(d, D, k, G, Ts, Invs, rng, final, 4000, 1200)
        if res is not None and consider(res[0], res[1]):
            best_n = res[0]
            goal = max(goal, res[0] * 1.04)
        else:
            goal = max(float(best_n) * 1.02, goal * 0.99)


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.9 * time_limit - 1.0)
    final = t0 + total
    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
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

    # Main search: C lift annealer plus grow-by-two, starting from the best valid graph.
    if d >= 3 and D >= 2:
        remaining = final - time.monotonic()
        if remaining > 2.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                                 stdin_graph=best, timeout=remaining + 4.0)
                consider(*lib.parse_graph_text(text))
            except Exception:
                _py_lift(d, D, rng, best[0], final, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
