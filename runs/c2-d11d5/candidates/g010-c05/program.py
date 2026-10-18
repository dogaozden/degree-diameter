"""Bi-Cayley voltage-lift search in C, then a C grow-by-two pass.

New in this version: the whole lift search runs inside the C engine. The lift is
built over the semidirect product Z_m x| Z_k2 with layer permutations and voltages.
Left multiplication by a group element is an automorphism of the lift, so the
diameter check needs only BFS-style bitmask propagation from the 2k block
representatives (uint16 masks). Permutations and voltages are annealed with a
time-based temperature and a defect-directed move, and the target order ratchets
up after each success. The best lift is then grown by two vertices at a time.

Python builds the exact constructions (projective planes, Araujo-Pardo-Lopez,
generalized quadrangles), makes a single lib.run_c call, and checks every result
with lib.is_valid. K_{d,d} is the fallback.
"""
import itertools
import time

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
#define CANDS 6
#define KMAX 6
#define PEN 1000L
#define SLICE 6.0
#define PATIENCE 3000L

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
static double t_end;
static Graph gbest, gwork, gtry, glift;
static int used[MAXN];
static int stamp = 0;

/* Lift state: vertex (block, g) has index block*G + g, blocks 0..k-1 are side A,
 * blocks k..2k-1 are side B. Layer l joins A-block i to B-block lay[l][i] with
 * voltage vol[l][i]: A_{i,g} ~ B_{j,g*s}. */
static int gk, gG, gm, gk2, gr;
static long gpw[64];
static int lay[MAXD][KMAX];
static int lin[MAXD][KMAX];
static int vol[MAXD][KMAX];
static int nbr[MAXD][MAXN];
static uint16_t LA[MAXN], LB[MAXN];
static uint16_t *gfin = LA;

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

/* ------------------------------------------------------------------ groups */

static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Choose Z_m x| Z_k2 with order m*k2 >= Gt (small slack). r^k2 = 1 mod m, gcd(r,m)=1.
 * Falls back to the direct product (r = 1) when no random r is found. */
static int sample_group(long Gt) {
    static const int K2S[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 24, 30};
    int nk = (int)(sizeof(K2S) / sizeof(K2S[0]));
    int k2 = K2S[rndint(nk)];
    long m = (Gt + k2 - 1) / k2 + rndint(3);
    if (m < 2) m = 2;
    long r = 1 % m;
    if (k2 > 1 && m >= 3 && rnd01() < 0.7) {
        for (int c = 0; c < 60; c++) {
            long cc = 2 + rndint((int)(m - 2));
            if (gcd_l(cc, m) == 1 && powmod_l(cc, k2, m) == 1 % m) { r = cc; break; }
        }
    }
    gm = (int)m;
    gk2 = k2;
    gr = (int)r;
    gG = (int)(m * k2);
    gpw[0] = 1 % m;
    for (int b = 1; b < k2; b++) gpw[b] = gpw[b - 1] * r % m;
    return 1;
}

static int gmul(int x, int y) {
    int a = x / gk2, b = x % gk2, c = y / gk2, e = y % gk2;
    int t = (int)((gpw[b] * c + a) % gm);
    return t * gk2 + (b + e) % gk2;
}

static int gpinv(int x) {
    int a = x / gk2, b = x % gk2;
    int nb = (gk2 - b) % gk2;
    long t = gpw[nb] * a % gm;
    int na = (int)((gm - t) % gm);
    return na * gk2 + nb;
}

/* ------------------------------------------------------------- lift state */

static void set_dart(int l, int i) {
    int G = gG, k = gk, j = lay[l][i], s = vol[l][i];
    int si = gpinv(s);
    int ai = i * G, bj = (k + j) * G;
    for (int g = 0; g < G; g++) {
        nbr[l][ai + g] = bj + gmul(g, s);
        nbr[l][bj + g] = ai + gmul(g, si);
    }
}

static void swap_blocks(int l, int i1, int i2) {
    int j1 = lay[l][i1], j2 = lay[l][i2];
    lay[l][i1] = j2;
    lay[l][i2] = j1;
    lin[l][j1] = i2;
    lin[l][j2] = i1;
    set_dart(l, i1);
    set_dart(l, i2);
}

static void random_lift(void) {
    int perm[KMAX];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < gk; i++) perm[i] = i;
        for (int i = gk - 1; i > 0; i--) {
            int t = rndint(i + 1);
            int tmp = perm[i];
            perm[i] = perm[t];
            perm[t] = tmp;
        }
        for (int i = 0; i < gk; i++) {
            lay[l][i] = perm[i];
            lin[l][perm[i]] = i;
            vol[l][i] = rndint(gG);
        }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < gk; i++) set_dart(l, i);
}

/* Same block pair and same voltage in two layers gives a repeated edge. */
static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < gk; i++)
        for (int a = 0; a < d; a++)
            for (int b = a + 1; b < d; b++)
                if (lay[a][i] == lay[b][i] && vol[a][i] == vol[b][i]) c++;
    return c;
}

/* Left-translation symmetry: only the 2k block representatives need BFS.
 * Returns the number of (vertex, representative) pairs at distance > D. */
static long reach_cost(void) {
    int K2 = 2 * gk, N = K2 * gG;
    uint16_t *cur = LA, *nxt = LB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < K2; b++) cur[b * gG] = (uint16_t)(1u << b);
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint16_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint16_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    gfin = cur;
    long un = 0;
    for (int v = 0; v < N; v++) un += K2 - __builtin_popcount(cur[v]);
    return un;
}

#define T_BASE 0.3
#define T_SPAN 2.5

/* Simulated annealing over permutations and voltages for the current group.
 * Returns 1 with a valid lift in the arrays, or 0 on timeout/stagnation. */
static int anneal(double until) {
    random_lift();
    int K2 = 2 * gk, N = K2 * gG;
    uint16_t full = (uint16_t)((1u << K2) - 1u);
    long cost = reach_cost() + PEN * dupcount();
    long best = cost, last = 0;
    double t_start = now();
    double dl = t_start + SLICE;
    if (dl > until) dl = until;
    double span = dl - t_start;
    if (span < 1e-3) span = 1e-3;
    double temp = T_BASE + T_SPAN;
    for (long it = 0;; it++) {
        if (cost == 0) return 1;
        if ((it & 31) == 0) {
            double tn = now();
            if (tn > dl) return 0;
            temp = T_BASE + T_SPAN * (1.0 - (tn - t_start) / span);
        }
        if (it - last > PATIENCE) return 0;

        if (gk >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(gk), i2 = rndint(gk - 1);
            if (i2 >= i1) i2++;
            swap_blocks(l, i1, i2);
            long c2 = reach_cost() + PEN * dupcount();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < best) { best = cost; last = it; }
            } else {
                swap_blocks(l, i1, i2);
            }
            continue;
        }

        /* Defect-directed choice: pick an unreached vertex and move a voltage on its block. */
        int v = -1;
        if (rnd01() < 0.4) {
            int cnt = 0;
            for (int u = 0; u < N; u++)
                if (gfin[u] != full) {
                    cnt++;
                    if (rndint(cnt) == 0) v = u;
                }
        }
        int l, i;
        if (v >= 0) {
            int blk = v / gG;
            l = rndint(d);
            i = (blk < gk) ? blk : lin[l][blk - gk];
        } else {
            l = rndint(d);
            i = rndint(gk);
        }
        int old = vol[l][i];
        int nw = rndint(gG);
        if (nw == old) continue;
        vol[l][i] = nw;
        set_dart(l, i);
        long c2 = reach_cost() + PEN * dupcount();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < best) { best = cost; last = it; }
        } else {
            vol[l][i] = old;
            set_dart(l, i);
        }
    }
}

static int store_lift(Graph *g) {
    int A = gk * gG, N = 2 * A;
    if (N > MAXN || d > MAXD) return 0;
    g->n = N;
    for (int v = 0; v < N; v++) {
        g->deg[v] = d;
        g->side[v] = (v < A) ? 0 : 1;
        for (int l = 0; l < d; l++) g->adj[v][l] = nbr[l][v];
    }
    return 1;
}

/* Bandit over base sizes k, with the target order ratcheting up on success. */
static void lift_phase(double until) {
    double trials[KMAX + 1], wins[KMAX + 1];
    for (int c = 0; c <= KMAX; c++) { trials[c] = 0; wins[c] = 0; }
    long goal = (long)gbest.n + 2;
    if (goal < 2L * d + 2) goal = 2L * d + 2;
    while (now() < until) {
        int k = 1;
        if (rnd01() < 0.2) {
            k = 1 + rndint(KMAX);
        } else {
            double bv = -1.0;
            for (int c = 1; c <= KMAX; c++) {
                double v = (wins[c] + 1.0) / (trials[c] + 2.0) + 0.02 * rnd01();
                if (v > bv) { bv = v; k = c; }
            }
        }
        long Gt = (goal + 2L * k - 1) / (2L * k);
        int ok = 0;
        if (sample_group(Gt) && 2L * k * gG <= MAXN) {
            gk = k;
            trials[k] += 1;
            if (anneal(until) && store_lift(&glift) && glift.n > gbest.n && is_valid(&glift)) {
                wins[k] += 1;
                copy_graph(&gbest, &glift);
                goal = (long)(gbest.n * 1.02) + 2;
                ok = 1;
            }
        }
        if (!ok) {
            long bn = gbest.n;
            goal = bn + (goal - bn) / 2 + 1;
        }
    }
}

/* ------------------------------------------------------- grow-by-two phase */

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
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.3;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    read_start(&gbest);
    if (gbest.n == 0) { printf("0 0\n"); return 0; }
    if (d >= 2) lift_phase(t0 + 0.7 * (t_end - t0));
    grow_search(t_end);
    if (!is_valid(&gbest)) { printf("0 0\n"); return 0; }
    print_graph(&gbest);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions.
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
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 2.0)
    final = t0 + total

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

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

    # One C run: bi-Cayley lift annealing followed by grow-by-two from the best graph.
    remaining = final - time.monotonic() - 1.0
    if remaining > 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 10.0)
            consider(*lib.parse_graph_text(text))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
