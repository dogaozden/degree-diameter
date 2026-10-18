"""Bi-Cayley lift search moved into C, plus a grow-by-two phase.

Python builds the exact constructions (projective planes, Araujo-Pardo-Lopez, GQ(W(q)))
and passes the best one to the C engine. C samples semidirect groups Z_m x| Z_k2, anneals
voltage lifts with a block-transitive reachability cost (one bitmask per vertex, 2k bits),
and then grows the best graph by two vertices if it is still small. Every returned graph
is checked with lib.is_valid, with K_{d,d} as the fallback.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Search core: bi-Cayley lift annealing over semidirect products + grow-by-two.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid bipartite start), or "0 0".
 * stdout: "n m" + edges of the best valid graph found.
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
#define MAXK 4
#define PEN 1000L
#define GROW_MAX_N 1500

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
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

/* ---------------- bi-Cayley lift search over Z_m x| Z_k2 ----------------
 * Vertices: A_{i,x} = i*G + x (i < LK), B_{p,y} = (LK+p)*G + y.
 * Layer l pairs A-block i with B-block LLay[l][i] through voltage LSv[l][i]:
 *   A_{i,x} ~ B_{p, x*s}.   Each layer is a permutation, so the graph is d-regular.
 * Reachability is checked only from block representatives. Left multiplication by G
 * is an automorphism acting regularly on each block, so this is exact for all pairs.
 */
static int LK = 1, LG = 2, Lm = 2, Lk2 = 1, Lr = 1;
static int Lpw[64];
static int LLay[MAXD][MAXK], LLinv[MAXD][MAXK], LSv[MAXD][MAXK];
static int32_t Lnbr[MAXD][MAXN];
static uint8_t Lrch[MAXN], Lnew[MAXN], Lacc[MAXN];

static int gmul(int x, int y) {
    int a = x / Lk2, b = x % Lk2, c = y / Lk2, e = y % Lk2;
    long t = ((long)a + (long)Lpw[b] * c) % Lm;
    return (int)(t * Lk2 + (b + e) % Lk2);
}

static int ginv(int x) {
    int a = x / Lk2, b = x % Lk2;
    int nb = (Lk2 - b) % Lk2;
    long t = (Lm - ((long)Lpw[nb] * a) % Lm) % Lm;
    return (int)(t * Lk2 + nb);
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod_i(long b, int e, int m) {
    long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static const int K2C[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

/* Sample Z_m x| Z_k2 with m*k2 >= target; sets Lm, Lk2, Lr, LG, Lpw. Returns 1 on success. */
static int sample_group(int target) {
    for (int att = 0; att < 200; att++) {
        int k2 = K2C[rndint(20)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = 1 % m;
        if (k2 > 1) {
            int found = 0;
            for (int t = 0; t < 80 && !found; t++) {
                int c = rndint(m);
                if (gcd_i(c, m) == 1 && powmod_i(c, k2, m) == 1 % m) { r = c; found = 1; }
            }
            if (!found) continue;
        }
        Lm = m;
        Lk2 = k2;
        Lr = r;
        LG = m * k2;
        Lpw[0] = 1 % m;
        for (int b = 1; b < k2; b++) Lpw[b] = (int)((long)Lpw[b - 1] * r % m);
        return 1;
    }
    return 0;
}

static void set_dart(int l, int i) {
    int p = LLay[l][i], s = LSv[l][i];
    int is = ginv(s);
    int ba = i * LG, bb = (LK + p) * LG;
    for (int x = 0; x < LG; x++) {
        Lnbr[l][ba + x] = bb + gmul(x, s);
        Lnbr[l][bb + x] = ba + gmul(x, is);
    }
}

static void swap_rows(int l, int i1, int i2) {
    int tmp = LLay[l][i1];
    LLay[l][i1] = LLay[l][i2];
    LLay[l][i2] = tmp;
    LLinv[l][LLay[l][i1]] = i1;
    LLinv[l][LLay[l][i2]] = i2;
    set_dart(l, i1);
    set_dart(l, i2);
}

static void lift_init(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < LK; i++) LLay[l][i] = i;
        for (int i = LK - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = LLay[l][i];
            LLay[l][i] = LLay[l][j];
            LLay[l][j] = tmp;
        }
        for (int i = 0; i < LK; i++) LLinv[l][LLay[l][i]] = i;
        for (int i = 0; i < LK; i++) LSv[l][i] = rndint(LG);
        for (int i = 0; i < LK; i++) set_dart(l, i);
    }
}

/* Duplicate darts: same A-block, same B-block and same voltage in two layers. */
static long lift_dups(void) {
    long c = 0;
    for (int l1 = 0; l1 < d; l1++)
        for (int l2 = l1 + 1; l2 < d; l2++)
            for (int i = 0; i < LK; i++)
                if (LLay[l1][i] == LLay[l2][i] && LSv[l1][i] == LSv[l2][i]) c++;
    return c;
}

/* Number of (vertex, representative) pairs farther than D apart. Writes Lrch. */
static long lift_cost(void) {
    int N = 2 * LK * LG;
    int nb2 = 2 * LK;
    memset(Lrch, 0, (size_t)N);
    for (int b = 0; b < nb2; b++) Lrch[b * LG] = (uint8_t)(1u << b);
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint8_t x = Lrch[v];
            for (int l = 0; l < d; l++) x |= Lrch[Lnbr[l][v]];
            Lnew[v] = x;
            changed |= (x != Lrch[v]);
        }
        memcpy(Lrch, Lnew, (size_t)N);
        if (!changed) break;
    }
    long unre = 0;
    for (int v = 0; v < N; v++) unre += nb2 - __builtin_popcount(Lrch[v]);
    return unre;
}

static int lift_search(long iters, long patience, double until) {
    int N = 2 * LK * LG;
    lift_init();
    uint8_t full = (uint8_t)((1u << (2 * LK)) - 1);
    long cost = lift_cost() + PEN * lift_dups();
    memcpy(Lacc, Lrch, (size_t)N);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best = cost, last = 0;
    for (long t = 0; t < iters; t++) {
        if (cost == 0) return 1;
        if (t - last > patience) break;
        if ((t & 31) == 0 && now() > until) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (LK >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(LK), i2 = rndint(LK - 1);
            if (i2 >= i1) i2++;
            swap_rows(l, i1, i2);
            long c2 = lift_cost() + PEN * lift_dups();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(Lacc, Lrch, (size_t)N);
                if (cost < best) { best = cost; last = t; }
            } else {
                swap_rows(l, i1, i2);
            }
            continue;
        }

        int v = -1;
        if (rnd01() < 0.4) {
            for (int tr = 0; tr < 30; tr++) {
                int w = rndint(N);
                if (Lacc[w] != full) { v = w; break; }
            }
        }
        int l, i;
        if (v >= 0) {
            int blk = v / LG;
            l = rndint(d);
            i = (blk < LK) ? blk : LLinv[l][blk - LK];
        } else {
            l = rndint(d);
            i = rndint(LK);
        }
        int old = LSv[l][i];
        int nw = rndint(LG);
        if (nw == old) continue;
        LSv[l][i] = nw;
        set_dart(l, i);
        long c2 = lift_cost() + PEN * lift_dups();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(Lacc, Lrch, (size_t)N);
            if (cost < best) { best = cost; last = t; }
        } else {
            LSv[l][i] = old;
            set_dart(l, i);
        }
    }
    return cost == 0;
}

static void lift_to_graph(Graph *g) {
    int N = 2 * LK * LG;
    g->n = N;
    for (int v = 0; v < N; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v < LK * LG ? 0 : 1);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < LK; i++) {
            int p = LLay[l][i], s = LSv[l][i];
            for (int x = 0; x < LG; x++)
                add_edge(g, i * LG + x, (LK + p) * LG + gmul(x, s));
        }
}

/* Ratcheted bandit over base sizes k; each success raises the order goal. */
static void lift_phase(double until) {
    static long trials[MAXK + 1], wins[MAXK + 1];
    long cap = moore_bound();
    if (cap > MAXN) cap = MAXN;
    if (cap < 4) return;
    double goal = (double)gbest.n * 1.05;
    if (goal < 2.0 * d) goal = 2.0 * d;

    while (now() < until) {
        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bs = -1.0;
            k = 1;
            for (int c = 1; c <= MAXK; c++) {
                double sc = (wins[c] + 1.0) / (trials[c] + 2.0) + 0.02 * rnd01();
                if (sc > bs) { bs = sc; k = c; }
            }
        }
        long kcap = cap / (2L * k);
        int target = (int)(goal / (2.0 * k)) + rndint(3);
        if (target < 2) target = 2;
        if (target > kcap) target = (int)kcap;
        if (target < 2) { goal = fmax((double)gbest.n * 1.02, goal * 0.99); continue; }

        if (!sample_group(target)) {
            goal = fmax((double)gbest.n * 1.02, goal * 0.99);
            continue;
        }
        long N = 2L * k * LG;
        if (N > cap) { goal = fmax((double)gbest.n * 1.02, goal * 0.99); continue; }
        if (N <= gbest.n) { goal = fmax(goal, (double)gbest.n * 1.02); continue; }

        LK = k;
        trials[k]++;
        int ok = lift_search(12000, 3000, until);
        if (ok) {
            lift_to_graph(&glift);
            if (is_valid(&glift) && glift.n > gbest.n) {
                copy_graph(&gbest, &glift);
                wins[k]++;
            }
            goal = fmax(goal, (double)N * 1.04);
        } else {
            goal = fmax((double)gbest.n * 1.02, goal * 0.99);
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
    t_end = t0 + limit * 0.93 - 0.3;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    gbest.n = 0;
    read_start(&gbest);

    int small = gbest.n > 0 && gbest.n <= GROW_MAX_N;
    double rem = t_end - now();
    lift_phase(small ? now() + 0.6 * rem : t_end);

    if (gbest.n > 0 && gbest.n <= GROW_MAX_N && now() < t_end) grow_search(t_end);

    if (gbest.n <= 0 || !is_valid(&gbest)) { printf("0 0\n"); return 0; }
    print_graph(&gbest);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions (Python).
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
    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # C engine: bi-Cayley lift annealing over semidirect products, then grow-by-two
    # on small graphs. Budget leaves room for compilation, parsing and the final check.
    budget = 0.9 * time_limit - 3.0
    if budget > 3.0 and d <= 32:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 15.0)
            consider(*lib.parse_graph_text(text))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
