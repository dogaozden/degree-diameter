"""Bold variant: a C engine that searches bi-Cayley voltage lifts over random semidirect
products Z_m x| Z_k2 (sampled in C), then grows the best graph by two vertices at a time.

Every returned graph is checked with lib.is_valid. K_{d,d} (or the best exact construction)
is the fallback, so every case returns a valid graph.
"""
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
#define MAXK 6

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
static Graph gbest, gwork, gtmp;
static double t_end;
static int used[MAXN];
static int stamp = 0;

/* ---------- utilities ---------- */

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

/* ---------- semidirect group Z_m x| Z_k2, element (a,b) coded a*k2+b ---------- */

static int LK, LG, LK2, LM;
static int LPW[64];
static int layer[MAXD][MAXK];
static int S[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static uint32_t reachv[MAXN], reachn[MAXN];

static int lmul(int x, int y) {
    int a = x / LK2, b = x % LK2, c = y / LK2, e = y % LK2;
    long t = ((long)a + (long)LPW[b] * c) % LM;
    return (int)(t * LK2 + (b + e) % LK2);
}

static int linv(int x) {
    int a = x / LK2, b = x % LK2;
    int nb = (LK2 - b) % LK2;
    long t = ((-(long)LPW[nb] * a) % LM + LM) % LM;
    return (int)(t * LK2 + nb);
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Sample a semidirect product with order >= target; r = 1 gives the direct product. */
static void sample_group(int target) {
    static const int K2S[12] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12};
    int k2 = K2S[rndint(12)];
    int m = (target + k2 - 1) / k2;
    if (m < 2) m = 2;
    m += rndint(3);
    int r = 1;
    if (k2 > 1 && m > 2 && rnd01() < 0.7) {
        int found = -1;
        for (int t = 0; t < 300 && found < 0; t++) {
            int c = 2 + rndint(m - 2);
            if (gcd_i(c, m) == 1 && powmod_l(c, k2, m) == 1) found = c;
        }
        if (found > 0) r = found;
    }
    LK2 = k2;
    LM = m;
    LG = m * k2;
    LPW[0] = 1 % m;
    for (int b = 1; b < k2; b++) LPW[b] = (int)((long)LPW[b - 1] * r % m);
}

/* Block i of A (A-vertex g) joins block j of B with voltage s: A_{i,g} ~ B_{j,g*s}. */
static void set_dart(int l, int i, int j, int s) {
    int G = LG, k = LK;
    int inv_s = linv(s);
    for (int g = 0; g < G; g++) {
        nbr[l][i * G + g] = (k + j) * G + lmul(g, s);
        nbr[l][(k + j) * G + g] = i * G + lmul(g, inv_s);
    }
}

static void swap_layer(int l, int i1, int i2) {
    int t = layer[l][i1];
    layer[l][i1] = layer[l][i2];
    layer[l][i2] = t;
    set_dart(l, i1, layer[l][i1], S[l][i1]);
    set_dart(l, i2, layer[l][i2], S[l][i2]);
}

/* Cost = unreached (representative, vertex) pairs + duplicate-dart penalty.
   Left translations are automorphisms, so checking the 2k block representatives is exact. */
static long reach_cost(void) {
    int G = LG, k = LK, N = 2 * k * G;
    for (int v = 0; v < N; v++) reachv[v] = 0;
    for (int b = 0; b < 2 * k; b++) reachv[b * G] = 1u << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = reachv[v];
            for (int l = 0; l < d; l++) x |= reachv[nbr[l][v]];
            reachn[v] = x;
            if (x != reachv[v]) changed = 1;
        }
        memcpy(reachv, reachn, sizeof(uint32_t) * N);
        if (!changed) break;
    }
    long cost = 2L * k * N;
    for (int v = 0; v < N; v++) cost -= __builtin_popcount(reachv[v]);
    long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (layer[l1][i] == layer[l2][i] && S[l1][i] == S[l2][i]) dup++;
    return cost + 1000 * dup;
}

static int lift_anneal(double deadline, long patience) {
    int k = LK, G = LG, dd = d;
    for (int l = 0; l < dd; l++) {
        for (int i = 0; i < k; i++) layer[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1), t = layer[l][i];
            layer[l][i] = layer[l][j];
            layer[l][j] = t;
        }
        for (int i = 0; i < k; i++) {
            S[l][i] = rndint(G);
            set_dart(l, i, layer[l][i], S[l][i]);
        }
    }
    long cost = reach_cost();
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best = cost, last = 0;
    for (long t = 0; cost > 0; t++) {
        if ((t & 63) == 0 && now() > deadline) break;
        if (t - last > patience) break;
        double temp = 0.5 + 0.01 * c0 * exp(-(double)t / 3000.0);
        int l = rndint(dd);
        if (k >= 2 && rnd01() < 0.25) {
            int i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            swap_layer(l, i1, i2);
            long c2 = reach_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < best) { best = cost; last = t; }
            } else {
                swap_layer(l, i1, i2);
            }
        } else {
            int i = rndint(k);
            int old = S[l][i], nw = rndint(G);
            if (nw == old) continue;
            S[l][i] = nw;
            set_dart(l, i, layer[l][i], nw);
            long c2 = reach_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < best) { best = cost; last = t; }
            } else {
                S[l][i] = old;
                set_dart(l, i, layer[l][i], old);
            }
        }
    }
    return cost == 0;
}

static void export_lift(Graph *g) {
    int N = 2 * LK * LG, half = LK * LG;
    g->n = N;
    for (int v = 0; v < N; v++) {
        g->deg[v] = 0;
        g->side[v] = v < half ? 0 : 1;
    }
    for (int u = 0; u < N; u++)
        for (int l = 0; l < d; l++) {
            int v = nbr[l][u];
            if (!has_edge(g, u, v) && g->deg[u] < MAXD && g->deg[v] < MAXD)
                add_edge(g, u, v);
        }
}

static void lift_phase(double until) {
    double goal = gbest.n * 1.03 + 2.0;
    while (now() < until) {
        int k = 1 + rndint(MAXK);
        int gg = (int)goal;
        int target = (gg + 2 * k - 1) / (2 * k);
        if (2L * k * target > MAXN) {
            k = 1;
            target = (gg + 1) / 2;
            if (2L * target > MAXN) break;
        }
        sample_group(target);
        LK = k;
        int N = 2 * LK * LG;
        if (N <= gbest.n || N > MAXN) {
            goal = gbest.n * 1.03 + 2.0;
            continue;
        }
        double dl = now() + 6.0;
        if (dl > until) dl = until;
        if (lift_anneal(dl, 4000)) {
            export_lift(&gtmp);
            if (gtmp.n > gbest.n && is_valid(&gtmp)) {
                copy_graph(&gbest, &gtmp);
                goal = gbest.n * 1.03 + 2.0;
            } else {
                goal = gbest.n * 1.03 + 2.0;
            }
        } else {
            double floor_goal = gbest.n * 1.005 + 2.0;
            goal = goal * 0.995 > floor_goal ? goal * 0.995 : floor_goal;
        }
    }
}

/* ---------- grow-by-two phase (inserts a vertex pair, then anneals swaps) ---------- */

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

    if (d < 2 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    read_start(&gbest);
    if (gbest.n == 0) { printf("0 0\n"); return 0; }
    lift_phase(t0 + 0.8 * (t_end - t0));
    grow_search(t_end);
    if (!is_valid(&gbest)) { printf("0 0\n"); return 0; }
    print_graph(&gbest);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions (used as starts and as fallbacks).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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

    # C engine: sampled semidirect-product lifts, then grow-by-two with the leftover time.
    total = max(1.0, 0.85 * time_limit - 1.5)
    remaining = total - (time.monotonic() - t0)
    if remaining > 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 10)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
