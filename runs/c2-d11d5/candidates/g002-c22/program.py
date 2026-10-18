"""Bi-Cayley lift annealing in C, with grow-by-two polishing.

Change from the parent: the voltage annealing that used to run in numpy now runs in C. Each lift is
a bi-Cayley graph over a semidirect product Z_m x| Z_k2 with k blocks per side and d layers of block
permutations plus voltages. Diameter is checked with bitmask reachability from the 2k block roots,
which is exact by left-translation symmetry. Successful lifts are checked with the full bitset
diameter test. Lift sizes are chosen just above the current best, and an adaptive choice of k
tracks which block counts succeed. Phase B grows the best graph by two vertices at a time.

Every returned graph is checked with lib.is_valid. K_{d,d} (or a known exact graph) is the fallback.
This is an exploratory search, and its effect on the d=11, D=5 target has not been measured.
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
#define MAXK2 64
#define PEN 1000

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

/* ---------- semidirect group Z_m x| Z_k2, element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e) ---------- */

typedef struct { int m, k2, G; int rp[MAXK2]; } Grp;

static void grp_init(Grp *g, int m, int k2, int r) {
    g->m = m;
    g->k2 = k2;
    g->G = m * k2;
    g->rp[0] = 1 % m;
    for (int b = 1; b < k2; b++) g->rp[b] = (int)((long)g->rp[b - 1] * r % m);
}

static int gmul(const Grp *g, int x, int y) {
    int a = x / g->k2, b = x % g->k2, c = y / g->k2, e = y % g->k2;
    return (int)(((long)a + (long)g->rp[b] * c) % g->m) * g->k2 + (b + e) % g->k2;
}

static int pick_r(int m, int k2) {
    if (k2 == 1 || m <= 2) return 1;
    for (int t = 0; t < 100; t++) {
        int c = 2 + rndint(m - 2);
        if (gcd(c, m) == 1 && powmod(c, k2, m) == 1 % m) return c;
    }
    return 1;
}

/* ---------- bi-Cayley lift: k blocks per side, d layers, voltages S[l][i] ---------- */

typedef struct {
    int k, G;
    Grp grp;
    int layers[MAXD][MAXK];
    int S[MAXD][MAXK];
} Lift;

static int nbr[MAXD][MAXN];
static uint16_t bufA[MAXN], bufB[MAXN], reachCur[MAXN], reachTry[MAXN];

/* Dart (l,i): top vertex i*G+x joins bottom (k+layers[l][i])*G + x*S[l][i]. */
static void set_dart(const Lift *L, int l, int i) {
    int k = L->k, G = L->G, j = L->layers[l][i], s = L->S[l][i];
    for (int x = 0; x < G; x++) {
        int y = gmul(&L->grp, x, s);
        int top = i * G + x, bot = (k + j) * G + y;
        nbr[l][top] = bot;
        nbr[l][bot] = top;
    }
}

static long dupcount(const Lift *L) {
    int k = L->k;
    int tot = d * k;
    long c = 0;
    for (int a = 0; a < tot; a++) {
        int l = a / k, i = a % k;
        for (int b = 0; b < a; b++) {
            int l2 = b / k, i2 = b % k;
            if (i == i2 && L->layers[l][i] == L->layers[l2][i2] && L->S[l][i] == L->S[l2][i2]) c++;
        }
    }
    return c;
}

/* Returns penalised cost; fills reachTry with per-vertex reach masks. */
static long eval_lift(const Lift *L) {
    int k = L->k, G = L->G, N = 2 * k * G;
    uint16_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint16_t) * (size_t)N);
    for (int b = 0; b < 2 * k; b++) cur[b * G] |= (uint16_t)(1u << b);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            uint16_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
        }
        uint16_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long un = 0;
    for (int v = 0; v < N; v++) un += 2 * k - __builtin_popcount((unsigned)cur[v]);
    memcpy(reachTry, cur, sizeof(uint16_t) * (size_t)N);
    return un + PEN * dupcount(L);
}

static void random_lift(Lift *L) {
    int k = L->k, G = L->G;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) L->layers[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = L->layers[l][i];
            L->layers[l][i] = L->layers[l][j];
            L->layers[l][j] = t;
        }
        for (int i = 0; i < k; i++) L->S[l][i] = rndint(G);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) set_dart(L, l, i);
}

static int anneal(Lift *L, double until, long iters, long patience) {
    int k = L->k, G = L->G, N = 2 * k * G, full = (1 << (2 * k)) - 1;
    random_lift(L);
    long cost = eval_lift(L);
    memcpy(reachCur, reachTry, sizeof(uint16_t) * (size_t)N);
    double c0 = cost > 0 ? (double)cost : 1.0;
    long best_cost = cost, last = 0;

    for (long t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && now() > until) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;
        long c2;

        if (k >= 2 && rnd01() < 0.2) {
            int l = rndint(d), i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int tmp = L->layers[l][i1];
            L->layers[l][i1] = L->layers[l][i2];
            L->layers[l][i2] = tmp;
            set_dart(L, l, i1);
            set_dart(L, l, i2);
            c2 = eval_lift(L);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(reachCur, reachTry, sizeof(uint16_t) * (size_t)N);
                if (cost < best_cost) { best_cost = cost; last = t; }
            } else {
                tmp = L->layers[l][i1];
                L->layers[l][i1] = L->layers[l][i2];
                L->layers[l][i2] = tmp;
                set_dart(L, l, i1);
                set_dart(L, l, i2);
            }
        } else {
            int l = -1, i = -1;
            if (rnd01() < 0.4) {
                int v = -1;
                for (int tr = 0; tr < 30; tr++) {
                    int w = rndint(N);
                    if (reachCur[w] != full) { v = w; break; }
                }
                if (v >= 0) {
                    int b = v / G;
                    l = rndint(d);
                    if (b < k) i = b;
                    else {
                        for (int ii = 0; ii < k; ii++)
                            if (L->layers[l][ii] == b - k) { i = ii; break; }
                    }
                }
            }
            if (i < 0) { l = rndint(d); i = rndint(k); }
            if (G < 2) continue;
            int old = L->S[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            L->S[l][i] = nw;
            set_dart(L, l, i);
            c2 = eval_lift(L);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(reachCur, reachTry, sizeof(uint16_t) * (size_t)N);
                if (cost < best_cost) { best_cost = cost; last = t; }
            } else {
                L->S[l][i] = old;
                set_dart(L, l, i);
            }
        }
    }
    return cost == 0;
}

static void lift_to_graph(const Lift *L, Graph *g) {
    int k = L->k, G = L->G, N = 2 * k * G;
    g->n = N;
    for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = v >= k * G; }
    for (int v = 0; v < k * G; v++)
        for (int l = 0; l < d; l++) add_edge(g, v, nbr[l][v]);
}

static double kwin[MAXK + 1], ktrial[MAXK + 1];
static const int K2C[14] = {1, 1, 2, 2, 2, 3, 4, 4, 5, 6, 8, 9, 10, 12};

static int pick_k(void) {
    if (rnd01() < 0.2) return 1 + rndint(MAXK);
    int bestk = 1;
    double bs = -1.0;
    for (int k = 1; k <= MAXK; k++) {
        double s = (kwin[k] + 1.0) / (ktrial[k] + 2.0) + 0.02 * rnd01();
        if (s > bs) { bs = s; bestk = k; }
    }
    return bestk;
}

static void lift_search(Graph *best, double until) {
    static Lift L;
    static Graph cand;
    long moore = moore_bound();
    long fails = 0;
    while (now() < until) {
        if (best->n + 2 > moore) return;
        int k = pick_k();
        long base = best->n / (2 * k);
        long Gt = base + 1 + rndint((int)(base / 8 + 2));
        int k2 = K2C[rndint(14)];
        long m = (Gt + k2 - 1) / k2;
        if (m < 2) m = 2;
        long G = m * k2;
        long N = 2L * k * G;
        if (N <= best->n || N > moore || N > MAXN || G > 100000) {
            if (++fails > 100000) return;
            continue;
        }
        int r = pick_r((int)m, k2);
        grp_init(&L.grp, (int)m, k2, r);
        L.k = k;
        L.G = (int)G;
        ktrial[k] += 1.0;
        if (anneal(&L, until, 8000, 2000)) {
            lift_to_graph(&L, &cand);
            if (cand.n > best->n && is_valid(&cand)) {
                copy_graph(best, &cand);
                kwin[k] += 1.0;
            }
        }
    }
}

/* ---------- grow-by-two with edge-swap annealing (from the parent) ---------- */

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

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    if (d < 1 || D < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && d >= 2 && best.n < moore_bound()) {
        lift_search(&best, t0 + limit * 0.7);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    # Exact Moore graph for D = 3 when d - 1 is a prime power: return immediately.
    if D == 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
        if lib.is_valid(best[0], best[1], d, D):
            return best

    # Record-family start for D = 3 when d - 2 is a prime power.
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    budget = 0.8 * time_limit - 3.0 - (time.monotonic() - t0)
    if budget > 1.0 and D >= 2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 5)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except (RuntimeError, ValueError, OSError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
