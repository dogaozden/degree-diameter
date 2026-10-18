"""Orbit-reduced lift annealing: bi-Cayley voltage lifts over semidirect products, with a C engine
that anneals voltages and base permutations, then grows the best graph by two vertices at a time."""
import time

import lib


# ----------------------------------------------------------------------------
# C engine.
#
# Lifts: base has p A-vertices and p B-vertices, and d layers, each a permutation sigma_t
# with a voltage g_{t,i} in a semidirect group G = Z_m x| Z_k (order N). A_{i,x} ~ B_{sigma_t(i), x*g}.
# Left multiplication by G is an automorphism, transitive on each fibre, so the diameter
# check only needs BFS from the 2p identity vertices. This makes each evaluation cheap.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
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
#define MAXP 6
#define MAXG 4096
#define PEN 100000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct {
    int m, k, r;
    int rp[MAXG];
} Grp;

typedef struct {
    int p, N;
    int sig[MAXD][MAXP];
    int vg[MAXD][MAXP];
} Lift;

static int d, D;
static double t_end;
static uint64_t rng_state = 88172645463325252ULL;
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];
static int vis[MAXN];
static int vis_stamp = 0;
static int qbuf[MAXN];
static int cbad[MAXN];
static int blist[MAXN];

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

/* Number of unordered pairs at distance > D. Fills badv[v] = bad partners of v. */
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

/* Z_m x|_r Z_k: element (a,b) = a*k+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k). Identity is 0. */
static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

static int random_group(int N, Grp *G) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)(count < 2000000000L ? count : 2000000000L)) == 0) {
                G->m = m; G->k = k; G->r = r;
            }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

static void rand_perm(int *a, int p) {
    for (int i = 0; i < p; i++) a[i] = i;
    for (int i = p - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int s = a[i]; a[i] = a[j]; a[j] = s;
    }
}

/* Vertices: A_{i,x} = i*N + x (side 0), B_{j,y} = p*N + j*N + y (side 1). Every vertex has degree d. */
static void build_lift(Graph *g, const Grp *G, const Lift *L) {
    int p = L->p, N = L->N;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < d; t++)
        for (int i = 0; i < p; i++) {
            int j = L->sig[t][i], gg = L->vg[t][i];
            for (int x = 0; x < N; x++)
                add_edge(g, i * N + x, p * N + j * N + gmul(G, x, gg));
        }
}

/* Duplicate darts: same A-index, same B-index, same voltage. */
static long dup_count(const Lift *L) {
    long c = 0;
    for (int i = 0; i < L->p; i++)
        for (int t1 = 0; t1 < d; t1++)
            for (int t2 = t1 + 1; t2 < d; t2++)
                if (L->sig[t1][i] == L->sig[t2][i] && L->vg[t1][i] == L->vg[t2][i]) c++;
    return c;
}

/* Unreached vertices within distance D from source s. */
static long source_cost(const Graph *g, int s) {
    vis_stamp++;
    int head = 0, tail = 0, dist = 0;
    qbuf[tail++] = s;
    vis[s] = vis_stamp;
    while (head < tail && dist < D) {
        int end = tail;
        while (head < end) {
            int v = qbuf[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (vis[u] != vis_stamp) { vis[u] = vis_stamp; qbuf[tail++] = u; }
            }
        }
        dist++;
    }
    return (long)g->n - tail;
}

/* Cost over the 2p fibre representatives (sufficient by fibre transitivity). */
static long lift_cost(Graph *g, const Grp *G, const Lift *L) {
    build_lift(g, G, L);
    long c = 0;
    int p = L->p, N = L->N;
    for (int i = 0; i < p; i++) c += source_cost(g, i * N);
    for (int j = 0; j < p; j++) c += source_cost(g, p * N + j * N);
    c += PEN * dup_count(L);
    return c;
}

/* Simulated annealing on voltages and layer permutations. Leaves L at the best state seen. */
static int lift_anneal(Graph *g, const Grp *G, Lift *L, long steps) {
    int p = L->p, N = L->N;
    long cur = lift_cost(g, G, L);
    Lift bestL = *L;
    long bestc = cur;
    double T = 2.0, Tend = 0.05;
    double f = pow(Tend / T, 1.0 / (double)steps);
    for (long s = 0; s < steps && cur > 0; s++, T *= f) {
        if ((s & 63) == 0 && now() > t_end) break;
        if (p >= 2 && rnd01() < 0.25) {
            int t = rndint(d), i1 = rndint(p), i2 = rndint(p - 1);
            if (i2 >= i1) i2++;
            int tmp = L->sig[t][i1]; L->sig[t][i1] = L->sig[t][i2]; L->sig[t][i2] = tmp;
            long c = lift_cost(g, G, L);
            if (c <= cur || rnd01() < exp((double)(cur - c) / T)) {
                cur = c;
            } else {
                tmp = L->sig[t][i1]; L->sig[t][i1] = L->sig[t][i2]; L->sig[t][i2] = tmp;
            }
        } else {
            int t = rndint(d), i = rndint(p);
            int old = L->vg[t][i];
            int ng = rndint(N - 1);
            if (ng >= old) ng++;
            L->vg[t][i] = ng;
            long c = lift_cost(g, G, L);
            if (c <= cur || rnd01() < exp((double)(cur - c) / T)) {
                cur = c;
            } else {
                L->vg[t][i] = old;
            }
        }
        if (cur < bestc) { bestc = cur; bestL = *L; }
    }
    *L = bestL;
    return bestc == 0;
}

static void lift_phase(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    static Lift L;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        int r = rndint(12);
        int p = r < 2 ? 1 : r < 4 ? 2 : r < 7 ? 3 : r < 10 ? 4 : r < 11 ? 5 : 6;
        long nmin = ((long)best->n + 2 + 2L * p - 1) / (2L * p);
        long N = nmin + rndint(3);
        if (N < 2 || 2L * p * N > moore || 2L * p * N > MAXN) {
            if (++fails > 100000) return;
            continue;
        }
        if (!random_group((int)N, &G)) continue;
        L.p = p;
        L.N = (int)N;
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            rand_perm(perm, p);
            for (int i = 0; i < p; i++) {
                L.sig[t][i] = perm[i];
                L.vg[t][i] = rndint((int)N);
            }
        }
        if (lift_anneal(&cand, &G, &L, 30000)) {
            build_lift(&cand, &G, &L);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* Grow by two vertices: attach x,y, then repair bad pairs with random edge switches. */
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
    memcpy(cbad, badv, sizeof(int) * work->n);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int nbl = 0;
        for (int w = 0; w < work->n; w++)
            if (cbad[w]) blist[nbl++] = w;
        if (nbl == 0) break;
        int v = rnd01() < 0.8 ? blist[rndint(nbl)] : rndint(work->n);
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
            memcpy(cbad, badv, sizeof(int) * work->n);
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
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && best.n < moore_bound()) {
        lift_phase(&best, t0 + (t_end - t0) * 0.6);
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
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite.
    best = lib.haar_graph(d, range(d))

    # Exact construction for D = 3 when d - 1 is a prime power (calibration case).
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            n, e = lib.araujo_lopez_graph(d - 2)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except (ValueError, RuntimeError):
            pass

    # Main search: C orbit-reduced lift annealing, then grow-by-two.
    budget = max(1.0, 0.8 * time_limit - 3.0)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 6.0)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except (RuntimeError, ValueError):
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
