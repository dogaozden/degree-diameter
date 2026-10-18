"""Combined program: a C engine that runs a bi-Cayley voltage-lift search over semidirect
groups Z_m x| Z_k2 (the lift search now runs in C), then grow-by-two insertion on the best
graph when it is small enough. Exact constructions (projective planes, Araujo-Pardo-Lopez,
generalized quadrangles) seed the search. Every returned graph is checked with lib.is_valid,
and K_{d,d} is the fallback.
"""
import itertools

import lib


C_SOURCE = r'''
/* Lift-and-grow search engine.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid bipartite start), or "0 0".
 * stdout: "n m" + edges of the best valid graph found (never worse than the input).
 *
 * Phase 1 (lift): random bi-Cayley lifts over Z_m x| Z_k2 with k blocks per side.
 *   Vertex A_{i,g} = i*G + g, B_{j,h} = (k+j)*G + h, G = m*k2. Layer l joins A_i to
 *   B_{lay[l][i]} with voltage s: A_{i,g} ~ B_{j, g*s}. Each layer is a perfect matching,
 *   so the graph is d-regular. Simulated annealing over layer permutations and voltages
 *   minimises the number of unreached (vertex, block-representative) pairs.
 * Phase 2 (grow): insert one vertex per side with spare degree, then anneal edge swaps.
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
#define NK2 20
#define PENALTY 1000L
#define GROW_MAX_N 1500

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
static Graph gbest, gwork, cand;
static double t_end;
static double goal;

/* ---- lift state ---- */
static int gk2, gm, gr, gG, gk;
static int pw[40];
static int lay[MAXD][MAXK];
static int sft[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static uint32_t rcA[MAXN], rcB[MAXN];
static uint32_t RS[MAXN], RT[MAXN];
static int trials_k[MAXK + 1], wins_k[MAXK + 1];
static const int K2S[NK2] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

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

/* ======================= bi-Cayley lift search ======================= */

static long long powmod_ll(long long b, long long e, long long m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return r;
}

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* Semidirect product Z_m x| Z_k2: element a*k2 + b; (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / gk2, b = x % gk2, c = y / gk2, e = y % gk2;
    long long t = (long long)a + (long long)pw[b] * c;
    return (int)((t % gm) * gk2 + (b + e) % gk2);
}

static int ginv(int x) {
    int a = x / gk2, b = x % gk2;
    int nb = (gk2 - b) % gk2;
    long long t = (long long)pw[nb] * a % gm;
    return (int)(((gm - t) % gm) * gk2 + nb);
}

/* Pick a random group with order about target; r = 1 (direct product) is the fallback. */
static int sample_group(long target) {
    gk2 = K2S[rndint(NK2)];
    long mm = (target + gk2 - 1) / gk2;
    if (mm < 2) mm = 2;
    if (mm > MAXN) return 0;
    gm = (int)mm;
    gr = 1;
    if (gk2 > 1 && gm > 2) {
        int start = rndint(gm - 2);
        for (int t = 0; t < gm - 2; t++) {
            int c = 2 + (start + t) % (gm - 2);
            if (gcd_int(c, gm) == 1 && powmod_ll(c, gk2, gm) == 1 % gm) { gr = c; break; }
        }
    }
    pw[0] = 1 % gm;
    for (int b = 1; b < gk2; b++) pw[b] = (int)((long long)pw[b - 1] * gr % gm);
    gG = gm * gk2;
    return 1;
}

static void build_nbr(void) {
    const int k = gk, G = gG;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) {
            int j = lay[l][i], s = sft[l][i];
            int si = ginv(s);
            int bA = i * G, bB = (k + j) * G;
            for (int g = 0; g < G; g++) {
                nbr[l][bA + g] = bB + gmul(g, s);
                nbr[l][bB + g] = bA + gmul(g, si);
            }
        }
    }
}

/* Cost = unreached (vertex, block-representative) pairs + duplicate-dart penalty.
 * Left multiplication is an automorphism, so covering every vertex's distance to the
 * representatives is equivalent to diameter <= D. Trial reach goes to RT. */
static long evaluate(void) {
    const int k = gk, G = gG, N = 2 * k * G;
    build_nbr();
    uint32_t *cur = rcA, *nxt = rcB;
    memset(cur, 0, sizeof(uint32_t) * (size_t)N);
    for (int b = 0; b < 2 * k; b++) cur[(size_t)b * G] = 1u << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int u = 0; u < N; u++) {
            uint32_t x = cur[u];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][u]];
            nxt[u] = x;
            changed |= (x != cur[u]);
        }
        uint32_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    long unr = 0;
    for (int u = 0; u < N; u++) unr += 2 * k - __builtin_popcount(cur[u]);
    memcpy(RT, cur, sizeof(uint32_t) * (size_t)N);
    long dups = 0;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (lay[l][i] == lay[l2][i] && sft[l][i] == sft[l2][i]) dups++;
    return unr + PENALTY * dups;
}

/* Simulated annealing for one group/block configuration. On success the state (lay, sft,
 * nbr) is a cost-0 lift. */
static int lift_search(long iters, long patience, double deadline) {
    const int k = gk, G = gG, N = 2 * k * G;
    const uint32_t full = (1u << (2 * k)) - 1u;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) lay[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1), t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        for (int i = 0; i < k; i++) sft[l][i] = rndint(G);
    }
    long cost = evaluate();
    memcpy(RS, RT, sizeof(uint32_t) * (size_t)N);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long bestc = cost, last = 0;

    for (long t = 0; t < iters; t++) {
        if (cost == 0 || t - last > patience || now() > deadline) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (k >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int tmp = lay[l][i1];
            lay[l][i1] = lay[l][i2];
            lay[l][i2] = tmp;
            long c2 = evaluate();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(RS, RT, sizeof(uint32_t) * (size_t)N);
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                tmp = lay[l][i1];
                lay[l][i1] = lay[l][i2];
                lay[l][i2] = tmp;
                build_nbr();
            }
            continue;
        }

        int l = 0, i = 0, u = -1;
        if (rnd01() < 0.4) {
            for (int tries = 0; tries < 30; tries++) {
                int v = rndint(N);
                if (RS[v] != full) { u = v; break; }
            }
        }
        if (u >= 0) {
            int block = u / G;
            l = rndint(d);
            if (block < k) i = block;
            else {
                i = 0;
                while (lay[l][i] != block - k) i++;
            }
        } else {
            l = rndint(d);
            i = rndint(k);
        }
        int old = sft[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        sft[l][i] = nw;
        long c2 = evaluate();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(RS, RT, sizeof(uint32_t) * (size_t)N);
            if (cost < bestc) { bestc = cost; last = t; }
        } else {
            sft[l][i] = old;
            build_nbr();
        }
    }
    return cost == 0;
}

/* Build the graph from the current cost-0 lift; keep it if valid and larger. */
static int adopt_lift(void) {
    const int k = gk, G = gG, N = 2 * k * G;
    if (N <= gbest.n || N > MAXN) return 0;
    cand.n = N;
    for (int v = 0; v < N; v++) {
        cand.deg[v] = 0;
        cand.side[v] = (unsigned char)(v < k * G ? 0 : 1);
    }
    for (int u = 0; u < k * G; u++)
        for (int l = 0; l < d; l++) add_edge(&cand, u, nbr[l][u]);
    if (!is_valid(&cand)) return 0;
    copy_graph(&gbest, &cand);
    return 1;
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

static void lift_loop(double until) {
    while (now() < until) {
        if (goal > MAXN - 300) goal = MAXN - 300;
        int k = pick_k();
        long target = (long)(goal / (2.0 * k)) + rndint(3);
        if (target < 2) target = 2;
        if (!sample_group(target)) {
            goal = fmax((double)gbest.n * 1.02, goal * 0.99);
            continue;
        }
        gk = k;
        int N = 2 * k * gG;
        if (N > MAXN) {
            goal = fmax((double)gbest.n * 1.02, goal * 0.99);
            continue;
        }
        if (N <= gbest.n) {
            goal = fmax(goal, gbest.n * 1.02);
            continue;
        }
        trials_k[k]++;
        if (lift_search(6000, 1500, until)) {
            wins_k[k]++;
            adopt_lift();
            goal = fmax(goal, N * 1.04);
        } else {
            goal = fmax((double)gbest.n * 1.02, goal * 0.99);
        }
    }
}

/* ============================ grow-by-two ============================ */

/* One grow-by-two attempt starting from best; on success work holds n+2 valid vertices. */
static int used[MAXN];
static int stamp = 0;

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
    while (now() < until && gbest.n + 2 <= moore_bound() && gbest.n + 2 <= MAXN - 2) {
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
    t_end = t0 + limit * 0.95 - 0.3;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    read_start(&gbest);
    goal = gbest.n > 0 ? gbest.n * 1.05 : 2.0 * d;

    /* Lift for 75% of the budget; if the graph is still small, grow; otherwise keep lifting. */
    double stage = t0 + 0.75 * (t_end - t0);
    lift_loop(stage);
    if (gbest.n > GROW_MAX_N || gbest.n == 0) lift_loop(t_end);
    else grow_search(t_end);

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
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
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
    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # One C run: lift search (bulk of the time), then grow-by-two if the graph is small.
    budget = max(1.0, 0.8 * time_limit - 2.0)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 8.0)
        n, e = lib.parse_graph_text(text)
        consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
