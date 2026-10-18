"""Bi-Cayley lift annealing in C, then grow-by-two, with Python constructions and checks.

New in this version: the voltage-lift search over semidirect products Z_m x| Z_k2 runs inside
the C engine. A lift is vertex-transitive under left multiplication by the group, so the graph
has diameter <= D exactly when every block representative (i, identity) reaches all vertices
within D. The cost is the number of unreached (representative, vertex) pairs, computed by k
BFS runs of depth D on the explicit lift. That is about 100x cheaper than the numpy version,
so the annealer gets far more moves. A bandit over base sizes k and a ratcheting order goal
steer the search. The best lift is then grown by the parent's grow-by-two engine.

Every returned graph is checked with lib.is_valid. K_{d,d} is the fallback.
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
#define MAXK 4
#define MAXG (MAXN / 2)
#define MAXK2 64
#define LIFT_FRAC 0.8
#define ANNEAL_ITERS 60000L
#define ANNEAL_PATIENCE 8000L
#define DUP_PEN 1000L

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
static Graph gbest, gwork, gcand;
static int used[MAXN];
static int stamp = 0;

/* Lift state: vertices A(i,g) = i*G + g for i < LK, B(p,h) = (LK+p)*G + h. */
static int LK, LK2, LM, LG, LN;
static int Aof[MAXG], Bof[MAXG], ginv[MAXG];
static int pw[MAXK2];
static int lay[MAXD][MAXK], ilay[MAXD][MAXK], sv[MAXD][MAXK];
static int nb[MAXN][MAXD];
static int vis[MAXN], visstamp = 0;
static int qbuf[MAXN];

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

static void make_kdd(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (v < d) ? 0 : 1;
    }
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            add_edge(g, i, d + j);
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

/* ---------------------------------------------------------------------------
 * Bi-Cayley lifts over Z_m x| Z_k2 (element (a,b) coded as a*k2+b,
 * (a,b)*(c,d) = (a + r^b c, b + d)).
 * Every layer l pairs A-block i with B-block lay[l][i] through voltage sv[l][i]:
 * A(i,g) ~ B(p, g*s). Each layer is a perfect matching between blocks, so the
 * graph is d-regular when no two layers repeat the same (i, p, s).
 * ------------------------------------------------------------------------- */

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcd_int(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static inline int gmul(int x, int y) {
    int b1 = Bof[x], b2 = Bof[y];
    int a = (Aof[x] + pw[b1] * Aof[y]) % LM;
    int b = b1 + b2;
    if (b >= LK2) b -= LK2;
    return a * LK2 + b;
}

/* Choose a random semidirect group of order about Gt for k base blocks per side. */
static int setup_group(int k, int Gt) {
    static const int K2s[] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12};
    int k2 = K2s[rndint(11)];
    int m = (Gt + k2 - 1) / k2;
    if (m < 2) m = 2;
    int r = 1;
    if (k2 > 1) {
        int ok = 0;
        for (int tr = 0; tr < 300 && !ok; tr++) {
            int c = (m > 2) ? 2 + rndint(m - 2) : 1;
            if (gcd_int(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                r = c;
                ok = 1;
            }
        }
        if (!ok) return 0;
    }
    long G = (long)m * k2;
    if (G > MAXG || 2L * k * G > MAXN) return 0;
    if (2L * k * G > moore_bound()) return 0;
    LK = k;
    LK2 = k2;
    LM = m;
    LG = (int)G;
    LN = (int)(2L * k * G);
    for (int b = 0; b < k2; b++) pw[b] = (int)powmod(r, b, m);
    for (int x = 0; x < LG; x++) {
        int a = x / LK2, b = x % LK2;
        Aof[x] = a;
        Bof[x] = b;
        int bb = (LK2 - b) % LK2;
        int aa = (int)((LM - ((long long)a * pw[bb]) % LM) % LM);
        ginv[x] = aa * LK2 + bb;
    }
    return 1;
}

static void set_ilay(int l) {
    for (int i = 0; i < LK; i++) ilay[l][lay[l][i]] = i;
}

static void random_config(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < LK; i++) lay[l][i] = i;
        for (int i = LK - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        set_ilay(l);
        for (int i = 0; i < LK; i++) sv[l][i] = rndint(LG);
    }
}

/* Fill nb[v][l] for every lifted vertex v from the current layers and voltages. */
static void rebuild_nb(void) {
    int k = LK, G = LG;
    for (int i = 0; i < k; i++)
        for (int g = 0; g < G; g++) {
            int v = i * G + g;
            for (int l = 0; l < d; l++) {
                int p = lay[l][i];
                nb[v][l] = (k + p) * G + gmul(g, sv[l][i]);
            }
        }
    for (int p = 0; p < k; p++)
        for (int h = 0; h < G; h++) {
            int v = (k + p) * G + h;
            for (int l = 0; l < d; l++) {
                int i = ilay[l][p];
                nb[v][l] = i * G + gmul(h, ginv[sv[l][i]]);
            }
        }
}

/* Vertices within distance D of src in the current lift, counted as unreached. */
static long bfs_unreached(int src) {
    visstamp++;
    int head = 0, tail = 0, cnt = 1;
    vis[src] = visstamp;
    qbuf[tail++] = src;
    for (int lev = 0; lev < D && head < tail; lev++) {
        int end = tail;
        while (head < end) {
            int v = qbuf[head++];
            for (int l = 0; l < d; l++) {
                int u = nb[v][l];
                if (vis[u] != visstamp) {
                    vis[u] = visstamp;
                    qbuf[tail++] = u;
                    cnt++;
                }
            }
        }
    }
    return LN - cnt;
}

/* Cost = unreached pairs (representative, vertex) over all block representatives,
 * plus a large penalty per repeated (block, block, voltage) triple. Zero means valid. */
static long lift_cost(void) {
    rebuild_nb();
    long dup = 0;
    for (int i = 0; i < LK; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (lay[l1][i] == lay[l2][i] && sv[l1][i] == sv[l2][i]) dup++;
    long unr = 0;
    for (int b = 0; b < 2 * LK; b++) unr += bfs_unreached(b * LG);
    return unr + DUP_PEN * dup;
}

/* Simulated annealing over layer permutations and voltages. Returns 1 when cost reaches 0.
 * On return nb may be stale; callers must call rebuild_nb() before reading it. */
static int anneal(long iters, long patience, double until) {
    long cost = lift_cost();
    double c0 = cost > 0 ? (double)cost : 1.0;
    long best = cost, last = 0;
    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 3) == 0 && now() > until) break;
        if (t - last > patience) break;
        double temp = 0.02 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.3) temp = 0.3;
        int l = rndint(d);
        if (LK >= 2 && rnd01() < 0.25) {
            int i1 = rndint(LK), i2 = rndint(LK - 1);
            if (i2 >= i1) i2++;
            int tmp = lay[l][i1];
            lay[l][i1] = lay[l][i2];
            lay[l][i2] = tmp;
            set_ilay(l);
            long c2 = lift_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < best) { best = cost; last = t; }
            } else {
                tmp = lay[l][i1];
                lay[l][i1] = lay[l][i2];
                lay[l][i2] = tmp;
                set_ilay(l);
            }
        } else {
            int i = rndint(LK);
            int old = sv[l][i];
            int nw = rndint(LG);
            if (nw == old) continue;
            sv[l][i] = nw;
            long c2 = lift_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < best) { best = cost; last = t; }
            } else {
                sv[l][i] = old;
            }
        }
    }
    return cost == 0;
}

/* Expand the current lift (nb must be fresh) into an explicit graph. */
static void lift_to_graph(Graph *g) {
    int half = LK * LG;
    g->n = LN;
    for (int v = 0; v < LN; v++) {
        g->deg[v] = 0;
        g->side[v] = (v < half) ? 0 : 1;
    }
    for (int v = 0; v < half; v++)
        for (int l = 0; l < d; l++)
            add_edge(g, v, nb[v][l]);
}

/* Bandit over base sizes k with a ratcheting order goal. */
static void lift_phase(double until, double goal) {
    int trials[MAXK + 1], wins[MAXK + 1];
    for (int k = 0; k <= MAXK; k++) { trials[k] = 0; wins[k] = 0; }
    while (now() < until) {
        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bv = -1.0;
            k = 1;
            for (int kk = 1; kk <= MAXK; kk++) {
                double v = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rnd01();
                if (v > bv) { bv = v; k = kk; }
            }
        }
        long Gt = (long)(goal / (2.0 * k)) + rndint(3);
        long cap = MAXN / (2 * k) - 12;
        if (Gt > cap) Gt = cap;
        if (Gt < 2) Gt = 2;
        if (!setup_group(k, (int)Gt)) {
            goal = fmax((double)gbest.n * 1.02, goal * 0.97);
            continue;
        }
        if (2L * k * LG <= gbest.n) {
            goal = fmax(goal, gbest.n * 1.02);
            continue;
        }
        trials[k]++;
        random_config();
        if (anneal(ANNEAL_ITERS, ANNEAL_PATIENCE, until)) {
            rebuild_nb();
            lift_to_graph(&gcand);
            if (gcand.n > gbest.n && is_valid(&gcand)) {
                copy_graph(&gbest, &gcand);
                wins[k]++;
            }
            goal = fmax(goal, gbest.n * 1.04);
        } else {
            goal = fmax(gbest.n * 1.02, goal * 0.97);
        }
    }
}

/* ---------------------------------------------------------------------------
 * Grow-by-two: insert one vertex on each side using freed degree, then anneal.
 * ------------------------------------------------------------------------- */

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
        long nb2 = bad_pairs(work);
        if (nb2 <= bad || rnd01() < exp((double)(bad - nb2) / T)) {
            bad = nb2;
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
    t_end = t0 + limit * 0.95 - 0.3;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 2 || d > MAXD || 2 * d > MAXN) { printf("0 0\n"); return 0; }

    read_start(&gbest);
    if (gbest.n == 0) make_kdd(&gbest);

    double goal = gbest.n * 1.02;
    double g0 = (double)moore_bound() / 4.0;
    if (g0 > MAXN - 2) g0 = MAXN - 2;
    if (g0 > goal) goal = g0;

    lift_phase(t0 + LIFT_FRAC * (t_end - t0), goal);
    grow_search(t_end);

    if (!is_valid(&gbest)) make_kdd(&gbest);
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
# Saturation: greedily add missing bipartite edges between deficient vertices.
# Distances only shrink, so validity is kept; callers still verify with lib.is_valid.
# ----------------------------------------------------------------------------

def _saturate(n, edges, d, D):
    """Greedily add missing bipartite edges between deficient vertices; returns (n, edges)."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if color[y] == -1:
                    color[y] = 1 - color[x]
                    stack.append(y)
    A = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    B = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    out = {(min(u, v), max(u, v)) for u, v in edges}
    for a in A:
        for b in B:
            if len(adj[a]) >= d:
                break
            if len(adj[b]) >= d or b in adj[a]:
                continue
            adj[a].add(b)
            adj[b].add(a)
            out.add((min(a, b), max(a, b)))
    return n, sorted(out)


def _safe_saturate(n, edges, d, D):
    """Saturate, but fall back to the input if anything goes wrong or the result is invalid."""
    try:
        sn, se = _saturate(n, edges, d, D)
        if lib.is_valid(sn, se, d, D):
            return sn, se
    except Exception:
        pass
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

    def consider_saturated(n, e):
        sn, se = _safe_saturate(n, e, d, D)
        consider(sn, se)
        consider(n, e)

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
            consider_saturated(*lib.araujo_lopez_graph(d - 2))
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

    # Main search: C lift annealing, then grow-by-two from the best graph.
    remaining = final - time.monotonic() - 1.0
    if remaining > 3.0:
        start = best if best_n > 2 * d else None
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=start, timeout=remaining + 3.0)
            n, e = lib.parse_graph_text(text)
            consider_saturated(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
