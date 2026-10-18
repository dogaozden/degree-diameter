"""Combined program: C-native bi-Cayley lift annealing, then a C grow-by-two phase.

New idea in this version: the lift search runs inside C. A semidirect-product lift is invariant
under left multiplication by the group, so the diameter condition only needs BFS from the 2k block
representatives. Each candidate costs O(2k * N * d) rather than an all-pairs check. The C engine
keeps the best valid graph (lift result or grown graph) and prints it.

Every returned graph is checked with lib.is_valid. K_{d,d} or a known construction is the fallback.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Stage 1: bi-Cayley lift annealing over Z_m x| Z_k2 (block-representative BFS cost).
 * Stage 2: grow-by-two from the best graph (insert one vertex per side, anneal swaps).
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid bipartite start), or "0 0".
 * stdout: "n m" + edges of the best valid graph found (never worse than the input).
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
#define PEN 1000

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
static Graph gbest, gwork, gtmp;
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
 * Vertices: A block i (i < KB) is i*GO + g; B block p is (KB+p)*GO + h.
 * Layer l: A block i joins B block lay[l][i] by voltage sv[l][i]:
 *          A_{i,g} ~ B_{p, g*sv}.   Each layer is a permutation, so the graph is d-regular.
 * Left multiplication by any group element is an automorphism, so validity is equivalent to:
 *          from each of the 2*KB block representatives, BFS of depth D reaches all N vertices.
 */
static const int K2_CHOICES[] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
#define NCH ((int)(sizeof K2_CHOICES / sizeof K2_CHOICES[0]))

static int KB, GO, MM, K2, RR;
static int pw[64];
static int lay[MAXD][MAXK];
static int sv[MAXD][MAXK];
static int nb[MAXN][MAXD];
static int vis[MAXN], vstamp = 0, qq[MAXN];

static long pmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long gcdl(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static void set_group(int kb, int go, int mm, int k2, int rr) {
    KB = kb; GO = go; MM = mm; K2 = k2; RR = rr;
    pw[0] = 1 % mm;
    for (int t = 1; t < k2; t++) pw[t] = (int)((long)pw[t - 1] * rr % mm);
}

/* (a,b)*(c,e) = (a + r^b c, b + e) with element code a*K2 + b. */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    int t = (int)(((long)pw[b] * c + a) % MM);
    return t * K2 + (b + e) % K2;
}

/* Inverse of (a,b) is (-r^(-b) a, -b). */
static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nbk = (K2 - b) % K2;
    int t = (int)((long)pw[nbk] * a % MM);
    t = (MM - t) % MM;
    return t * K2 + nbk;
}

static void build_nb(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < KB; i++) {
            int p = lay[l][i], s = sv[l][i];
            for (int g = 0; g < GO; g++) {
                int A = i * GO + g;
                int B = (KB + p) * GO + gmul(g, s);
                nb[A][l] = B;
                nb[B][l] = A;
            }
        }
}

/* Duplicate darts: same block pair and voltage in two layers would create a multi-edge. */
static long dup_count(void) {
    long c = 0;
    for (int l1 = 0; l1 < d; l1++)
        for (int l2 = l1 + 1; l2 < d; l2++)
            for (int i = 0; i < KB; i++)
                if (lay[l1][i] == lay[l2][i] && sv[l1][i] == sv[l2][i]) c++;
    return c;
}

/* Sum over block representatives of the number of vertices not reached within distance D. */
static long lift_cost(void) {
    int N = 2 * KB * GO;
    long unreached = 0;
    for (int src = 0; src < 2 * KB; src++) {
        int s0 = src * GO;
        vstamp++;
        int head = 0, tail = 0;
        vis[s0] = vstamp;
        qq[tail++] = s0;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int v = qq[head++];
                for (int l = 0; l < d; l++) {
                    int u = nb[v][l];
                    if (vis[u] != vstamp) { vis[u] = vstamp; qq[tail++] = u; }
                }
            }
        }
        unreached += N - tail;
    }
    return unreached;
}

/* Anneal one lift; on success the exact lift is verified and stored in gbest if larger. */
static int anneal(int kb, int go, int mm, int k2, int rr, long iters, double until, long patience) {
    set_group(kb, go, mm, k2, rr);
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < KB; i++) lay[l][i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lay[l][i]; lay[l][i] = lay[l][j]; lay[l][j] = t;
        }
        for (int i = 0; i < KB; i++) sv[l][i] = rndint(GO);
    }
    build_nb();
    long cost = lift_cost() + (long)PEN * dup_count();
    double c0 = cost > 1 ? (double)cost : 1.0;
    long last = 0;
    static int save_lay[MAXD][MAXK], save_sv[MAXD][MAXK];
    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 7) == 0 && now() > until) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;
        memcpy(save_lay, lay, sizeof lay);
        memcpy(save_sv, sv, sizeof sv);
        if (KB >= 2 && rnd01() < 0.25) {
            int l = rndint(d), i1 = rndint(KB), i2 = rndint(KB - 1);
            if (i2 >= i1) i2++;
            int t2 = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = t2;
        } else {
            int l = rndint(d), i = rndint(KB), ns = rndint(GO);
            if (ns == sv[l][i]) continue;
            sv[l][i] = ns;
        }
        build_nb();
        long c2 = lift_cost() + (long)PEN * dup_count();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < 0) break;
            if (cost < 1 || cost <= c2) last = (cost < 1) ? t : last;
        } else {
            memcpy(lay, save_lay, sizeof lay);
            memcpy(sv, save_sv, sizeof sv);
        }
    }
    if (cost != 0) return 0;
    build_nb();
    int NN = 2 * KB * GO;
    gtmp.n = NN;
    for (int v = 0; v < NN; v++) { gtmp.deg[v] = 0; gtmp.side[v] = (v < KB * GO) ? 0 : 1; }
    for (int v = 0; v < KB * GO; v++)
        for (int l = 0; l < d; l++) add_edge(&gtmp, v, nb[v][l]);
    if (!is_valid(&gtmp)) return 0;
    if (NN > gbest.n) copy_graph(&gbest, &gtmp);
    return 1;
}

static int sample_group(int kb, int target, int *mo, int *k2o, int *ro) {
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2_CHOICES[rndint(NCH)];
        int mm = (target + k2 - 1) / k2;
        if (mm < 2) mm = 2;
        if (2 * kb * mm * k2 > MAXN) continue;
        int rr = 1;
        if (k2 > 1 && mm > 2 && rndint(10) < 7) {
            for (int t = 0; t < 80; t++) {
                int c = 2 + rndint(mm - 2);
                if (gcdl(c, mm) == 1 && pmod(c, k2, mm) == 1 % mm) { rr = c; break; }
            }
        }
        *mo = mm; *k2o = k2; *ro = rr;
        return 1;
    }
    return 0;
}

static void lift_phase(double until) {
    long trials[MAXK + 1], wins[MAXK + 1];
    for (int k = 0; k <= MAXK; k++) { trials[k] = 0; wins[k] = 0; }
    double goal = gbest.n > 0 ? gbest.n * 1.05 : 4.0 * d;
    while (now() < until) {
        if (gbest.n + 2 > MAXN) break;
        int kb = 1;
        if (rndint(5) == 0) {
            kb = 1 + rndint(MAXK);
        } else {
            double bv = -1.0;
            for (int k = 1; k <= MAXK; k++) {
                double v = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
                if (v > bv) { bv = v; kb = k; }
            }
        }
        int target = (int)(goal / (2.0 * kb)) + rndint(3);
        if (target < 2) target = 2;
        if (2 * kb * target > MAXN) target = MAXN / (2 * kb);
        int mm, k2, rr;
        if (!sample_group(kb, target, &mm, &k2, &rr)) {
            goal = fmax(gbest.n * 1.02, goal * 0.99);
            continue;
        }
        int go = mm * k2;
        int N = 2 * kb * go;
        if (N <= gbest.n) {
            goal = fmax(goal, gbest.n * 1.02);
            continue;
        }
        trials[kb]++;
        if (anneal(kb, go, mm, k2, rr, 6000, until, 1500)) {
            wins[kb]++;
            if (N * 1.04 > goal) goal = N * 1.04;
        } else {
            goal = fmax(gbest.n * 1.02, goal * 0.99);
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
    t_end = t0 + limit * 0.9 - 0.2;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    read_start(&gbest);
    if (gbest.n == 0) { printf("0 0\n"); return 0; }

    double lift_end = t0 + 0.65 * (t_end - t0);
    if (d >= 2) lift_phase(lift_end);
    if (gbest.n > 2 * d) grow_search(t_end);

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

    if D == 2:
        return best

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

    # Search: the C engine does lift annealing and then grow-by-two from the best graph.
    total = max(1.0, 0.85 * time_limit - 1.5)
    remaining = total - (time.monotonic() - t0) - 1.0
    if remaining > 2.0 and d >= 2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 10)
            consider(*lib.parse_graph_text(text))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
