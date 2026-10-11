"""Combined search: Python builds the best known start (projective planes, Araujo-Lopez,
generalized quadrangles, or K_{d,d}); a C engine anneals voltage lifts over semidirect products
Z_m x| Z_k, and climbs the vertex count one lift step at a time."""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v" (a valid start), or "0 0".
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Method: lifts over Z_m x| Z_k with p vertices per side. Vertices A_{i,g} = i*N+g and
 * B_{j,h} = p*N + j*N + h. Dart (layer, i) joins A_{i,g} to B_{sigma_layer(i), g*s} for all g.
 * Left multiplication is an automorphism, so the diameter is <= D iff a BFS of depth D from
 * each of the 2p class representatives reaches everything. The cost is the number of
 * unreached (representative, vertex) pairs; simulated annealing drives it to 0 by changing
 * voltages and by swapping endpoints inside a layer (which keeps the graph d-regular).
 * Each success raises the vertex count by 2p, and the search climbs from the best graph.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 16
#define MAXW (MAXN / 64)
#define MAXP 4
#define MAXQ (MAXD * MAXP)
#define MAXCAND 256

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int m, k, r; } GrpC;

static int d, D;
static double t_end;
static Graph best, work;
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* ------------------------------------------------------------ utilities */

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

/* ------------------------------------------------------------ graph basics */

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
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
    static int queue[MAXN];
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
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

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element a*k+b; (a,b)(c,e) = (a + r^b c mod m, b+e mod k). */
static int gm, gk, gr;
static long rp[MAXN];

static int gmul(int x, int y) {
    int a = x / gk, b = x % gk, c = y / gk, e = y % gk;
    return (int)(((long)a + rp[b] * c) % gm) * gk + (b + e) % gk;
}

static void set_group(int m, int k, int r) {
    gm = m; gk = k; gr = r;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = rp[b - 1] * r % m;
}

static GrpC cand[MAXCAND];
static int ncand;

static int enum_groups(int N) {
    ncand = 0;
    for (int k = 1; k <= N; k++) {
        if (N % k) continue;
        int m = N / k;
        if (m == 1) {
            if (ncand < MAXCAND) { cand[ncand].m = 1; cand[ncand].k = k; cand[ncand].r = 0; ncand++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1 || powmod(r, k, m) != 1 % m) continue;
            if (ncand < MAXCAND) { cand[ncand].m = m; cand[ncand].k = k; cand[ncand].r = r; ncand++; }
        }
    }
    return ncand;
}

/* ------------------------------------------------------------ lift state */

static int nd;          /* darts = d * p */
static int P_, NG;      /* base vertices per side, group order */
static int di[MAXQ], dj[MAXQ], ds[MAXQ];
static int dperm[MAXQ][MAXN];
static int bds[MAXQ], bdj[MAXQ];
static int adjL[MAXN][MAXD], degL[MAXN];
static int mark[MAXN], qbuf[MAXN];
static int stampv = 0;

static void refresh_perm(int q) {
    for (int g = 0; g < NG; g++) dperm[q][g] = gmul(g, ds[q]);
}

/* True if dart q repeats the (i, j, s) of another dart (would create a multi-edge). */
static int clash_dart(int q) {
    for (int t = 0; t < nd; t++)
        if (t != q && di[t] == di[q] && dj[t] == dj[q] && ds[t] == ds[q]) return 1;
    return 0;
}

static int random_state(int p, int N, GrpC G) {
    int perm[MAXP];
    P_ = p; NG = N; nd = d * p;
    set_group(G.m, G.k, G.r);
    for (int layer = 0; layer < d; layer++) {
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1), s = perm[i];
            perm[i] = perm[j];
            perm[j] = s;
        }
        for (int i = 0; i < p; i++) {
            int q = layer * p + i;
            di[q] = i;
            dj[q] = perm[i];
            ds[q] = rndint(N);
        }
    }
    for (int q = 0; q < nd; q++) {
        int tries = 0;
        while (clash_dart(q)) {
            if (++tries > 10000) return 0;
            ds[q] = rndint(N);
        }
    }
    for (int q = 0; q < nd; q++) refresh_perm(q);
    return 1;
}

static void save_best(void) {
    memcpy(bds, ds, sizeof(int) * nd);
    memcpy(bdj, dj, sizeof(int) * nd);
}

static void restore_best(void) {
    memcpy(ds, bds, sizeof(int) * nd);
    memcpy(dj, bdj, sizeof(int) * nd);
    for (int q = 0; q < nd; q++) refresh_perm(q);
}

static void build_lift_adj(void) {
    int p = P_, N = NG, V = 2 * p * N;
    for (int v = 0; v < V; v++) degL[v] = 0;
    for (int q = 0; q < nd; q++)
        for (int g = 0; g < N; g++) {
            int a = di[q] * N + g;
            int b = p * N + dj[q] * N + dperm[q][g];
            adjL[a][degL[a]++] = b;
            adjL[b][degL[b]++] = a;
        }
}

/* Unreached (representative, vertex) pairs over the 2p class representatives. 0 = valid. */
static long lift_cost(void) {
    int p = P_, N = NG, V = 2 * p * N;
    if (stampv > 1000000000) { memset(mark, 0, sizeof(mark)); stampv = 0; }
    build_lift_adj();
    long total = 0;
    for (int s = 0; s < 2 * p; s++) {
        int src = s < p ? s * N : p * N + (s - p) * N;
        stampv++;
        int head = 0, tail = 0;
        mark[src] = stampv;
        qbuf[tail++] = src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = qbuf[head++];
                for (int k = 0; k < degL[u]; k++) {
                    int v = adjL[u][k];
                    if (mark[v] != stampv) {
                        mark[v] = stampv;
                        qbuf[tail++] = v;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

static void build_graph(Graph *g) {
    int p = P_, N = NG;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int q = 0; q < nd; q++)
        for (int x = 0; x < N; x++)
            add_edge(g, di[q] * N + x, p * N + dj[q] * N + dperm[q][x]);
}

/* Simulated annealing on the current lift. Returns the best cost; on 0 the state is the
 * valid lift. */
static long anneal(long max_steps, double until) {
    long cost = lift_cost(), best_cost = cost;
    save_best();
    if (best_cost == 0) return 0;
    const double T0 = 2.0, T1 = 0.05;
    for (long it = 0; it < max_steps && best_cost > 0; it++) {
        if ((it & 31) == 0 && now() > until) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)max_steps);
        if (P_ >= 2 && rndint(3) == 0) {
            int layer = rndint(d);
            int i1 = rndint(P_), i2 = rndint(P_);
            if (i1 == i2) continue;
            int q1 = layer * P_ + i1, q2 = layer * P_ + i2;
            int t = dj[q1]; dj[q1] = dj[q2]; dj[q2] = t;
            if (clash_dart(q1) || clash_dart(q2)) {
                t = dj[q1]; dj[q1] = dj[q2]; dj[q2] = t;
                continue;
            }
            long c2 = lift_cost();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) {
                cost = c2;
            } else {
                t = dj[q1]; dj[q1] = dj[q2]; dj[q2] = t;
                continue;
            }
        } else {
            int q = rndint(nd);
            int olds = ds[q];
            int news = rndint(NG);
            if (news == olds) continue;
            ds[q] = news;
            if (clash_dart(q)) { ds[q] = olds; continue; }
            refresh_perm(q);
            long c2 = lift_cost();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) {
                cost = c2;
            } else {
                ds[q] = olds;
                refresh_perm(q);
                continue;
            }
        }
        if (cost < best_cost) {
            best_cost = cost;
            save_best();
        }
    }
    restore_best();
    return best_cost;
}

/* ------------------------------------------------------------ main */

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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (D < 2) { printf("2 1\n0 1\n"); return 0; }

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    long moore = moore_bound();
    long cap = moore < MAXN ? moore : MAXN;
    static const int pch[6] = {1, 1, 2, 2, 3, 4};

    while (now() < t_end) {
        int p = pch[rndint(6)];
        long Nmin_l = best.n / (2 * p) + 1;
        if (Nmin_l < d) Nmin_l = d;
        if (2L * p * Nmin_l > cap) {
            if (p == 1) break;
            continue;
        }
        int Nmin = (int)Nmin_l;
        int N = Nmin;
        if (rndint(4) == 0) N += rndint(3);
        while (N > Nmin && 2L * p * N > cap) N--;
        if (2L * p * N > cap) continue;
        if (enum_groups(N) == 0) continue;
        GrpC G = cand[rndint(ncand)];
        if (!random_state(p, N, G)) continue;
        double remain = t_end - now();
        if (remain <= 0) break;
        double slice = 1.5 + N / 80.0;
        if (slice > remain) slice = remain;
        long c = anneal(300000, now() + slice);
        if (c == 0) {
            build_graph(&work);
            if (work.n > best.n && is_valid(&work)) memcpy(&best, &work, sizeof(Graph));
        }
    }

    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    import itertools
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


def _known(d, D):
    """Best directly constructed start for (d, D), or None."""
    try:
        if D == 3:
            if lib.is_prime_power(d - 1):
                return lib.projective_plane_incidence(d - 1)
            if d - 2 >= 3 and lib.is_prime_power(d - 2):
                return lib.araujo_lopez_graph(d - 2)
        if D == 4:
            for q in range(min(d - 1, 5), 1, -1):
                if lib.is_prime_power(q):
                    return _gq_w(q)
    except Exception:
        return None
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2
    known = _known(d, D)
    if known is not None and known[0] > best[0] and lib.is_valid(known[0], known[1], d, D):
        best = known

    if d > 16:   # C engine limit
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 5)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass
    return best
