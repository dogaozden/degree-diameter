"""Combined search: fast orbit-based simulated annealing over group voltage lifts in C,
seeded from the best algebraic construction (PG(2,q), Araujo-Lopez, W(q)), followed by a
grow-by-two repair phase. Python only builds the start graph and validates the result."""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v" (a valid start graph), or "0 0".
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phases:
 *  1. Group voltage lifts. Base: k A-vertices and k B-vertices, each A_i has d darts
 *     (one per layer, layers are permutations). Group: semidirect Z_m x| Z_k2 of order G.
 *     Dart (i,j,s) joins A(i,g) to B(j, g*s). Left multiplication is an automorphism, so
 *     the diameter is <= D iff a BFS of depth D from each of the 2k representatives
 *     reaches every vertex. Simulated annealing over voltages (and base permutations)
 *     minimises the number of unreached (representative, vertex) pairs.
 *     Target order is pushed upward: the group order G is aimed just above the
 *     current best lift, and the aim spreads wider after repeated failures.
 *  2. Grow by two: add one vertex per side using spare degree from d-1 deleted edges,
 *     then anneal degree-preserving swaps until diameter <= D.
 */
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
#define MAXK 3
#define MAXDARTS (MAXD * MAXK)
#define BIGCOST 1000000000L
#define LIFT_ITERS 15000

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int i, j, s; } Dart;

static int d, D;
static double t_end;
static Graph best;

/* ------------------------------------------------------------------ utilities */

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

static int gcd_i(int a, int b) {
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

/* ------------------------------------------------------------------ graph basics */

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

/* ------------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D. Also sets badv[v]. */
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
            int back = 0;
            for (int k = 0; k < g->deg[u]; k++)
                if (g->adj[u][k] == v) back = 1;
            if (!back) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

/* ------------------------------------------------------------------ input / output */

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            u == v || g->deg[u] >= MAXD || g->deg[v] >= MAXD) {
            g->n = 0;
            return;
        }
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
                if (g->side[u] == 255) {
                    g->side[u] = 1 - g->side[v];
                    queue[tail++] = u;
                } else if (g->side[u] == g->side[v]) {
                    g->n = 0;
                    return;
                }
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

/* ------------------------------------------------------------------ groups */

/* Current group Z_gm x| Z_gk, element (a,b) coded a*gk + b,
 * (a,b)(c,e) = (a + r^b c mod gm, b + e mod gk). */
static int gm_ = 1, gk_ = 1;
static int grp_rp[MAXN];

static int gmul(int x, int y) {
    int a = x / gk_, b = x % gk_, c = y / gk_, e = y % gk_;
    return (int)(((long)a + (long)grp_rp[b] * c) % gm_) * gk_ + (b + e) % gk_;
}

static void set_group(int m, int k, int r) {
    gm_ = m;
    gk_ = k;
    grp_rp[0] = 1 % m;
    for (int b = 1; b < k; b++) grp_rp[b] = (int)((long)grp_rp[b - 1] * r % m);
}

/* Uniformly pick a valid (m, k, r) with m*k = N, r^k = 1 mod m, gcd(r, m) = 1. */
static int pick_group(int N, int *pm, int *pk, int *pr) {
    int count = 0, bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            count++;
            if (rndint(count) == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            count++;
            if (rndint(count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (count == 0) return 0;
    *pm = bm;
    *pk = bk;
    *pr = br;
    return 1;
}

/* ------------------------------------------------------------------ voltage lifts */

static int lk, lG, nd_cur;
static Dart cur_d[MAXDARTS], best_d[MAXDARTS];
static int ladj[MAXN][MAXD];
static int ldeg[MAXN];
static int lvis[MAXN], lqueue[MAXN];
static int lstamp = 0;

static int has_dup(void) {
    for (int a = 0; a < nd_cur; a++)
        for (int b = a + 1; b < nd_cur; b++)
            if (cur_d[a].i == cur_d[b].i && cur_d[a].j == cur_d[b].j &&
                cur_d[a].s == cur_d[b].s)
                return 1;
    return 0;
}

/* Number of unreached (representative, vertex) pairs within distance D. 0 means valid. */
static long lift_cost(void) {
    if (has_dup()) return BIGCOST;
    int N = 2 * lk * lG;
    for (int v = 0; v < N; v++) ldeg[v] = 0;
    for (int t = 0; t < nd_cur; t++) {
        int a0 = cur_d[t].i * lG;
        int b0 = (lk + cur_d[t].j) * lG;
        int s = cur_d[t].s;
        for (int g = 0; g < lG; g++) {
            int a = a0 + g, b = b0 + gmul(g, s);
            ladj[a][ldeg[a]++] = b;
            ladj[b][ldeg[b]++] = a;
        }
    }
    long total = 0;
    for (int r = 0; r < 2 * lk; r++) {
        int src = r * lG; /* representatives: vertex r*G is a representative of its class */
        if (++lstamp > 1000000000) {
            memset(lvis, 0, sizeof lvis);
            lstamp = 1;
        }
        int head = 0, tail = 0;
        lvis[src] = lstamp;
        lqueue[tail++] = src;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int u = lqueue[head++];
                for (int q = 0; q < ldeg[u]; q++) {
                    int v = ladj[u][q];
                    if (lvis[v] != lstamp) {
                        lvis[v] = lstamp;
                        lqueue[tail++] = v;
                    }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static void init_darts(int k) {
    for (int t = 0; t < d; t++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < k; i++) {
            cur_d[t * k + i].i = i;
            cur_d[t * k + i].j = perm[i];
            cur_d[t * k + i].s = rndint(lG);
        }
    }
}

/* Simulated annealing over voltages (and base permutations when k > 1) in the current group.
 * Returns 1 if a valid lift was found; its darts are then in best_d. */
static int sa_lift(int k, int G, int iters, double deadline) {
    lk = k;
    lG = G;
    nd_cur = d * k;
    init_darts(k);
    long cost = lift_cost();
    long bestc = cost;
    memcpy(best_d, cur_d, sizeof(Dart) * nd_cur);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && now() > deadline) break;
        double T = 3.0 * (1.0 - (double)it / iters) + 0.05;
        int undo_swap = 0, idx = 0, idx2 = 0, olds = 0;
        if (k > 1 && rndint(4) == 0) {
            int t = rndint(d);
            int i1 = rndint(k), i2 = rndint(k);
            if (i1 == i2) continue;
            idx = t * k + i1;
            idx2 = t * k + i2;
            int tmp = cur_d[idx].j;
            cur_d[idx].j = cur_d[idx2].j;
            cur_d[idx2].j = tmp;
            undo_swap = 1;
        } else {
            idx = rndint(nd_cur);
            olds = cur_d[idx].s;
            cur_d[idx].s = rndint(G);
        }
        long c2 = lift_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost < bestc) {
                bestc = cost;
                memcpy(best_d, cur_d, sizeof(Dart) * nd_cur);
            }
        } else if (undo_swap) {
            int tmp = cur_d[idx].j;
            cur_d[idx].j = cur_d[idx2].j;
            cur_d[idx2].j = tmp;
        } else {
            cur_d[idx].s = olds;
        }
    }
    return bestc == 0;
}

/* Build the explicit graph of the lift with darts dd, base size k, group order G (current group). */
static void build_lift_graph(Graph *g, int k, int G, const Dart *dd) {
    int N = 2 * k * G;
    g->n = N;
    for (int v = 0; v < N; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= k * G;
    }
    for (int t = 0; t < d * k; t++)
        for (int x = 0; x < G; x++)
            add_edge(g, dd[t].i * G + x, (k + dd[t].j) * G + gmul(x, dd[t].s));
}

/* Consecutive failures per base size k; widens the group-order search window. */
static int lift_fail[MAXK + 1];

static void lift_search(double until) {
    static Graph cand;
    long moore = moore_bound();
    while (now() < until) {
        if (best.n >= moore) return;
        int r = rndint(10);
        int k = r < 5 ? 1 : (r < 8 ? 2 : 3);
        long Gmin = (d + k - 1) / k;
        if (Gmin < 2) Gmin = 2;
        /* Smallest group order that makes the lift strictly larger than best. */
        long target = best.n / (2L * k) + 1;
        long spread = 2 + 3L * lift_fail[k];
        if (spread > 60) spread = 60;
        long G = target + rndint((int)spread);
        if (G < Gmin) G = Gmin + rndint(3);
        long cap = (moore < MAXN ? moore : MAXN) / (2L * k);
        if (G > cap) G = cap;
        if (G < Gmin) { lift_fail[k]++; continue; }
        int gm, gk, gr;
        if (!pick_group((int)G, &gm, &gk, &gr)) { lift_fail[k]++; continue; }
        set_group(gm, gk, gr);
        if (sa_lift(k, (int)G, LIFT_ITERS, until)) {
            build_lift_graph(&cand, k, (int)G, best_d);
            if (cand.n > best.n && is_valid(&cand)) {
                copy_graph(&best, &cand);
                lift_fail[k] = 0;
                continue;
            }
        }
        lift_fail[k]++;
    }
}

/* ------------------------------------------------------------------ grow by two */

static int grow_once(const Graph *base, Graph *work, double until) {
    int n = base->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, base);
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

static void grow_search(Graph *b, double until) {
    static Graph work;
    while (now() < until && b->n + 2 <= moore_bound() && b->n + 2 <= MAXN) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(b, &work, now() + slice)) copy_graph(b, &work);
    }
}

/* ------------------------------------------------------------------ main */

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

    if (d < 1 || D < 1 || d > MAXD) {
        printf("1 0\n");
        return 0;
    }
    if (D == 1) {
        printf("2 1\n0 1\n");
        return 0;
    }

    read_start(&best);
    if (d >= 3 && D >= 2) {
        lift_search(t0 + (t_end - t0) * 0.8);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d (q capped for speed)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _cycle(n):
    return n, [(i, (i + 1) % n) for i in range(n)]


def _candidates(d, D):
    """Algebraic starting graphs for (d, D); each is checked with lib.is_valid later."""
    out = [lib.haar_graph(d, range(d))]          # K_{d,d}: valid for D >= 2
    if d == 2:
        out.append(_cycle(2 * D))                # Moore graph for d = 2
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            out.append(pg)
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            out.append(gq)
    return out


def _best_valid(cands, d, D):
    best = None
    for n, e in cands:
        if (best is None or n > best[0]) and lib.is_valid(n, e, d, D):
            best = (n, e)
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    best = _best_valid(_candidates(d, D), d, D)
    if best is None:
        best = lib.haar_graph(d, range(d))

    moore = lib.moore_bound(d, D)
    if d < 3 or D < 2 or best[0] >= moore:
        return best

    budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
    if budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 5.0)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass
    return best
