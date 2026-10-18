"""Bold revision: an exact, fast C bi-Cayley engine replaces the Python lift search.

Construction: vertices are A_{i,x} and B_{j,x} for base blocks i, j < k and group
elements x of a semidirect group Z_m x| Z_k2 (order N, k*N vertices per side). Each
of the d layers is a perfect matching between A-blocks and B-blocks with a group
voltage, so the lift is d-regular and bipartite. Left translation is an automorphism,
so the diameter is at most D iff a BFS from each of the 2k block representatives
reaches all 2kN vertices within D. That check costs O(k * N * d) per move, far
cheaper than the all-pairs bitset check. C simulated annealing over layer
permutations and voltages searches for graphs of order just above the current best,
with the group order and base size k drawn at random. Output is validated exactly.
A grow-by-two annealing phase runs on the leftover time. The fallback K_{d,d} and
the exact PG(2,q), Araujo-Lopez and generalized-quadrangle constructions stay in place.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Bipartite degree-diameter search core (fast bi-Cayley annealing + grow).
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid start), or "0 0".
 * stdout: "n m" + edge lines, the largest valid graph found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 16
#define MAXK 6
#define MAXW (MAXN / 64)
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

/* Number of unordered pairs at distance > D (exact, bitset BFS). */
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

/* ---------------- semidirect group Z_m x|_r Z_k, element (a,b) = a*k+b ---------------- */

typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static Grp GG;

static void set_group(int m, int k, int r) {
    GG.m = m;
    GG.k = k;
    GG.r = r;
    GG.rp[0] = 1 % m;
    for (int b = 1; b < k; b++) GG.rp[b] = (int)((long)GG.rp[b - 1] * r % m);
}

/* (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int k = GG.k, m = GG.m;
    int a = x / k, b = x % k, c = y / k, e = y % k;
    long t = (a + (long)GG.rp[b] * c) % m;
    return (int)(t * k + (b + e) % k);
}

/* (a,b)^{-1} = (-r^{-b} a, -b). */
static int ginv(int x) {
    int k = GG.k, m = GG.m;
    int a = x / k, b = x % k;
    int nb = (k - b) % k;
    long ap = (m - ((long)GG.rp[nb] * a) % m) % m;
    return (int)(ap * k + nb);
}

static int cand_m[MAXN], cand_k[MAXN], cand_r[MAXN];

/* Pick a uniformly random group of order N from the family of semidirect products. */
static int pick_group(int N) {
    int cnt = 0;
    for (int m = 1; m <= N && cnt < MAXN; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            cand_m[cnt] = 1; cand_k[cnt] = k; cand_r[cnt] = 0; cnt++;
            continue;
        }
        for (int r = 1; r < m && cnt < MAXN; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cand_m[cnt] = m; cand_k[cnt] = k; cand_r[cnt] = r; cnt++;
        }
    }
    if (!cnt) return 0;
    int c = rndint(cnt);
    set_group(cand_m[c], cand_k[c], cand_r[c]);
    return 1;
}

/* ---------------- bi-Cayley lift state ---------------- */

static int KB, GN, NVt;                  /* base blocks per side, group order, vertices */
static int lperm[MAXD][MAXK];            /* layer l: A-block i matched to B-block lperm[l][i] */
static int linv[MAXD][MAXK];             /* layer l: B-block j matched to A-block linv[l][j] */
static int lvol[MAXD][MAXK];             /* layer l: voltage on A-block i */
static int NB[MAXN][MAXD];               /* neighbour of vertex v in layer l */
static int bfs_stamp[MAXN], bq[MAXN], bdist[MAXN];
static int bfs_clock = 0;
static double anneal_until;

/* A_{i,x} ~ B_{j, x*s}; B_{j,h} ~ A_{i, h*s^{-1}}. */
static void rebuild_layer(int l) {
    for (int i = 0; i < KB; i++) {
        int j = lperm[l][i], s = lvol[l][i];
        for (int x = 0; x < GN; x++)
            NB[i * GN + x][l] = (KB + j) * GN + gmul(x, s);
    }
    for (int j = 0; j < KB; j++) {
        int i = linv[l][j];
        int si = ginv(lvol[l][i]);
        for (int h = 0; h < GN; h++)
            NB[(KB + j) * GN + h][l] = i * GN + gmul(h, si);
    }
}

/* Sum over the 2K block representatives of vertices NOT within distance D. Zero iff diameter <= D
 * (left translations are automorphisms, so one representative per block suffices). */
static long eval_cost(void) {
    long cost = 0;
    for (int b = 0; b < 2 * KB; b++) {
        int src = b * GN;
        bfs_clock++;
        int head = 0, tail = 0;
        bq[tail++] = src;
        bfs_stamp[src] = bfs_clock;
        bdist[src] = 0;
        while (head < tail) {
            int v = bq[head++];
            if (bdist[v] >= D) continue;
            for (int l = 0; l < d; l++) {
                int u = NB[v][l];
                if (bfs_stamp[u] != bfs_clock) {
                    bfs_stamp[u] = bfs_clock;
                    bdist[u] = bdist[v] + 1;
                    bq[tail++] = u;
                }
            }
        }
        cost += NVt - tail;
    }
    return cost;
}

/* Number of parallel-edge clashes: same A-block, same B-block, same voltage in two layers. */
static long dupcount(void) {
    long dup = 0;
    for (int i = 0; i < KB; i++)
        for (int l = 0; l < d; l++)
            for (int q = 0; q < l; q++)
                if (lperm[l][i] == lperm[q][i] && lvol[l][i] == lvol[q][i]) dup++;
    return dup;
}

static void swap_perm(int l, int i1, int i2) {
    int t = lperm[l][i1];
    lperm[l][i1] = lperm[l][i2];
    lperm[l][i2] = t;
    linv[l][lperm[l][i1]] = i1;
    linv[l][lperm[l][i2]] = i2;
}

static int anneal(int iters, long patience) {
    NVt = 2 * KB * GN;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < KB; i++) perm[i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < KB; i++) {
            lperm[l][i] = perm[i];
            linv[l][perm[i]] = i;
            lvol[l][i] = rndint(GN);
        }
        rebuild_layer(l);
    }
    long cost = eval_cost() + PEN * dupcount();
    long best = cost, last = 0;
    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 7) == 0 && now() > anneal_until) break;
        if (t - last > patience) break;
        double frac = (double)t / (double)iters;
        double temp = 0.3 + 3.0 * (1.0 - frac);
        int l = rndint(d);
        if (KB >= 2 && rnd01() < 0.25) {
            int i1 = rndint(KB), i2 = rndint(KB - 1);
            if (i2 >= i1) i2++;
            swap_perm(l, i1, i2);
            rebuild_layer(l);
            long nc = eval_cost() + PEN * dupcount();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / temp)) {
                cost = nc;
            } else {
                swap_perm(l, i1, i2);
                rebuild_layer(l);
            }
        } else {
            int i = rndint(KB);
            int old = lvol[l][i];
            int nv = rndint(GN);
            if (nv == old) continue;
            lvol[l][i] = nv;
            rebuild_layer(l);
            long nc = eval_cost() + PEN * dupcount();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / temp)) {
                cost = nc;
            } else {
                lvol[l][i] = old;
                rebuild_layer(l);
            }
        }
        if (cost < best) { best = cost; last = t; }
    }
    return cost == 0;
}

/* Build the lifted graph from the current state; returns is_valid. */
static int build_candidate(Graph *g) {
    int half = KB * GN;
    g->n = NVt;
    for (int v = 0; v < NVt; v++) { g->deg[v] = 0; g->side[v] = v >= half; }
    for (int v = 0; v < half; v++)
        for (int l = 0; l < d; l++)
            add_edge(g, v, NB[v][l]);
    return is_valid(g);
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    long cap = moore_bound();
    if (cap > MAXN) cap = MAXN;
    long step = 2;
    int fails = 0;
    while (now() < until) {
        if (best->n + 2 > cap) return;
        long target = best->n + step;
        if (target > cap) target = cap;
        int k = 1 + rndint(MAXK);
        long N;
        for (;;) {
            N = (target + 2L * k - 1) / (2L * k);
            if (2L * k * N <= cap || k == 1) break;
            k--;
        }
        if (2L * k * N > cap) N = cap / (2L * k);
        if (N < 1) continue;
        if (rndint(2) && 2L * k * (N + 1) <= cap) N++;
        if (2L * k * N <= best->n) continue;
        if (!pick_group((int)N)) continue;
        KB = k;
        GN = (int)N;
        NVt = 2 * KB * GN;
        long iters = (long)(1e9 / (2.0 * KB * NVt * d + 1.0));
        if (iters < 2000) iters = 2000;
        if (iters > 300000) iters = 300000;
        anneal_until = until;
        int ok = anneal((int)iters, iters / 4 + 500);
        if (ok && build_candidate(&cand) && cand.n > best->n) {
            copy_graph(best, &cand);
            step = step + step / 2 + 2;
            fails = 0;
        } else {
            if (++fails >= 2) {
                fails = 0;
                step = step * 2 / 3;
                if (step < 2) step = 2;
            }
        }
    }
}

/* ---------------- grow-by-two annealing from the best graph ---------------- */

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
    while (now() < until && best->n + 2 <= moore_bound() && best->n + 2 <= MAXN) {
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
    if (d < 1 || d > MAXD || D < 1) {
        if (d >= 1 && d <= MAXD) { complete_bipartite(&best); print_graph(&best); }
        else printf("0 0\n");
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2) {
        lift_search(&best, t0 + (t_end - t0) * 0.8);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions (calibration cases return immediately).
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 3.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Replace the best graph if (n, e) is larger and valid."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # C engine: fast bi-Cayley annealing over semidirect groups, then grow-by-two.
    if D >= 2 and d <= 16:
        c_budget = end - time.monotonic() - 1.0
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=best, timeout=c_budget + 6)
                n_out, e_out = lib.parse_graph_text(text)
                consider(n_out, e_out)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
