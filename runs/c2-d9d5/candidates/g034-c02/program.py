"""Metacyclic voltage lifts for the bipartite degree-diameter problem.

This version replaces the affine-group (F_q x| C_c) search with a different family:
metacyclic groups G = Z_m x| Z_k, with r^k = 1 mod m, coded as a*k + b and multiplied
by (a, b)(c, e) = (a + r^b c, b + e). The family includes the affine groups of the
parent (for example F_251 x| C_5 is Z_251 x| Z_5) and also cyclic and other metacyclic
groups, so the search covers more group orders.

Construction: K left orbits and K right orbits, each left orbit with d darts (a, b, g):
L^a_x ~ R^b_{x g}. Each right orbit receives exactly d darts, so the graph is d-regular
and bipartite with 2KN vertices. Left translations are automorphisms that act
transitively on each orbit, so the diameter check needs only 2K BFS runs.

Stage A searches K = 1 (single bi-Cayley-type lift, 2N vertices) over metacyclic groups.
Stage B searches K = 2 (4N vertices) with the remaining time. The fallback chain
(K_{d,d}, projective planes, Araujo-Pardo-Lopez, W(q)) is kept, and every candidate
is checked with lib.is_valid before it is accepted.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Metacyclic multi-orbit voltage-lift search.
 * Group G = Z_m x| Z_k, r^k = 1 mod m, element a*k+b, (a,b)(c,e) = (a + r^b c, b+e).
 * Usage: prog d D seed time_limit lo hi K     (stdin ignored)
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
 * Vertices: left L^a_x = a*GN + x (a < K); right R^b_y = K*GN + b*GN + y.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXK 2
#define MAXD 32
#define MAXND (MAXK * MAXD)
#define MAXN 8192
#define MAXV (2 * MAXK * MAXN)
#define MAXCAND 200000

typedef struct { int m, k, r, N; } Cand;

static int K, d, D, GN, nd;
static int gm = 1, gk = 1;
static int RP[MAXN];            /* RP[b] = r^b mod gm */
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* ------------------------------------------------------------ group */

static void setup_group(int m, int k, int r) {
    gm = m;
    gk = k;
    GN = m * k;
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)(((long)RP[b - 1] * r) % m);
}

static inline int gmul(int x, int y) {
    int a = x / gk, b = x % gk, c = y / gk, e = y % gk;
    int na = (a + (int)(((long)RP[b] * c) % gm)) % gm;
    int nb = b + e;
    if (nb >= gk) nb -= gk;
    return na * gk + nb;
}

static inline int ginv(int x) {
    int a = x / gk, b = x % gk;
    int nb = (gk - b) % gk;
    int t = (int)(((long)RP[nb] * a) % gm);
    int na = (gm - t) % gm;
    return na * gk + nb;
}

/* ------------------------------------------------------------ voltage lift state */

static int tb[MAXND], vg[MAXND];                 /* dart target orbit, voltage */
static int fwdT[MAXND][MAXN], invT[MAXND][MAXN]; /* x*v and x*v^-1 */
static int inc_t[MAXK][MAXD];                    /* darts entering right orbit b */
static int cnt_in[MAXK];
static int bestTb[MAXND], bestVg[MAXND];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

/* Dart t leaves left orbit t/d: L_x ~ R^{tb[t]}_{x * v}. */
static void set_dart(int t, int v) {
    vg[t] = v;
    int iv = ginv(v);
    for (int x = 0; x < GN; x++) {
        fwdT[t][x] = gmul(x, v);
        invT[t][x] = gmul(x, iv);
    }
}

static void rebuild_inc(void) {
    for (int b = 0; b < K; b++) cnt_in[b] = 0;
    for (int t = 0; t < nd; t++) {
        int b = tb[t];
        if (cnt_in[b] < MAXD) inc_t[b][cnt_in[b]++] = t;
    }
}

/* Each right orbit receives exactly d darts. */
static void random_init(void) {
    int list[MAXND];
    int p = 0;
    for (int b = 0; b < K; b++)
        for (int i = 0; i < d; i++) list[p++] = b;
    for (int i = nd - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tmp = list[i]; list[i] = list[j]; list[j] = tmp;
    }
    for (int t = 0; t < nd; t++) tb[t] = list[t];
    rebuild_inc();
    for (int t = 0; t < nd; t++) set_dart(t, rndint(GN));
}

/* Darts in the same left orbit with equal target and voltage give a repeated edge. */
static long dup_count(void) {
    long c = 0;
    for (int t1 = 0; t1 < nd; t1++)
        for (int t2 = t1 + 1; t2 < nd; t2++)
            if (t1 / d == t2 / d && tb[t1] == tb[t2] && vg[t1] == vg[t2]) c++;
    return c;
}

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int V2 = K * GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < V2) {
                int a = v / GN, x = v % GN;
                for (int i = 0; i < d; i++) {
                    int t = a * d + i;
                    int u = V2 + tb[t] * GN + fwdT[t][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - V2;
                int b = w / GN, y = w % GN;
                for (int j = 0; j < d; j++) {
                    int t = inc_t[b][j];
                    int u = (t / d) * GN + invT[t][y];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* One BFS per orbit representative (2K total) decides the diameter, because
 * left translations are automorphisms acting transitively on each orbit. */
static long cover_cost(void) {
    long V = 2L * K * GN;
    long c = 0;
    for (int a = 0; a < K; a++) c += V - bfs_count(a * GN);
    for (int b = 0; b < K; b++) c += V - bfs_count(K * GN + b * GN);
    return c + 1000L * dup_count();
}

static void save_best(void) {
    memcpy(bestTb, tb, sizeof(int) * (size_t)nd);
    memcpy(bestVg, vg, sizeof(int) * (size_t)nd);
}

/* Simulated annealing over voltages (and target swaps when K > 1). */
static int search_group(double until, int iters) {
    while (now() < until) {
        random_init();
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            long c2;
            if (K > 1 && rnd01() < 0.3) {
                int t1 = rndint(nd), t2 = rndint(nd);
                if (tb[t1] == tb[t2]) continue;
                int tmp = tb[t1]; tb[t1] = tb[t2]; tb[t2] = tmp;
                rebuild_inc();
                c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    tmp = tb[t1]; tb[t1] = tb[t2]; tb[t2] = tmp;
                    rebuild_inc();
                }
            } else {
                int t = rndint(nd);
                int x = rndint(GN);
                if (x == vg[t]) continue;
                int old = vg[t];
                set_dart(t, x);
                c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else set_dart(t, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void print_result(void) {
    int V2 = K * GN;
    printf("%d %d\n", 2 * V2, V2 * d);
    for (int a = 0; a < K; a++)
        for (int x = 0; x < GN; x++)
            for (int i = 0; i < d; i++) {
                int t = a * d + i;
                int u = V2 + tb[t] * GN + fwdT[t][x];
                printf("%d %d\n", a * GN + x, u);
            }
}

/* ------------------------------------------------------------ candidates */

static Cand cand[MAXCAND];
static int nc = 0;

static int cmp_cand(const void *A, const void *B) {
    const Cand *x = (const Cand *)A, *y = (const Cand *)B;
    if (x->N != y->N) return x->N - y->N;
    if (x->m != y->m) return x->m - y->m;
    if (x->k != y->k) return x->k - y->k;
    return x->r - y->r;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return r;
}

static int gcd_(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    K = atoi(argv[7]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3 || K < 1 || K > MAXK) {
        printf("0 0\n");
        return 0;
    }
    nd = K * d;
    if (hi > MAXN) hi = MAXN;
    if (lo < 2) lo = 2;

    /* Metacyclic groups Z_m x| Z_k with N = m*k in [lo, hi]. */
    for (int k = 1; k <= hi; k++) {
        for (int m = 2; m * k <= hi; m++) {
            int N = m * k;
            if (N < lo) continue;
            int rmax = (k == 1) ? 2 : m;
            for (int r = 1; r < rmax; r++) {
                if (gcd_(r, m) != 1) continue;
                if (powmod(r, k, m) != 1) continue;
                if (nc < MAXCAND) {
                    Cand cd;
                    cd.m = m; cd.k = k; cd.r = r; cd.N = N;
                    cand[nc++] = cd;
                }
            }
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    int best_idx = -1, bestN = 0;

    /* Phase 1: binary search over the sorted candidate list, with a time slice per probe. */
    int li = 0, hi_i = nc - 1;
    while (li <= hi_i && now() < t_end) {
        int mid = (li + hi_i) / 2;
        double rem = t_end - now();
        double slice = rem * 0.25;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_group(cand[mid].m, cand[mid].k, cand[mid].r);
        if (search_group(now() + slice, 8000)) {
            if (cand[mid].N > bestN) {
                bestN = cand[mid].N;
                best_idx = mid;
                save_best();
            }
            li = mid + 1;
        } else {
            hi_i = mid - 1;
        }
    }

    /* Phase 2: spend leftover time on candidates above the best order. */
    int fails = 0;
    int idx = best_idx < 0 ? 0 : best_idx + 1;
    while (idx < nc && now() < t_end && fails < 3) {
        if (cand[idx].N <= bestN) { idx++; continue; }
        double rem = t_end - now();
        double slice = rem * 0.5;
        if (slice > rem) slice = rem;
        setup_group(cand[idx].m, cand[idx].k, cand[idx].r);
        if (search_group(now() + slice, 8000)) {
            bestN = cand[idx].N;
            best_idx = idx;
            save_best();
            idx++;
            fails = 0;
        } else {
            idx++;
            fails++;
        }
    }

    if (best_idx < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(cand[best_idx].m, cand[best_idx].k, cand[best_idx].r);
    memcpy(tb, bestTb, sizeof(int) * (size_t)nd);
    rebuild_inc();
    for (int t = 0; t < nd; t++) set_dart(t, bestVg[t]);
    print_result();
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
    """W(q) for the largest prime power q with q + 1 <= d (kept small for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _meta_search(d, D, seed, budget, lo, hi, K):
    """Run the metacyclic voltage-lift engine with K left and K right orbits; returns (n, edges)."""
    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi, K],
                     stdin_graph=None, timeout=budget + 8.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    def left():
        return time_limit - (time.monotonic() - t0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2 and is the safe fallback.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
        # Exact Moore graph: nothing can beat it.
        if D == 3 and lib.is_prime_power(d - 1) and best[0] > 2 * d:
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)

        # Stage A: single-orbit metacyclic lifts (2N vertices), the new family.
        budget = 0.6 * left() - 2.0
        lo = max(best[0] // 2 + 1, 2)
        hi = mb // 2
        if budget > 2.0 and lo <= hi:
            try:
                consider(_meta_search(d, D, seed, budget, lo, hi, 1))
            except Exception:
                pass

        # Stage B: two-orbit metacyclic lifts (4N vertices) with the remaining time.
        budget = 0.8 * left() - 2.0
        lo = max(best[0] // 4 + 1, 2)
        hi = mb // 4
        if budget > 2.0 and lo <= hi:
            try:
                consider(_meta_search(d, D, seed + 1, budget, lo, hi, 2))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
