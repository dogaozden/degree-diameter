"""Semidirect voltage lifts over Z_m x| Z_k for the bipartite degree-diameter problem.

New idea in this version: the parent's group family is affine F_q x| H with q a
prime power, so its group orders are sparse. This version searches the larger
family Z_m x|_r Z_k (r^k = 1 mod m, gcd(r, m) = 1). Each (m, k) contributes one
representative per element order of r, which keeps the candidate list small.
The family contains the parent's affine groups for prime q (the parent's 2510
graph is Z_251 x| Z_5, so it is included), and it has many more orders near the
record, so the search can step through every admissible order just above the
current best.

Engine: an ascending sweep over candidate orders N. Each order gets at most three
short probes; the first success raises the bar and later candidates must beat it.
Each probe is a simulated annealing over dart targets and voltages, scored by
cover cost. Diameter is checked from one BFS per orbit representative, which is
valid because left translations are transitive on each orbit.

Python runs a two-orbit stage (4N vertices) first, then a single-orbit stage
(2N vertices) with the remaining time. The best valid graph wins.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Semidirect voltage-lift sweep.
 * Usage: prog d D seed time_limit lo hi K [kmax]     (stdin ignored)
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 * Group G = Z_m x|_r Z_k, element a*k + b; (a,b)(c,e) = (a + r^b c, b + e).
 * Vertices: left L^a_x = a*N + x (a < K), right R^b_y = K*N + b*N + y.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 4800
#define MAXD 64
#define MAXK 2
#define MAXND (MAXK * MAXD)
#define MAXV (2 * MAXK * MAXG)
#define MAXCAND 300000
#define MAXRK 32
#define MAXTRY 3

typedef struct { int m, k, r, N; unsigned key; } Cand;

static int K, d, D, GN, GM, GK, nd;
static int PW[MAXRK];
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static Cand cand[MAXCAND];
static int ncand = 0;

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

/* ------------------------------------------------------------ group arithmetic */

static void setup_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GN = m * k;
    long x = 1 % m;
    for (int b = 0; b < k; b++) {
        PW[b] = (int)x;
        x = x * r % m;
    }
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int na = (int)((a + (long)PW[b] * c) % GM);
    int nb = b + e;
    if (nb >= GK) nb -= GK;
    return na * GK + nb;
}

static inline int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int na = (int)(((long)(GM - PW[nb]) % GM) * a % GM);
    return na * GK + nb;
}

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/* Smallest e >= 1 with r^e = 1 mod m, or -1 if none with e <= k. */
static int ordmod(int r, int m, int k) {
    long x = 1 % m;
    for (int e = 1; e <= k; e++) {
        x = x * r % m;
        if (x == 1 % m) return e;
    }
    return -1;
}

/* ------------------------------------------------------------ candidate enumeration */

static void add_cand(int m, int k, int r, int N) {
    if (ncand >= MAXCAND) return;
    cand[ncand].m = m;
    cand[ncand].k = k;
    cand[ncand].r = r;
    cand[ncand].N = N;
    cand[ncand].key = (unsigned)rnd();
    ncand++;
}

/* One candidate per (m, k, element order e of r): r and r' of equal order give
 * isomorphic groups when the unit group is cyclic (prime m). */
static void enumerate_groups(int lo, int hi, int kmax) {
    for (int k = 1; k <= kmax; k++) {
        int mlo = (lo + k - 1) / k, mhi = hi / k;
        if (mlo < 2) mlo = 2;
        for (int m = mlo; m <= mhi; m++) {
            int N = m * k;
            if (k == 1) {
                add_cand(m, 1, 1, N);
                continue;
            }
            unsigned char seen[MAXRK];
            memset(seen, 0, sizeof seen);
            for (int r = 1; r < m; r++) {
                if (gcd_i(r, m) != 1) continue;
                int e = ordmod(r, m, k);
                if (e < 0 || seen[e]) continue;
                seen[e] = 1;
                add_cand(m, k, r, N);
            }
        }
    }
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->N != y->N) return x->N < y->N ? -1 : 1;
    if (x->key != y->key) return x->key < y->key ? -1 : 1;
    return 0;
}

/* ------------------------------------------------------------ voltage lift state */

static int tb[MAXND], vg[MAXND];
static int fwdT[MAXND][MAXG], invT[MAXND][MAXG];
static int inc_t[MAXK][MAXD];
static int cnt_in[MAXK];
static int bestTb[MAXND], bestVg[MAXND];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

/* Dart t = a*d + i leaves left orbit a: L^a_g ~ R^{tb[t]}_{g * vg[t]}. */
static void set_dart(int t, int x) {
    vg[t] = x;
    int ix = ginv(x);
    for (int g = 0; g < GN; g++) {
        fwdT[t][g] = gmul(g, x);
        invT[t][g] = gmul(g, ix);
    }
}

static void rebuild_inc(void) {
    for (int b = 0; b < K; b++) cnt_in[b] = 0;
    for (int t = 0; t < nd; t++) {
        int b = tb[t];
        if (cnt_in[b] < MAXD) inc_t[b][cnt_in[b]++] = t;
    }
}

static void random_init(void) {
    int list[MAXND];
    int p = 0;
    for (int b = 0; b < K; b++)
        for (int i = 0; i < d; i++) list[p++] = b;
    for (int i = nd - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tmp = list[i];
        list[i] = list[j];
        list[j] = tmp;
    }
    for (int t = 0; t < nd; t++) tb[t] = list[t];
    rebuild_inc();
    for (int t = 0; t < nd; t++) set_dart(t, rndint(GN));
}

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
                    if (vis[u] != stamp_) {
                        vis[u] = stamp_;
                        que[tail++] = u;
                    }
                }
            } else {
                int w = v - V2;
                int b = w / GN, y = w % GN;
                for (int j = 0; j < d; j++) {
                    int t = inc_t[b][j];
                    int u = (t / d) * GN + invT[t][y];
                    if (vis[u] != stamp_) {
                        vis[u] = stamp_;
                        que[tail++] = u;
                    }
                }
            }
        }
    }
    return tail;
}

/* Left translations are automorphisms transitive on each orbit, so one BFS per
 * orbit representative decides the diameter. */
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

/* Simulated annealing with random restarts until the deadline. */
static int search_group(double until) {
    const int iters = 6000;
    while (now() < until) {
        random_init();
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            if (K > 1 && rnd01() < 0.4) {
                int t1 = rndint(nd), t2 = rndint(nd);
                if (tb[t1] == tb[t2]) continue;
                int tmp = tb[t1];
                tb[t1] = tb[t2];
                tb[t2] = tmp;
                rebuild_inc();
                long c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    tmp = tb[t1];
                    tb[t1] = tb[t2];
                    tb[t2] = tmp;
                    rebuild_inc();
                }
            } else {
                int t = rndint(nd);
                int x = rndint(GN);
                if (x == vg[t]) continue;
                int old = vg[t];
                set_dart(t, x);
                long c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else set_dart(t, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void print_result(void) {
    int V = 2 * K * GN;
    printf("%d %d\n", V, K * GN * d);
    for (int a = 0; a < K; a++)
        for (int x = 0; x < GN; x++)
            for (int i = 0; i < d; i++) {
                int t = a * d + i;
                int u = K * GN + tb[t] * GN + fwdT[t][x];
                printf("%d %d\n", a * GN + x, u);
            }
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
    int kmax = argc > 8 ? atoi(argv[8]) : 16;
    if (kmax < 1) kmax = 1;
    if (kmax > MAXRK - 1) kmax = MAXRK - 1;
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
    if (lo < 2) lo = 2;
    if (hi > MAXG) hi = MAXG;
    if (hi < lo) {
        printf("0 0\n");
        return 0;
    }

    enumerate_groups(lo, hi, kmax);
    qsort(cand, (size_t)ncand, sizeof(Cand), cmp_cand);

    /* Ascending sweep over admissible orders above the current best. */
    int bestN = 0, bm = 0, bk = 0, br = 0;
    int lastN = -1, tries = 0;
    for (int i = 0; i < ncand && now() < t_end; i++) {
        Cand c = cand[i];
        if (c.N <= bestN) continue;
        if (c.N != lastN) {
            lastN = c.N;
            tries = 0;
        }
        if (tries >= MAXTRY) continue;
        tries++;
        double rem = t_end - now();
        double slice = rem * 0.05;
        if (slice < 0.8) slice = 0.8;
        if (slice > 3.0) slice = 3.0;
        if (slice > rem) slice = rem;
        setup_group(c.m, c.k, c.r);
        if (search_group(now() + slice)) {
            bestN = c.N;
            bm = c.m;
            bk = c.k;
            br = c.r;
            save_best();
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(bm, bk, br);
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


def _orbit_search(d, D, seed, budget, lo, hi, K):
    """Run the semidirect sweep engine with K left and K right orbits; returns (n, edges)."""
    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi, K, 16],
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

        # Stage A: two-orbit semidirect lifts, 4N vertices, orders just above best/4.
        budget = 0.4 * left() - 2.0
        lo = max(best[0] // 4 + 1, 2)
        hi = min(mb // 4, 4800)
        if budget > 2.0 and lo <= hi:
            try:
                consider(_orbit_search(d, D, seed, budget, lo, hi, 2))
            except Exception:
                pass

        # Stage B: single-orbit semidirect lifts, 2N vertices, with the remaining time.
        budget = 0.92 * left() - 2.0
        lo = max(best[0] // 2 + 1, 2)
        hi = min(mb // 2, 4800)
        if budget > 2.0 and lo <= hi:
            try:
                consider(_orbit_search(d, D, seed + 1, budget, lo, hi, 1))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
