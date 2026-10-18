"""Generalised group voltage lifts for the bipartite degree-diameter problem.

New idea in this version: the parent only used affine groups F_q x| C_c, so its
group orders were q*c with q a prime power. This version searches ALL semidirect
products G = Z_m x|_r Z_k (element (a, b), product (a, b)(c, e) = (a + r^b c, b + e),
requiring gcd(r, m) = 1 and r^k = 1 mod m). This covers cyclic and abelian groups
(r = 1) and nonabelian ones, for every order N = m*k, so the feasible orders are
dense enough to hit values near record/4 and record/2.

Left and right orbits are as before: K left orbits, K right orbits, each right orbit
receives exactly d darts, the graph is d-regular and bipartite on 2KN vertices.
Left translations are automorphisms that act transitively on each orbit, so the
diameter test needs only 2K BFS runs. Phase 1 binary-searches the distinct orders
N; each probe tries every group of that order in turn. Phase 2 climbs above the
best order. Stage A runs K = 2, Stage B runs K = 1. The best valid graph is returned.
"""
import time

import lib

C_SOURCE = r'''
/* Semidirect-product voltage lift search with K left and K right orbits.
 * Usage: prog d D seed time_limit lo hi K     (stdin ignored)
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 * Vertices: left L^a_x = a*N + x (a < K), right R^b_y = K*N + b*N + y.
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
#define MAXK 2
#define MAXND (MAXK * MAXD)
#define MAXV (2 * MAXK * MAXN)
#define MAXCAND 60000
#define PER_MK 4

typedef struct { int m, k, r, N; } Cand;

static int K, d, D, GN, nd;
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

static int gcdi(int a, int b) {
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

/* ------------------------------------------------------------ group Z_m x|_r Z_k */

/* Element (a, b) is coded a*k + b. Product (a,b)(c,e) = (a + r^b c, b + e).
 * Inverse of (a,b) is (-r^(k-b) a, k-b), using r^k = 1 mod m. */
static int Mm, Kk, Rr;
static int powR[MAXN];

static void setup_group(int m, int k, int r) {
    Mm = m;
    Kk = k;
    Rr = r;
    GN = m * k;
    powR[0] = 1 % m;
    for (int b = 1; b < k; b++) powR[b] = (int)((long)powR[b - 1] * r % m);
}

static inline int gmul(int x, int y) {
    int a = x / Kk, b = x % Kk, c = y / Kk, e = y % Kk;
    int na = (int)(((long)a + (long)powR[b] * c) % Mm);
    int nb = (b + e) % Kk;
    return na * Kk + nb;
}

static inline int ginv(int x) {
    int a = x / Kk, b = x % Kk;
    int nb = (Kk - b) % Kk;
    int na = (int)((Mm - ((long)powR[nb] * a) % Mm) % Mm);
    return na * Kk + nb;
}

/* ------------------------------------------------------------ voltage lift state */

static int tb[MAXND], vg[MAXND];
static int fwdT[MAXND][MAXN], invT[MAXND][MAXN];
static int inc_t[MAXK][MAXD];
static int cnt_in[MAXK];
static int bestTb[MAXND], bestVg[MAXND];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

/* Dart t = a*d + i leaves left orbit a: L^a_x ~ R^{tb[t]}_{x * vg[t]}. */
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

/* Random regular assignment: each right orbit receives exactly d darts. */
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

/* Duplicate darts (same left orbit, same target, same voltage) give repeated edges. */
static long dup_count(void) {
    long c = 0;
    for (int t1 = 0; t1 < nd; t1++)
        for (int t2 = t1 + 1; t2 < nd; t2++)
            if (t1 / d == t2 / d && tb[t1] == tb[t2] && vg[t1] == vg[t2]) c++;
    return c;
}

/* Number of vertices reached within distance D of src. */
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

/* Left translations are automorphisms transitive on each orbit, so one BFS from
 * each orbit representative (2K in total) decides the diameter. */
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

/* Simulated annealing over dart targets (swaps) and voltages for the current group. */
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
            long c2;
            if (K > 1 && rnd01() < 0.4) {
                int t1 = rndint(nd), t2 = rndint(nd);
                if (tb[t1] == tb[t2]) continue;
                int tmp = tb[t1];
                tb[t1] = tb[t2];
                tb[t2] = tmp;
                rebuild_inc();
                c2 = cover_cost();
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

/* ------------------------------------------------------------ search over groups */

static Cand cand[MAXCAND];
static int dN[MAXCAND], dS[MAXCAND], dC[MAXCAND];
static int nD = 0;
static int best_group = -1;

/* Try every group of distinct order index di until one succeeds or time runs out. */
static int try_order(int di, double until) {
    int s = dS[di], c = dC[di];
    for (int j = 0; j < c && now() < until; j++) {
        double rem = until - now();
        double sl = rem / (double)(c - j);
        Cand *cd = &cand[s + j];
        setup_group(cd->m, cd->k, cd->r);
        if (search_group(now() + sl)) {
            best_group = s + j;
            save_best();
            return 1;
        }
    }
    return 0;
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

    /* All semidirect products Z_m x|_r Z_k of order N = m*k in [lo, hi], m >= 2.
     * r ranges over solutions of gcd(r,m)=1 and r^k = 1 mod m; up to PER_MK are kept
     * (r = 1 always first). Candidates come out sorted by N. */
    static int rl[MAXN];
    int nc = 0;
    for (int N = lo; N <= hi; N++) {
        for (int k = 1; k <= N / 2; k++) {
            if (N % k) continue;
            int m = N / k;
            int nr = 0;
            for (int r = 1; r < m; r++) {
                if (gcdi(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
                rl[nr++] = r;
            }
            int picks = nr < PER_MK ? nr : PER_MK;
            for (int j = 0; j < picks && nc < MAXCAND; j++) {
                cand[nc].m = m;
                cand[nc].k = k;
                cand[nc].r = rl[(long)j * nr / picks];
                cand[nc].N = N;
                nc++;
            }
        }
    }
    for (int i = 0; i < nc; ) {
        int j = i;
        while (j < nc && cand[j].N == cand[i].N) j++;
        dN[nD] = cand[i].N;
        dS[nD] = i;
        dC[nD] = j - i;
        nD++;
        i = j;
    }

    int bestDi = -1;
    int bestN = 0;

    /* Phase 1: binary search over distinct orders; each probe gets a share of time. */
    int li = 0, hiI = nD - 1;
    while (li <= hiI && now() < t_end) {
        int mid = (li + hiI) / 2;
        double rem = t_end - now();
        double sl = rem * 0.3;
        if (sl < 0.5) sl = 0.5;
        if (sl > rem) sl = rem;
        if (try_order(mid, now() + sl)) {
            bestDi = mid;
            bestN = dN[mid];
            li = mid + 1;
        } else {
            hiI = mid - 1;
        }
    }

    /* Phase 2: use leftover time on the orders just above the best. */
    int fails = 0;
    int idx = bestDi < 0 ? 0 : bestDi + 1;
    while (idx < nD && now() < t_end && fails < 2) {
        if (dN[idx] <= bestN) { idx++; continue; }
        double rem = t_end - now();
        double sl = rem * 0.5;
        if (sl > rem) sl = rem;
        if (try_order(idx, now() + sl)) {
            bestDi = idx;
            bestN = dN[idx];
            idx++;
            fails = 0;
        } else {
            idx++;
            fails++;
        }
    }

    if (best_group < 0) {
        printf("0 0\n");
        return 0;
    }
    Cand cd = cand[best_group];
    setup_group(cd.m, cd.k, cd.r);
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d (kept small for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _orbit_lift_search(d, D, seed, budget, lo, hi, K):
    """Run the C engine with K left and K right orbits; returns (n, edges)."""
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
        cap = 4096

        # Stage A: two-orbit lifts over semidirect products, 4|G| vertices.
        budget = 0.45 * left() - 2.0
        lo = max(best[0] // 4 + 1, 2)
        hi = min(mb // 4, cap)
        if budget > 2.0 and lo <= hi:
            try:
                consider(_orbit_lift_search(d, D, seed, budget, lo, hi, 2))
            except Exception:
                pass

        # Stage B: single-orbit lifts over semidirect products, 2|G| vertices.
        budget = 0.85 * left() - 2.0
        lo = max(best[0] // 2 + 1, 2)
        hi = min(mb // 2, cap)
        if budget > 2.0 and lo <= hi:
            try:
                consider(_orbit_lift_search(d, D, seed + 1, budget, lo, hi, 1))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
