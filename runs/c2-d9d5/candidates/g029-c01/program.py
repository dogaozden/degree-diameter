"""Semidirect-group multi-orbit voltage lifts for the bipartite degree-diameter problem.

Change from the parent: the group is no longer restricted to affine groups F_q x| C_c.
Each job uses a general semidirect product G = Z_m x|_r Z_k (elements (a, b) coded a*k+b,
product (a,b)(c,e) = (a + r^b c, b+e)), with K = 1, 2 or 3 left orbits and K right orbits.
Each dart (a, i) joins L^a_x to R^{t}_{x g} for a voltage g in G, so the graph has 2KN
vertices and is d-regular. Left translation by G is an automorphism that is transitive on
each orbit, so the diameter check needs only 2K BFS runs, one per orbit representative.

Search: C simulated annealing over voltages and dart-target swaps for a fixed job. Python
explores the job list (V = 2KN) with an exponential-then-bisection search over V, so it
probes near the frontier instead of sweeping every order. The fallbacks K_{d,d}, PG(2,q),
Araujo-Lopez and W(q) are kept, and every returned graph passes lib.is_valid.
"""
import bisect
import itertools
import math
import time

import numpy as np

import lib

MAXN_C = 4096

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
#define MAXK 3
#define MAXND (MAXK * MAXD)
#define MAXV (2 * MAXK * MAXN)
#define MAXGK 64

static int d, D, K, nd, GM, GK, GR, N;
static int rp[MAXGK];
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static int tb[MAXND], vg[MAXND];
static int fwdT[MAXND][MAXN], invT[MAXND][MAXN];
static int inc_t[MAXK][MAXD], cnt_in[MAXK];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* Element (a, b) is coded a*GK + b. Product (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int na = (int)(((long)a + (long)rp[b] * c) % GM);
    int nb = (b + e) % GK;
    return na * GK + nb;
}

/* Inverse of (a, b) is (-r^(-b) a, -b), and r^(-b) = r^(GK-b). */
static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int na = (int)((GM - ((long)rp[nb] * a) % GM) % GM);
    return na * GK + nb;
}

/* Dart t leaves left orbit t/d: L^a_x ~ R^{tb[t]}_{x g}. */
static void set_dart(int t, int g) {
    vg[t] = g;
    int ig = ginv(g);
    for (int x = 0; x < N; x++) {
        fwdT[t][x] = gmul(x, g);
        invT[t][x] = gmul(x, ig);
    }
}

static void rebuild_inc(void) {
    for (int b = 0; b < K; b++) cnt_in[b] = 0;
    for (int t = 0; t < nd; t++) {
        int b = tb[t];
        if (cnt_in[b] < d) inc_t[b][cnt_in[b]++] = t;
    }
}

/* Each right orbit receives exactly d darts, so the graph is d-regular. */
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
    for (int t = 0; t < nd; t++) set_dart(t, rndint(N));
}

/* Two darts from the same left orbit with the same target and voltage give a double edge. */
static long dup_count(void) {
    long c = 0;
    for (int t1 = 0; t1 < nd; t1++)
        for (int t2 = t1 + 1; t2 < nd; t2++)
            if (t1 / d == t2 / d && tb[t1] == tb[t2] && vg[t1] == vg[t2]) c++;
    return c;
}

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int V2 = K * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < V2) {
                int a = v / N, x = v % N;
                for (int i = 0; i < d; i++) {
                    int t = a * d + i;
                    int u = V2 + tb[t] * N + fwdT[t][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - V2;
                int b = w / N, y = w % N;
                for (int j = 0; j < d; j++) {
                    int t = inc_t[b][j];
                    int u = (t / d) * N + invT[t][y];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* One representative per orbit suffices (left translations are transitive on each orbit). */
static long cover_cost(void) {
    long V = 2L * K * N;
    long c = 0;
    for (int a = 0; a < K; a++) c += V - bfs_count(a * N);
    for (int b = 0; b < K; b++) c += V - bfs_count(K * N + b * N);
    return c + 1000L * dup_count();
}

static int search(double until) {
    const int iters = 5000;
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
                int g = rndint(N);
                if (g == vg[t]) continue;
                int old = vg[t];
                set_dart(t, g);
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
    printf("%d %d\n", 2 * K * N, K * N * d);
    for (int a = 0; a < K; a++)
        for (int x = 0; x < N; x++)
            for (int i = 0; i < d; i++) {
                int t = a * d + i;
                int u = K * N + tb[t] * N + fwdT[t][x];
                printf("%d %d\n", a * N + x, u);
            }
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    GM = atoi(argv[5]);
    GK = atoi(argv[6]);
    GR = atoi(argv[7]);
    K = atoi(argv[8]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 1 || K < 1 || K > MAXK || GM < 1 || GK < 1 || GK > MAXGK) {
        printf("0 0\n");
        return 0;
    }
    N = GM * GK;
    if (N > MAXN) {
        printf("0 0\n");
        return 0;
    }
    if (GR < 0 || GR >= GM) {
        printf("0 0\n");
        return 0;
    }
    rp[0] = 1 % GM;
    for (int b = 1; b < GK; b++) rp[b] = (int)((long)rp[b - 1] * GR % GM);
    if (((long)rp[GK - 1] * GR) % GM != 1 % GM) {
        printf("0 0\n");
        return 0;
    }
    if (gcd_i(GR, GM) != 1) {
        printf("0 0\n");
        return 0;
    }
    nd = K * d;
    if (search(t_end)) print_result();
    else printf("0 0\n");
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


def _semidirect_jobs(lo_v, hi_v):
    """Jobs (V, K, m, k, r) with V = 2*K*m*k in (lo_v, hi_v], for G = Z_m x|_r Z_k."""
    jobs = []
    for K in (1, 2, 3):
        lo_n = lo_v // (2 * K) + 1
        hi_n = min(hi_v // (2 * K), MAXN_C)
        if lo_n > hi_n:
            continue
        for k in range(1, 13):
            for m in range(max(1, -(-lo_n // k)), hi_n // k + 1):
                rs_list = [0] if m == 1 else [1]
                if m > 2 and k > 1:
                    x = np.arange(2, m, dtype=np.int64)
                    acc = x.copy()
                    for _ in range(k - 1):
                        acc = acc * x % m
                    ok = (acc == 1) & (np.gcd(x, m) == 1)
                    if ok.any():
                        rs_list.append(int(x[ok][0]))
                for r in rs_list:
                    jobs.append((2 * K * m * k, K, m, k, r))
    jobs.sort()
    return jobs


def _pick(Vs, tried, lo, hi, target):
    """Index of an untried job with lo < V < hi (hi may be None), nearest to target."""
    i0 = bisect.bisect_right(Vs, lo)
    j = max(bisect.bisect_left(Vs, target), i0)
    up = j
    while up < len(Vs) and up in tried:
        up += 1
    if up >= len(Vs) or (hi is not None and Vs[up] >= hi):
        up = None
    down = j - 1
    while down >= i0 and down in tried:
        down -= 1
    if down < i0:
        down = None
    if up is None:
        return down
    if down is None:
        return up
    return up if Vs[up] - target <= target - Vs[down] else down


def _semidirect_search(d, D, seed, remaining, best_n, mb):
    """Exponential-then-bisection search over the vertex count V; returns (n, edges) or None."""
    jobs = _semidirect_jobs(best_n, mb)
    if not jobs:
        return None
    Vs = [j[0] for j in jobs]
    tried = set()
    found = None
    lo_ok = best_n
    hi_bad = None
    step = 16
    trial = 0
    while True:
        rem = remaining()
        if rem < 5.0:
            break
        if hi_bad is None:
            target = lo_ok + step
        else:
            if hi_bad - lo_ok <= 2:
                break
            target = (lo_ok + hi_bad) // 2
        idx = _pick(Vs, tried, lo_ok, hi_bad, target)
        if idx is None:
            break
        tried.add(idx)
        V, K, m, k, r = jobs[idx]
        budget = min(rem - 2.5, max(2.5, min(6.0, rem / 3.0)))
        n, e = 0, []
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed * 1000 + trial, round(budget, 2), m, k, r, K],
                             stdin_graph=None, timeout=budget + 8.0)
            n, e = lib.parse_graph_text(text)
        except Exception:
            n = 0
        trial += 1
        if n == V and lib.is_valid(n, e, d, D):
            found = (n, e)
            lo_ok = V
            step *= 2
        else:
            hi_bad = V if hi_bad is None else min(hi_bad, V)
    return found


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    def remaining():
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
        if best[0] < mb:
            try:
                consider(_semidirect_search(d, D, seed, remaining, best[0], mb))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
