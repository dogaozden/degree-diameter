"""Generic semidirect-product voltage lifts for the bipartite degree-diameter problem.

New idea in this version: the parent searched only affine groups F_q x| Z_c. This
version searches the wider family of metacyclic groups Z_M x|_r Z_KK, where
r^KK = 1 (mod M) and gcd(r, M) = 1. The group law is computed in C from (M, KK, r),
so no multiplication table crosses the pipe. Affine groups with prime q are special
cases (r of order c in Z_q^*), so the family contains the parent's graphs.

Each group gives a K-orbit lift. Left orbit a has d darts (a, b, g) with
L^a_x ~ R^b_{x g}; every right orbit receives exactly d darts, so the graph is
d-regular and bipartite. Left translations are automorphisms that are transitive on
every orbit, so the cover check needs only 2K BFS runs. Python sweeps group orders
upward from a lower anchor (a fixed fraction of the Moore bound), trying up to three
non-isomorphic twists per order (one representative per cyclic subgroup of Z_M^*).
Stage A uses K = 2 (4|G| vertices) and Stage B uses K = 1 (2|G| vertices). The
largest valid graph wins, with the Haar and projective-plane fallbacks kept.
"""
import itertools
import math
import random
import time

import lib

C_SOURCE = r'''
/* Metacyclic voltage-lift search over G = Z_M x|_r Z_KK.
 * Usage: prog d D seed time_limit M KK r K
 * Element (a, b) is coded a*KK + b; (a,b)(c,e) = (a + r^b c, b + e), indices mod (M, KK).
 * Output: "n m" then m lines "u v" for a valid lift, or "0 0".
 * Vertices: left L^a_x = a*GN + x, right R^b_y = K*GN + b*GN + y.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 40
#define MAXK 2
#define MAXND (MAXK * MAXD)
#define MAXG 5000
#define MAXV (2 * MAXK * MAXG)

static int K, d, D, M, KK, GN;
static int PW[MAXG];          /* PW[b] = r^b mod M */
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

static inline int gmul(int x, int y) {
    int a = x / KK, b = x % KK, c = y / KK, e = y % KK;
    long na = ((long)a + (long)PW[b] * (long)c) % M;
    int nb = (b + e) % KK;
    return (int)(na * KK + nb);
}

static int ginv(int x) {
    int a = x / KK, b = x % KK;
    int nb = (KK - b) % KK;
    long na = ((long)M - ((long)PW[nb] * (long)a) % M) % M;
    return (int)(na * KK + nb);
}

static int tb[MAXND], vg[MAXND];
static int fwdT[MAXND][MAXG], invT[MAXND][MAXG];
static int inc_t[MAXK][MAXD], cnt_in[MAXK];
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
    for (int t = 0; t < K * d; t++) {
        int b = tb[t];
        if (cnt_in[b] < MAXD) inc_t[b][cnt_in[b]++] = t;
    }
}

static void random_init(void) {
    int list[MAXND];
    int nd = K * d, p = 0;
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

static long dup_count(void) {
    long c = 0;
    int nd = K * d;
    for (int t1 = 0; t1 < nd; t1++)
        for (int t2 = t1 + 1; t2 < nd; t2++)
            if (t1 / d == t2 / d && tb[t1] == tb[t2] && vg[t1] == vg[t2]) c++;
    return c;
}

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
                for (int j = 0; j < cnt_in[b]; j++) {
                    int t = inc_t[b][j];
                    int u = (t / d) * GN + invT[t][y];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* One BFS per orbit suffices: left translations are transitive on each orbit. */
static long cover_cost(void) {
    long V = 2L * K * GN;
    long c = 0;
    for (int a = 0; a < K; a++) c += V - bfs_count(a * GN);
    for (int b = 0; b < K; b++) c += V - bfs_count(K * GN + b * GN);
    return c + 1000L * dup_count();
}

static int search_group(double until) {
    const int iters = 6000;
    int nd = K * d;
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
                int tmp = tb[t1]; tb[t1] = tb[t2]; tb[t2] = tmp;
                rebuild_inc();
                long c2 = cover_cost();
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
    int V = 2 * K * GN, E = K * GN * d;
    printf("%d %d\n", V, E);
    for (int a = 0; a < K; a++)
        for (int x = 0; x < GN; x++)
            for (int i = 0; i < d; i++) {
                int t = a * d + i;
                int u = K * GN + tb[t] * GN + fwdT[t][x];
                printf("%d %d\n", a * GN + x, u);
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
    M = atoi(argv[5]);
    KK = atoi(argv[6]);
    int r = atoi(argv[7]);
    K = atoi(argv[8]);
    t_end = now() + limit * 0.9 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3 || K < 1 || K > MAXK || M < 1 || KK < 1 ||
        (long)M * KK > MAXG) {
        printf("0 0\n");
        return 0;
    }
    GN = M * KK;
    r %= M;
    /* r must be a unit with r^KK = 1 (mod M). */
    {
        int g = r, h = M;
        while (h) { int t = g % h; g = h; h = t; }
        if (g != 1) { printf("0 0\n"); return 0; }
    }
    PW[0] = 1 % M;
    for (int b = 1; b < KK; b++) PW[b] = (int)((long)PW[b - 1] * r % M);
    if (((long)PW[KK - 1] * r) % M != 1 % M) {
        printf("0 0\n");
        return 0;
    }

    if (search_group(t_end)) print_result();
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


def _group_choices(N, rng):
    """Twisted metacyclic groups Z_M x|_r Z_KK of order N (KK <= 12), one per cyclic
    subgroup of units, shuffled; then direct products Z_M x Z_KK as fallbacks."""
    twisted, direct = [], []
    for KK in range(2, min(N, 12) + 1):
        if N % KK:
            continue
        M = N // KK
        if M < 2:
            continue
        seen = set()
        for r in range(2, M):
            if math.gcd(r, M) != 1 or pow(r, KK, M) != 1 % M:
                continue
            sub = frozenset(pow(r, i, M) for i in range(KK))
            if sub in seen:
                continue
            seen.add(sub)
            twisted.append((M, KK, r))
        direct.append((M, KK, 1))
    rng.shuffle(twisted)
    return twisted + direct


def _group_search(d, D, seed, budget, lo, hi, K, consider):
    """Sweep group orders N in [lo, hi] upward; for each N try a few twisted groups in C."""
    if budget <= 2.0 or lo > hi:
        return
    rng = random.Random(seed * 7919 + K)
    t_end = time.monotonic() + budget
    slice_ = max(0.8, budget / 25.0)
    N = lo
    while N <= hi:
        if time.monotonic() > t_end - 1.0:
            break
        choices = _group_choices(N, rng)[:3]
        for M, KK, r in choices:
            rem = t_end - time.monotonic()
            if rem < 1.0:
                break
            s = min(slice_, rem)
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed + N, round(s, 2), M, KK, r, K],
                                 stdin_graph=None, timeout=s + 8.0)
                n, e = lib.parse_graph_text(text)
            except Exception:
                continue
            if n > 0:
                consider((n, e))
                break
        N += 1


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
        # Lower starting point: a fixed fraction of the Moore bound (keeps the climb short).
        anchor = int(0.26 * mb)

        # Stage A: two-orbit lifts, 4|G| vertices.
        budget = 0.25 * left() - 2.0
        lo = max(best[0] // 4 + 1, anchor // 4, 2)
        hi = min(mb // 4, 1200)
        if budget > 2.0 and lo <= hi:
            try:
                _group_search(d, D, seed, budget, lo, hi, 2, consider)
            except Exception:
                pass

        # Stage B: single-orbit lifts, 2|G| vertices, with most of the remaining time.
        budget = 0.85 * left() - 2.0
        lo = max(best[0] // 2 + 1, anchor // 2, 2)
        hi = min(mb // 2, 4900)
        if budget > 2.0 and lo <= hi:
            try:
                _group_search(d, D, seed + 1, budget, lo, hi, 1, consider)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
