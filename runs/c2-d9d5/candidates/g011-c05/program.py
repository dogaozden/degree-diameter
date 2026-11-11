"""Semidirect-product voltage lifts with a shared group-descriptor sweep.

New idea in this version: every candidate group is a semidirect product
Z_m x|_r Z_k, passed to the C engine as a three-integer descriptor (m, k, r) with
multiplication (a,b)(c,e) = (a + r^b c, b + e). The C side never stores a
multiplication table, so one process can sweep thousands of groups cheaply.

The sweep covers several families per order N:
  * cyclic Z_N (the parent's Haar lifts),
  * abelian Z_(N/p) x Z_p for the smallest prime p | N,
  * dihedral-type Z_(N/2) x|_(-1) Z_2,
  * affine F_p x| Z_c (c | p-1, p = N/c prime), which contains the parent's affine family.

C binary-searches the sorted descriptor list for the largest feasible order, then
climbs upward. Lifts have K left and K right orbits, so the graph has 2KN vertices
(K = 1 uses order N, K = 2 uses 4N with N in the top quarter). Left translation is
an automorphism for every orbit, so diameter is checked with 2K BFS runs.
"""
import itertools
import math
import time

import lib

C_SOURCE = r'''
/* Semidirect-lift search, K left and K right orbits.
 * Usage: prog d D seed time_limit K
 * stdin: "1 M" then M/2 groups, each as two lines "m k" and "r 0" (sorted by m*k).
 * Output: "n m" then m lines "u v" for the largest valid lift found, or "0 0".
 * Vertices: left L^a_x = a*N + x, right R^b_y = K*N + b*N + y.
 * Group element x = a*k + b stands for (a, b) in Z_m x|_r Z_k.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 5000
#define MAXD 32
#define MAXK 2
#define MAXND (MAXK * MAXD)
#define MAXV (2 * MAXK * MAXN)

typedef struct { int m, k, r; } Desc;

static int d, D, KK, nd;
static int gm = 1, gk = 1, N = 1;
static int PW[MAXN + 1];
static int INVV[MAXN];
static double t_end;
static uint64_t rs = 88172645463325252ULL;
static int tb[MAXND], vg[MAXND];
static int bestTb[MAXND], bestVg[MAXND];
static int inc_t[MAXK][MAXD];
static int cnt_in[MAXK];
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

/* (a,b)(c,e) = (a + r^b c, b + e), coded as a*gk + b. */
static inline int gmul(int x, int y) {
    int a = x / gk, b = x - a * gk;
    int c = y / gk, e = y - c * gk;
    int na = (a + PW[b] * c) % gm;
    int nb = b + e;
    if (nb >= gk) nb -= gk;
    return na * gk + nb;
}

/* Inverse of (a,b) is (-r^{-b} a, -b), with r^{-b} = r^{(k-b) mod k}. */
static int ginv(int x) {
    int a = x / gk, b = x - a * gk;
    int nb = (gk - b) % gk;
    int c = (int)(((long)((gm - a) % gm) * PW[nb]) % gm);
    return c * gk + nb;
}

static void setup_group(int m, int k, int r) {
    gm = m;
    gk = k;
    N = m * k;
    PW[0] = 1 % m;
    for (int b = 1; b < k; b++) PW[b] = (int)((long)PW[b - 1] * r % m);
    for (int x = 0; x < N; x++) INVV[x] = ginv(x);
}

static int valid_desc(int m, int k, int r) {
    if (m < 2 || k < 1 || (long)m * k > MAXN) return 0;
    if (r < 1 || r >= m) return 0;
    int g = r, h = m;
    while (h) { int t = g % h; g = h; h = t; }
    if (g != 1) return 0;
    long x = 1 % m;
    for (int i = 0; i < k; i++) x = x * r % m;
    return x == 1 % m;
}

static void rebuild_inc(void) {
    for (int b = 0; b < KK; b++) cnt_in[b] = 0;
    for (int t = 0; t < nd; t++) {
        int b = tb[t];
        if (cnt_in[b] < MAXD) inc_t[b][cnt_in[b]++] = t;
    }
}

/* Each right orbit receives exactly d darts. */
static void random_init(void) {
    int perm[MAXND];
    int p = 0;
    for (int b = 0; b < KK; b++)
        for (int i = 0; i < d; i++) perm[p++] = b;
    for (int i = nd - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
    }
    for (int t = 0; t < nd; t++) tb[t] = perm[t];
    rebuild_inc();
    for (int t = 0; t < nd; t++) vg[t] = rndint(N);
}

static long dup_count(void) {
    long c = 0;
    for (int t1 = 0; t1 < nd; t1++)
        for (int t2 = t1 + 1; t2 < nd; t2++)
            if (t1 / d == t2 / d && tb[t1] == tb[t2] && vg[t1] == vg[t2]) c++;
    return c;
}

static int bfs_count(int src) {
    int V2 = KK * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < V2) {
                int a = v / N, x = v - a * N;
                for (int i = 0; i < d; i++) {
                    int t = a * d + i;
                    int u = V2 + tb[t] * N + gmul(x, vg[t]);
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - V2;
                int b = w / N, y = w - b * N;
                for (int j = 0; j < d; j++) {
                    int t = inc_t[b][j];
                    int u = (t / d) * N + gmul(y, INVV[vg[t]]);
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left translations are automorphisms transitive on each orbit, so one BFS per
 * orbit (2K total) decides the diameter. */
static long cover_cost(void) {
    long V = 2L * KK * N;
    long c = 0;
    for (int a = 0; a < KK; a++) c += V - bfs_count(a * N);
    for (int b = 0; b < KK; b++) c += V - bfs_count(KK * N + b * N);
    return c + 1000L * dup_count();
}

static void save_best(void) {
    memcpy(bestTb, tb, sizeof(int) * (size_t)nd);
    memcpy(bestVg, vg, sizeof(int) * (size_t)nd);
}

static int search_group(double until) {
    const int iters = 4000;
    while (now() < until) {
        random_init();
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            long c2;
            if (KK > 1 && rnd01() < 0.4) {
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
                int x = rndint(N);
                if (x == vg[t]) continue;
                int old = vg[t];
                vg[t] = x;
                c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else vg[t] = old;
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static int cmp_desc(const void *a, const void *b) {
    const Desc *x = a, *y = b;
    long nx = (long)x->m * x->k, ny = (long)y->m * y->k;
    return (nx > ny) - (nx < ny);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    KK = atoi(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3 || KK < 1 || KK > MAXK) {
        printf("0 0\n");
        return 0;
    }
    nd = KK * d;

    int hn, hm;
    if (scanf("%d %d", &hn, &hm) != 2) {
        printf("0 0\n");
        return 0;
    }
    int G = hm / 2;
    if (G <= 0) {
        printf("0 0\n");
        return 0;
    }
    Desc *desc = malloc(sizeof(Desc) * (size_t)G);
    int nlist = 0;
    for (int i = 0; i < G; i++) {
        int a, b, c, e;
        if (scanf("%d %d %d %d", &a, &b, &c, &e) != 4) break;
        if (valid_desc(a, b, c)) {
            desc[nlist].m = a;
            desc[nlist].k = b;
            desc[nlist].r = c;
            nlist++;
        }
    }
    if (nlist == 0) {
        printf("0 0\n");
        return 0;
    }
    qsort(desc, (size_t)nlist, sizeof(Desc), cmp_desc);

    int bi = -1, bestN = 0;
    double rem;

    /* Phase 1: binary search over the sorted descriptor list. */
    int li = 0, hiI = nlist - 1;
    while (li <= hiI && now() < t_end) {
        int mid = (li + hiI) / 2;
        rem = t_end - now();
        double slice = rem * 0.15;
        if (slice < 0.8) slice = 0.8;
        if (slice > rem) slice = rem;
        setup_group(desc[mid].m, desc[mid].k, desc[mid].r);
        if (search_group(now() + slice)) {
            if (N > bestN) {
                bestN = N;
                bi = mid;
                save_best();
            }
            li = mid + 1;
        } else {
            hiI = mid - 1;
        }
    }

    /* Phase 2: climb upward from the best feasible descriptor. */
    int fails = 0;
    int idx = bi < 0 ? 0 : bi + 1;
    while (idx < nlist && now() < t_end && fails < 6) {
        if (desc[idx].m * desc[idx].k <= bestN) {
            idx++;
            continue;
        }
        rem = t_end - now();
        double slice = rem * 0.25;
        if (slice > rem) slice = rem;
        setup_group(desc[idx].m, desc[idx].k, desc[idx].r);
        if (search_group(now() + slice)) {
            bestN = N;
            bi = idx;
            save_best();
            fails = 0;
        } else {
            fails++;
        }
        idx++;
    }

    if (bi < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(desc[bi].m, desc[bi].k, desc[bi].r);
    memcpy(tb, bestTb, sizeof(int) * (size_t)nd);
    memcpy(vg, bestVg, sizeof(int) * (size_t)nd);
    int V = 2 * KK * N;
    printf("%d %d\n", V, KK * N * d);
    for (int a = 0; a < KK; a++)
        for (int x = 0; x < N; x++)
            for (int i = 0; i < d; i++) {
                int t = a * d + i;
                int u = KK * N + tb[t] * N + gmul(x, vg[t]);
                printf("%d %d\n", a * N + x, u);
            }
    free(desc);
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


def _is_prime(n):
    return n >= 2 and all(n % f for f in range(2, int(n ** 0.5) + 1))


def _prim_root(p):
    """A primitive root modulo the odd prime p."""
    phi = p - 1
    fac = []
    x, f = phi, 2
    while f * f <= x:
        if x % f == 0:
            fac.append(f)
            while x % f == 0:
                x //= f
        f += 1
    if x > 1:
        fac.append(x)
    for g in range(2, p):
        if all(pow(g, phi // f, p) != 1 for f in fac):
            return g
    return 1


def _descriptors(N):
    """Semidirect descriptors (m, k, r) with m*k = N from several families."""
    out = [(N, 1, 1)]                       # cyclic Z_N
    divs = set()
    i = 1
    while i * i <= N:
        if N % i == 0:
            divs.add(i)
            divs.add(N // i)
        i += 1
    spf = min(f for f in divs if f >= 2)
    if spf < N:
        out.append((N // spf, spf, 1))      # abelian Z_(N/p) x Z_p
    if N % 2 == 0 and N // 2 >= 3:
        m = N // 2
        out.append((m, 2, m - 1))           # dihedral-type, r = -1
    for c in sorted(divs):
        if c < 2 or c >= N:
            continue
        p = N // c
        if p >= 3 and _is_prime(p) and (p - 1) % c == 0:
            g = _prim_root(p)
            out.append((p, c, pow(g, (p - 1) // c, p)))   # F_p x| Z_c, r of order c
    return out


def _lift_search(d, D, seed, budget, K, lo, hi):
    """Run the C sweep with K left and K right orbits; returns (n, edges) or None."""
    lo = max(lo, 2)
    hi = min(hi, 4999)
    if lo > hi or budget < 2.0:
        return None
    desc = []
    for N in range(lo, hi + 1):
        desc.extend(_descriptors(N))
    if not desc:
        return None
    pairs = []
    for m, k, r in desc:
        pairs += [(m, k), (r, 0)]
    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), K],
                     stdin_graph=(1, pairs), timeout=budget + 8.0)
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

        # Stage A: K = 1 semidirect lifts, 2N vertices, N just above best/2.
        budget = 0.6 * left() - 3.0
        if budget > 3.0:
            try:
                consider(_lift_search(d, D, seed, budget, 1,
                                      best[0] // 2 + 1, mb // 2))
            except Exception:
                pass

        # Stage B: K = 2 lifts, 4N vertices, with the remaining time.
        budget = left() - 4.0
        if budget > 3.0:
            try:
                consider(_lift_search(d, D, seed + 1, budget, 2,
                                      best[0] // 4 + 1, mb // 4))
            except Exception:
                pass

    return best
