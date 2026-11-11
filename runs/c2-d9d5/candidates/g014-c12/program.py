"""Multi-orbit voltage lifts over semidirect groups Z_m x|_r Z_k for the bipartite degree-diameter problem.

Change from the parent: instead of one Haar graph over the affine group F_q x| H, the C engine
searches lifts of a small base bipartite multigraph with a left orbits and a right orbits
(a in 1..4). The base is d-regular: it is a sum of d random permutation matrices, so every
left and right orbit has exactly d darts. Each dart (i, j, g) joins L_{i,x} to R_{j,x*g}.
Distinct voltages are required for each pair (i, j), which keeps the lift simple. Moves change
one voltage or swap the right endpoints of two darts, which preserves regularity.

Left translations act on each orbit, so the diameter check needs one BFS per orbit
(2a BFS runs). Groups are Z_m x|_r Z_k with r^k = 1 mod m and gcd(r, m) = 1. Orders are tried in
ascending order above the incumbent, each with an annealing budget.

Safe fallback: K_{d,d}, the projective-plane and Araujo-Pardo-Lopez constructions, and the
generalized quadrangle for D = 4. Every candidate is checked with lib.is_valid before it is kept.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit voltage lift search over Z_m x|_r Z_k.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo, hi bound the TOTAL vertex count 2*a*N.
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXA 4
#define MAXE (MAXA * MAXD)
#define MAXV 16384
#define MAXCAND 300000

typedef struct { int a, m, k, r, total; } Cand;

static int d, D;
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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* ------------------------------------------------------------ group Z_m x|_r Z_k */

static int GM, GK, GR, GN;
static int PWR[MAXV];

/* Element (a, b) is coded a*k + b. (a1,b1)(a2,b2) = (a1 + r^b1 a2, b1 + b2). */
static void set_group(int m, int k, int r) {
    GM = m; GK = k; GR = r; GN = m * k;
    int p = 1 % m;
    for (int b = 0; b < k; b++) {
        PWR[b] = p;
        p = (int)((long long)p * r % m);
    }
}

static inline int gmul(int x, int y) {
    int a1 = x / GK, b1 = x - a1 * GK;
    int a2 = y / GK, b2 = y - a2 * GK;
    int a = (int)(((long long)a1 + (long long)PWR[b1] * a2) % GM);
    int b = b1 + b2;
    if (b >= GK) b -= GK;
    return a * GK + b;
}

static inline int ginv(int x) {
    int a = x / GK, b = x - a * GK;
    int nb = (GK - b) % GK;
    long long t = (long long)PWR[nb] * a % GM;
    int na = (int)((GM - t) % GM);
    return na * GK + nb;
}

/* ------------------------------------------------------------ base multigraph state */

static int A_, E;
static int EI[MAXE], EJ[MAXE], EG[MAXE];
static int LJ[MAXA][MAXD], LG[MAXA][MAXD], RI[MAXA][MAXD], RG[MAXA][MAXD];

static void rebuild(void) {
    int cl[MAXA], cr[MAXA];
    for (int i = 0; i < A_; i++) cl[i] = cr[i] = 0;
    for (int k = 0; k < E; k++) {
        int i = EI[k], j = EJ[k];
        int t = cl[i]++;
        LJ[i][t] = j;
        LG[i][t] = EG[k];
        int s = cr[j]++;
        RI[j][s] = i;
        RG[j][s] = ginv(EG[k]);
    }
}

/* True if dart k with voltage g would duplicate another dart on the same (i, j) pair. */
static int conflict(int k, int g) {
    for (int q = 0; q < E; q++)
        if (q != k && EI[q] == EI[k] && EJ[q] == EJ[k] && EG[q] == g) return 1;
    return 0;
}

static int has_dup(void) {
    for (int p = 0; p < E; p++)
        for (int q = p + 1; q < E; q++)
            if (EI[p] == EI[q] && EJ[p] == EJ[q] && EG[p] == EG[q]) return 1;
    return 0;
}

/* Random d-regular base: d random permutation matrices, then distinct voltages per pair. */
static void random_base(void) {
    int idx = 0;
    int perm[MAXA];
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < A_; i++) perm[i] = i;
        for (int i = A_ - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        for (int i = 0; i < A_; i++) {
            EI[idx] = i;
            EJ[idx] = perm[i];
            EG[idx] = -1;
            idx++;
        }
    }
    for (int k = 0; k < E; k++) {
        int g;
        do { g = rndint(GN); } while (conflict(k, g));
        EG[k] = g;
    }
}

/* ------------------------------------------------------------ BFS cost */

static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

/* Vertices: left L_{i,x} = i*N + x; right R_{j,y} = AN + j*N + y, AN = a*N.
 * L_{i,x} ~ R_{j, x*g} for each dart (i, j, g). */
static int bfs_count(int src) {
    int N = GN, AN = A_ * GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < AN) {
                int i = v / N, x = v - i * N;
                for (int t = 0; t < d; t++) {
                    int u = AN + LJ[i][t] * N + gmul(x, LG[i][t]);
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int idx = v - AN;
                int j = idx / N, y = idx - j * N;
                for (int t = 0; t < d; t++) {
                    int u = RI[j][t] * N + gmul(y, RG[j][t]);
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Fibre transitivity: one source per orbit decides the diameter. */
static long cost_all(void) {
    int AN = A_ * GN, V = 2 * AN;
    long c = 0;
    for (int s = 0; s < 2 * A_; s++) {
        int src = s < A_ ? s * GN : AN + (s - A_) * GN;
        c += (long)(V - bfs_count(src));
    }
    return c;
}

/* ------------------------------------------------------------ iterated annealing */

/* Returns 1 with the solution left in EI/EJ/EG/LJ/... when cost 0 is reached, 0 on timeout. */
static int search_cand(double until) {
    const int iters = 6000;
    int have = 0;
    long bestc = 0;
    static int incI[MAXE], incJ[MAXE], incG[MAXE];
    while (now() < until) {
        if (!have) {
            random_base();
        } else {
            memcpy(EI, incI, sizeof(int) * (size_t)E);
            memcpy(EJ, incJ, sizeof(int) * (size_t)E);
            memcpy(EG, incG, sizeof(int) * (size_t)E);
            for (int t = 0; t < 2; t++) {
                int k = rndint(E), g;
                do { g = rndint(GN); } while (g == EG[k] || conflict(k, g));
                EG[k] = g;
            }
        }
        rebuild();
        long cost = cost_all();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            if (rnd01() < 0.8) {
                int k = rndint(E);
                int g = rndint(GN);
                if (g == EG[k] || conflict(k, g)) continue;
                int old = EG[k];
                EG[k] = g;
                rebuild();
                long c2 = cost_all();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    EG[k] = old;
                    rebuild();
                }
            } else {
                int k1 = rndint(E), k2 = rndint(E);
                if (EJ[k1] == EJ[k2]) continue;
                int tmp = EJ[k1]; EJ[k1] = EJ[k2]; EJ[k2] = tmp;
                if (has_dup()) {
                    tmp = EJ[k1]; EJ[k1] = EJ[k2]; EJ[k2] = tmp;
                    continue;
                }
                rebuild();
                long c2 = cost_all();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    tmp = EJ[k1]; EJ[k1] = EJ[k2]; EJ[k2] = tmp;
                    rebuild();
                }
            }
            if (cost == 0) return 1;
        }
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(incI, EI, sizeof(int) * (size_t)E);
            memcpy(incJ, EJ, sizeof(int) * (size_t)E);
            memcpy(incG, EG, sizeof(int) * (size_t)E);
        }
    }
    return 0;
}

static void print_result(void) {
    int N = GN, AN = A_ * N;
    printf("%d %d\n", 2 * AN, AN * d);
    for (int i = 0; i < A_; i++)
        for (int x = 0; x < N; x++)
            for (int t = 0; t < d; t++)
                printf("%d %d\n", i * N + x, AN + LJ[i][t] * N + gmul(x, LG[i][t]));
}

static int cmp_cand(const void *x, const void *y) {
    const Cand *p = x, *q = y;
    if (p->total != q->total) return p->total < q->total ? -1 : 1;
    return 0;
}

/* ------------------------------------------------------------ main */

static int bestTotal = 0;
static int bestA, bestM, bestK, bestR;
static int bestI[MAXE], bestJ[MAXE], bestG[MAXE];

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (lo < 2 * d) lo = 2 * d;
    if (hi > MAXV) hi = MAXV;
    if (lo > hi) { printf("0 0\n"); return 0; }

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int a = 1; a <= MAXA; a++) {
        int Nlo = (lo + 2 * a - 1) / (2 * a), Nhi = hi / (2 * a);
        if (Nlo < d) Nlo = d;
        for (int N = Nlo; N <= Nhi && nc < MAXCAND; N++) {
            for (int m = 1; m <= N && nc < MAXCAND; m++) {
                if (N % m) continue;
                int k = N / m;
                for (int r = 0; r < m; r++) {
                    if (m > 1 && r == 0) continue;
                    if (gcd_i(r, m) != 1) continue;
                    if (powmod(r, k, m) != 1 % m) continue;
                    if (nc >= MAXCAND) break;
                    Cand c;
                    c.a = a; c.m = m; c.k = k; c.r = r; c.total = 2 * a * N;
                    cand[nc++] = c;
                }
            }
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Ascending order above the incumbent: each attempt gets a share of the remaining time. */
    for (int ci = 0; ci < nc; ci++) {
        double rem = t_end - now();
        if (rem < 0.3) break;
        Cand *c = &cand[ci];
        if (c->total <= bestTotal) continue;
        double slice = 0.15 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        A_ = c->a;
        E = A_ * d;
        set_group(c->m, c->k, c->r);
        if (search_cand(now() + slice)) {
            bestTotal = c->total;
            bestA = A_; bestM = c->m; bestK = c->k; bestR = c->r;
            memcpy(bestI, EI, sizeof(int) * (size_t)E);
            memcpy(bestJ, EJ, sizeof(int) * (size_t)E);
            memcpy(bestG, EG, sizeof(int) * (size_t)E);
        }
    }

    if (bestTotal == 0) {
        printf("0 0\n");
        return 0;
    }
    A_ = bestA;
    E = A_ * d;
    set_group(bestM, bestK, bestR);
    memcpy(EI, bestI, sizeof(int) * (size_t)E);
    memcpy(EJ, bestJ, sizeof(int) * (size_t)E);
    memcpy(EG, bestG, sizeof(int) * (size_t)E);
    rebuild();
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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

    # Search: multi-orbit voltage lifts over Z_m x|_r Z_k, totals above the incumbent.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
        lo = max(best[0] + 2, mb // 8)
        hi = min(mb // 2, 16000)
        if budget > 2.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
