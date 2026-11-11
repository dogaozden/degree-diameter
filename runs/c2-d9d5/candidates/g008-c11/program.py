"""Mixed semidirect-product Haar lifts for the bipartite degree-diameter problem.

Construction change: the parent searched only F_p x| H (prime p, H of order c dividing p-1).
This version searches the full family of semidirect products Z_m x|_r Z_k, with
m*k = N, r^k = 1 (mod m), gcd(r, m) = 1, for every N in range. Each group gives the
bipartite Haar graph on G with L_g ~ R_{g s} for a d-element set S. Left translations act
transitively on each side, so diameter <= D reduces to two BFS runs (from L_e and R_e).

The C engine runs two phases in one process:
  1. A floor phase restricted to the affine candidates (prime m, k >= 2), which contains the
     parent's family, so the parent's order is reached again as a safe floor.
  2. A bold phase over all semidirect candidates above the current best order.
The Python side keeps the Projective-plane, Araujo-Lopez and W(q) constructions and the
K_{d,d} fallback, and validates every candidate with lib.is_valid.
"""
import itertools
import time

import lib

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
#define MAXCAND 400000

typedef struct { int m, k, r, N, aff; } Cand;

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

static long gcdl(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
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
static int is_prime(long n) {
    if (n < 2) return 0;
    for (long f = 2; f * f <= n; f++)
        if (n % f == 0) return 0;
    return 1;
}

/* ------------------------------------------------ group Z_m x|_r Z_k */

static int GM, GK, GR, GN;
static int PW[MAXN];

/* Element (a, b) is coded a*k + b. Product (a,b)(c,e) = (a + r^b c, b + e). */
static void setup_group(int m, int k, int r) {
    GM = m; GK = k; GR = r; GN = m * k;
    PW[0] = 1 % m;
    for (int b = 1; b < k; b++) PW[b] = (int)((long)PW[b - 1] * r % m);
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int na = (int)((a + (long)PW[b] * c) % GM);
    int nd = (b + e) % GK;
    return na * GK + nd;
}

static inline int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    long t = (long)PW[nb] * a % GM;
    int na = (int)((GM - t) % GM);
    return na * GK + nb;
}

/* ------------------------------------------------ Haar graph state */

static int S[MAXD], SI[MAXD];
static int FW[MAXD][MAXN], BW[MAXD][MAXN];
static int vis[2 * MAXN], que[2 * MAXN];
static int stamp_ = 0;

/* Vertices: L_g = g, R_h = N + h. L_g ~ R_{g s}, so R_h ~ L_{h s^-1}. */
static void set_s(int i, int x) {
    S[i] = x;
    SI[i] = ginv(x);
    for (int g = 0; g < GN; g++) {
        FW[i][g] = gmul(g, x);
        BW[i][g] = gmul(g, SI[i]);
    }
}

static int bfs_count(int src) {
    int N = GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int u = N + FW[i][v];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int h = v - N;
                for (int i = 0; i < d; i++) {
                    int u = BW[i][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Vertices not reached within D from L_e and from R_e (both sides transitive). */
static long cover_cost(void) {
    int V = 2 * GN;
    return (long)(V - bfs_count(0)) + (long)(V - bfs_count(GN));
}

static int in_S(int x, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == x) return 1;
    return 0;
}

/* Simulated annealing over S (size d) in the current group.
 * Returns 1 when cost 0 is reached, 0 on timeout. S then holds the solution. */
static int search_group(double until, int iters) {
    int N = GN;
    while (now() < until) {
        for (int i = 0; i < d; i++) {
            int x;
            do { x = rndint(N); } while (in_S(x, i));
            set_s(i, x);
        }
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(d);
            int x;
            do { x = rndint(N); } while (in_S(x, d));
            int old = S[i];
            set_s(i, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_s(i, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------ candidates */

static Cand cand[MAXCAND];
static int nc = 0;

static void gen_cands(int lo, int hi) {
    nc = 0;
    for (int N = lo; N <= hi; N++) {
        for (int k = 1; k <= N; k++) {
            if (N % k) continue;
            int m = N / k;
            if (m < 2) continue;
            for (int r = 1; r < m; r++) {
                if (gcdl(r, m) != 1) continue;
                if (powmod(r, k, m) != 1) continue;
                if (nc >= MAXCAND) return;
                cand[nc].m = m;
                cand[nc].k = k;
                cand[nc].r = r;
                cand[nc].N = N;
                cand[nc].aff = (k >= 2 && is_prime(m) && (m - 1) % k == 0);
                nc++;
            }
        }
    }
}

static void shuffle_cands(void) {
    for (int i = nc - 1; i > 0; i--) {
        int j = rndint(i + 1);
        Cand t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
}

static int cmp_N(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    return (x->N > y->N) - (x->N < y->N);
}

/* ------------------------------------------------ main */

static int bestN = 0, bestM = 0, bestK = 0, bestR = 0;
static int bestS[MAXD];

static void record_success(void) {
    bestN = GN;
    bestM = GM;
    bestK = GK;
    bestR = GR;
    memcpy(bestS, S, sizeof(int) * (size_t)d);
}

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
    if (hi > MAXN - 1) hi = MAXN - 1;
    if (lo < 2 * d) lo = 2 * d;
    if (lo > hi) { printf("0 0\n"); return 0; }

    gen_cands(lo, hi);
    shuffle_cands();
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_N);

    /* Phase 1: affine floor (prime m, k >= 2), as in the parent family. */
    double total = t_end - t0;
    double p1_end = t0 + 0.35 * total;
    for (int pass = 0; pass < 1000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            Cand c = cand[ci];
            if (!c.aff || c.N <= bestN) continue;
            double rem = p1_end - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = 0.2 * rem;
            if (slice < 1.0) slice = 1.0;
            if (slice > rem) slice = rem;
            setup_group(c.m, c.k, c.r);
            if (search_group(now() + slice, 6000)) record_success();
        }
        if (!tried || p1_end - now() < 0.3) break;
    }

    /* Phase 2: all semidirect candidates above the current best, ascending in N. */
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            Cand c = cand[ci];
            if (c.N <= bestN) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = 0.5;
            if (slice > rem) slice = rem;
            setup_group(c.m, c.k, c.r);
            if (search_group(now() + slice, 6000)) record_success();
        }
        if (!tried || t_end - now() < 0.3) break;
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(bestM, bestK, bestR);
    for (int i = 0; i < d; i++) set_s(i, bestS[i]);
    int N = GN;
    printf("%d %d\n", 2 * N, N * d);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + FW[i][g]);
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

    # Search: Haar graphs over Z_m x|_r Z_k (all semidirect candidates in range).
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] // 2 + 1, mb // 8)
        hi = min(mb // 4, 2400)
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
