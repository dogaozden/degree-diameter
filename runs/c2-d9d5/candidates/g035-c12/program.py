"""Base-b voltage lifts over small semidirect groups for the bipartite degree-diameter problem.

Construction: let G = Z_m x|_r Z_k (r^k = 1 mod m, gcd(r, m) = 1; r = 1 gives the abelian
product). Take a base bipartite multigraph with B black and B white vertices, d darts at each
vertex (d random perfect matchings between the two sides, kept connected), and a voltage in G on
each dart. The lift has 2*B*|G| vertices: black (u, x) joins white (v, x*a) for each dart (u, v, a).
Voltages on parallel darts are distinct, so the lift is simple, bipartite and d-regular.

Left translation by G is an automorphism, so the diameter check needs only 2B BFS runs, one from
each base vertex at the identity. B = 1 is the Haar-lift family of the parent, so the search
still covers it. The new part is B = 2, 3 (multi-vertex bases), which the parent never tried.

Search: a task list of (group, B) pairs with orders above the current best. Each attempt picks a
task at random, half the time from orders within about 8% above the best so far, and runs
simulated annealing on the voltages with random restarts inside the attempt slice.

Safety: K_{d,d} and the algebraic constructions are computed first, and every returned graph
passes lib.is_valid before it is used.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Base-B voltage lift search over semidirect groups Z_m x|_r Z_k.
 * Usage: prog d D seed time_limit lo_order hi_order bmax   (stdin ignored)
 * Output: "n m" then m lines "u v" for the best valid lift found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 3200
#define MAXD 32
#define MAXB 3
#define MAXDART (MAXB * MAXD)
#define MAXV (2 * MAXB * MAXN)
#define MAXT 60000

typedef struct { int m, k, r, b; } Task;

static int d, D, B, N, nd;
static int *MT = NULL;      /* MT[x*N + y] = x*y in G */
static int *INVT = NULL;    /* INVT[x] = x^-1 */
static int bu[MAXDART], bv[MAXDART], vol[MAXDART];
static int wadj[MAXB * MAXD];          /* wadj[t*d + r] = dart index of the r-th dart at white t */
static int stampv[MAXV], queue_[MAXV];
static int stamp_ = 0;
static Task *tasks = NULL;
static int ntask = 0;
static uint64_t rs = 88172645463325252ULL;
static double t_end, t_start;

static int bestB, bestM, bestK, bestR;
static int bbu[MAXDART], bbv[MAXDART], bvol[MAXDART];

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

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long base, long e, long m) {
    long r = 1 % m;
    base %= m;
    while (e > 0) {
        if (e & 1) r = r * base % m;
        base = base * base % m;
        e >>= 1;
    }
    return r;
}

/* Group G = Z_m x|_r Z_k, element (a, b) coded a*k + b, identity 0.
 * (a, b)(c, e) = (a + r^b c, b + e). */
static void setup_group(int m, int k, int r) {
    N = m * k;
    free(MT);
    free(INVT);
    MT = (int *)malloc(sizeof(int) * (size_t)N * (size_t)N);
    INVT = (int *)malloc(sizeof(int) * (size_t)N);
    int *pw = (int *)malloc(sizeof(int) * (size_t)k);
    pw[0] = 1 % m;
    for (int i = 1; i < k; i++) pw[i] = (int)((long)pw[i - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            int na = (int)((a + (long)pw[b] * c) % m);
            int nb = (b + e) % k;
            MT[(size_t)x * N + y] = na * k + nb;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[(size_t)x * N + y] == 0) { INVT[x] = y; break; }
    free(pw);
}

static int base_connected(void) {
    int f[2 * MAXB];
    for (int i = 0; i < 2 * B; i++) f[i] = 0;
    f[0] = 1;
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int k = 0; k < nd; k++) {
            int a = bu[k], b = B + bv[k];
            if (f[a] != f[b]) { f[a] = 1; f[b] = 1; changed = 1; }
        }
    }
    for (int i = 0; i < 2 * B; i++)
        if (!f[i]) return 0;
    return 1;
}

/* d random perfect matchings between the B black and B white vertices. */
static void random_structure(void) {
    do {
        for (int r = 0; r < d; r++) {
            int perm[MAXB];
            for (int i = 0; i < B; i++) perm[i] = i;
            for (int i = B - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
            }
            for (int u = 0; u < B; u++) {
                int k = r * B + u;
                bu[k] = u;
                bv[k] = perm[u];
                wadj[perm[u] * d + r] = k;
            }
        }
    } while (!base_connected());
}

/* True if dart k with voltage x clashes with an earlier dart (index < lim) on the same base pair. */
static int conflict(int k, int x, int lim) {
    for (int k2 = 0; k2 < lim; k2++)
        if (k2 != k && bu[k2] == bu[k] && bv[k2] == bv[k] && vol[k2] == x) return 1;
    return 0;
}

/* Number of lift vertices within distance D of src. Black (u,x) has id u*N+x, white (t,y) has (B+t)*N+y. */
static int reach_count(int src) {
    int BN = B * N;
    stamp_++;
    int head = 0, tail = 0;
    queue_[tail++] = src;
    stampv[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = queue_[head++];
            if (v < BN) {
                int u = v / N, x = v % N;
                for (int r = 0; r < d; r++) {
                    int k = r * B + u;
                    int w = (B + bv[k]) * N + MT[x * N + vol[k]];
                    if (stampv[w] != stamp_) { stampv[w] = stamp_; queue_[tail++] = w; }
                }
            } else {
                int t = v / N - B, y = v % N;
                for (int r = 0; r < d; r++) {
                    int k = wadj[t * d + r];
                    int w = bu[k] * N + MT[y * N + INVT[vol[k]]];
                    if (stampv[w] != stamp_) { stampv[w] = stamp_; queue_[tail++] = w; }
                }
            }
        }
    }
    return tail;
}

/* Left translation is an automorphism, so the sources are (class, identity) for each base vertex. */
static long cost_eval(void) {
    long V = 2L * B * N;
    long c = 0;
    for (int s = 0; s < 2 * B; s++)
        c += V - reach_count(s * N);
    return c;
}

/* One random structure plus simulated annealing on the voltages. Returns 1 on diameter <= D. */
static int sa_run(double until, int iters) {
    random_structure();
    for (int k = 0; k < nd; k++) {
        int x;
        do { x = rndint(N); } while (conflict(k, x, k));
        vol[k] = x;
    }
    long cost = cost_eval();
    if (cost == 0) return 1;
    double Ts = 0.05 * (double)cost + 1.0, Te = 0.3;
    for (int it = 0; it < iters; it++) {
        if ((it & 31) == 0 && now() > until) return 0;
        double T = Ts * pow(Te / Ts, (double)it / iters);
        int k = rndint(nd);
        int x = rndint(N);
        if (x == vol[k] || conflict(k, x, nd)) continue;
        int old = vol[k];
        vol[k] = x;
        long c2 = cost_eval();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost == 0) return 1;
        } else {
            vol[k] = old;
        }
    }
    return 0;
}

static int attempt(double until, int iters) {
    while (now() < until) {
        if (sa_run(until, iters)) return 1;
    }
    return 0;
}

static void add_task(int m, int k, int r, int b) {
    if (ntask < MAXT) {
        tasks[ntask].m = m;
        tasks[ntask].k = k;
        tasks[ntask].r = r;
        tasks[ntask].b = b;
        ntask++;
    }
}

static void print_best(void) {
    B = bestB;
    nd = B * d;
    setup_group(bestM, bestK, bestR);
    memcpy(bu, bbu, sizeof(bu));
    memcpy(bv, bbv, sizeof(bv));
    memcpy(vol, bvol, sizeof(vol));
    int V = 2 * B * N, E = nd * N;
    printf("%d %d\n", V, E);
    for (int k = 0; k < nd; k++) {
        int u = bu[k], v = bv[k];
        for (int x = 0; x < N; x++)
            printf("%d %d\n", u * N + x, (B + v) * N + MT[x * N + vol[k]]);
    }
}

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long lo_order = atol(argv[5]);
    long hi_order = atol(argv[6]);
    int bmax = atoi(argv[7]);
    t_start = now();
    t_end = t_start + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2 || bmax < 1) {
        printf("0 0\n");
        return 0;
    }
    if (bmax > MAXB) bmax = MAXB;

    tasks = (Task *)malloc(sizeof(Task) * MAXT);
    for (int b = 1; b <= bmax; b++) {
        long twob = 2L * b;
        long nlo = (lo_order + twob - 1) / twob;
        long nhi = hi_order / twob;
        if (nhi > MAXN) nhi = MAXN;
        if (nlo < d) nlo = d;
        if (nlo < 2) nlo = 2;
        for (long m = 2; m <= nhi; m++) {
            for (long k = 1; m * k <= nhi; k++) {
                long Nn = m * k;
                if (Nn < nlo) continue;
                add_task((int)m, (int)k, 1, b);
                if (k >= 2) {
                    int extra = 0;
                    for (long r = 2; r < m && extra < 2; r++) {
                        if (gcd_int((int)r, (int)m) != 1) continue;
                        if (powmod(r, k, m) != 1) continue;
                        add_task((int)m, (int)k, (int)r, b);
                        extra++;
                    }
                }
            }
        }
    }
    if (ntask == 0) {
        printf("0 0\n");
        return 0;
    }

    long bestOrder = lo_order - 1;
    int found = 0;
    double slice_base = 0.15 * (t_end - t_start);
    if (slice_base < 0.8) slice_base = 0.8;

    while (1) {
        double rem = t_end - now();
        if (rem < 0.5) break;
        long lim_near = bestOrder + bestOrder / 12 + 2;
        int cnt_all = 0, cnt_near = 0;
        for (int t = 0; t < ntask; t++) {
            long ord = 2L * tasks[t].b * tasks[t].m * tasks[t].k;
            if (ord <= bestOrder) continue;
            cnt_all++;
            if (ord <= lim_near) cnt_near++;
        }
        if (cnt_all == 0) break;
        int use_near = (cnt_near > 0) && (rnd01() < 0.5);
        int want = use_near ? rndint(cnt_near) : rndint(cnt_all);
        int pick = -1;
        for (int t = 0; t < ntask && pick < 0; t++) {
            long ord = 2L * tasks[t].b * tasks[t].m * tasks[t].k;
            if (ord <= bestOrder) continue;
            if (use_near && ord > lim_near) continue;
            if (want == 0) pick = t;
            else want--;
        }
        if (pick < 0) break;

        Task T = tasks[pick];
        B = T.b;
        nd = B * d;
        setup_group(T.m, T.k, T.r);
        double slice = slice_base;
        if (slice > rem) slice = rem;
        if (attempt(now() + slice, 4000)) {
            bestOrder = 2L * B * N;
            bestB = B;
            bestM = T.m;
            bestK = T.k;
            bestR = T.r;
            memcpy(bbu, bu, sizeof(bu));
            memcpy(bbv, bv, sizeof(bv));
            memcpy(bvol, vol, sizeof(vol));
            found = 1;
        }
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    print_best();
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

    # New search: base-B voltage lifts over semidirect groups, aiming above the current best.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        lo_order = best[0] + 2
        hi_order = 2 * mb // 3
        if budget > 2.0 and lo_order <= hi_order:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo_order, hi_order, 3],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
