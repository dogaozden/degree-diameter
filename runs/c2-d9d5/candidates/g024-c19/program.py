"""Multi-base-vertex voltage lifts over small non-abelian groups for the bipartite degree-diameter problem.

Change in this version: the parent searched only single-base Haar graphs over one group. This
version builds lifts of a base graph with K vertices per side (K = 1..4). Each A-side base
vertex a has d darts, dart (a, i) goes to B-side base vertex (a+i) mod K, and each dart carries
a voltage s in a group G of order N. The lift has 2KN vertices and is d-regular and bipartite.
Distinct darts between the same base pair get distinct voltages, so the lift is simple.

Groups are G = Z_m x| Z_t (element (a,b) coded a*t+b, product (a+r^b c, b+e)), which covers
cyclic groups (t=1) and non-abelian groups. Left translation is an automorphism, so the
diameter is at most D iff the BFS ball of radius D around (v, identity) covers the graph for
each base vertex v. Simulated annealing on the voltages minimizes the total uncovered count.

Pool order: candidates (K, group) with order K*N in [mb//8, min(mb//2, 2040)], sorted by
K*N ascending, repeated passes with fresh random restarts. The Python side keeps the valid
fallbacks (projective plane, Araujo-Pardo-Lopez, generalized quadrangle, K_{d,d}) and checks
every returned graph with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-base voltage lift search.
 * Usage: prog d D seed time_limit Mlo Mhi     (stdin ignored)
 * A lift has 2*K*N vertices, where M = K*N is in [Mlo, Mhi].
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 2040
#define MAXN 2048
#define MAXK 4
#define MAXD 32
#define MAXDART (MAXK * MAXD)
#define MAXV (2 * MAXK * MAXN)
#define MAXCAND 400000

typedef struct { int k, N, m, t, r; } Cand;

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

/* ------------------------------------------------------------ group Z_m x| Z_t */

static int MUL[MAXN][MAXN];
static int INV[MAXN];
static int PWR[MAXN];
static int GN, GM, GT, GR;

/* Element (a,b) is coded a*t+b. Product (a,b)(c,e) = (a + r^b c, b+e). Identity is 0. */
static void setup_group(int m, int t, int r) {
    GM = m; GT = t; GR = r; GN = m * t;
    PWR[0] = 1 % m;
    for (int b = 1; b < t; b++) PWR[b] = (int)(((long)PWR[b - 1] * r) % m);
    for (int x = 0; x < GN; x++) {
        int a = x / t, b = x % t;
        for (int y = 0; y < GN; y++) {
            int c = y / t, e = y % t;
            int na = (int)(((long)a + (long)PWR[b] * c) % m);
            int ne = (b + e) % t;
            MUL[x][y] = na * t + ne;
        }
    }
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++)
            if (MUL[x][y] == 0) { INV[x] = y; break; }
}

/* ------------------------------------------------------------ base structure */

static int K, DEG;
static int sv[MAXDART], si[MAXDART];
static int incl[MAXK][MAXD];      /* darts entering B-vertex b */
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

/* Dart x = a*DEG + i goes from A-vertex a to B-vertex (a+i) mod K. */
static void setup_base(int k) {
    K = k; DEG = d;
    int cnt[MAXK];
    for (int b = 0; b < MAXK; b++) cnt[b] = 0;
    for (int a = 0; a < K; a++)
        for (int i = 0; i < DEG; i++) {
            int b = (a + i) % K;
            incl[b][cnt[b]++] = a * DEG + i;
        }
}

static void set_volt(int x, int s) {
    sv[x] = s;
    si[x] = INV[s];
}

/* Would voltage s on dart x clash with a parallel dart (same base pair)?
 * all=0 checks only earlier darts (used while initialising). */
static int conflicts(int x, int s, int all) {
    int a = x / DEG, i = x % DEG;
    for (int i2 = i % K; i2 < DEG; i2 += K) {
        if (i2 == i) continue;
        if (!all && i2 > i) break;
        if (sv[a * DEG + i2] == s) return 1;
    }
    return 0;
}

/* Vertices: A-vertex a, element g -> a*N+g; B-vertex b, element h -> (K+b)*N+h.
 * Lift edge for dart x: (a,g) -- (b, g*s). So B vertex (b,h) sees (a, h*s^-1). */
static int bfs_count(int src) {
    int N = GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int u = que[head++];
            int v = u / N, g = u - v * N;
            if (v < K) {
                for (int i = 0; i < DEG; i++) {
                    int x = v * DEG + i;
                    int b = (v + i) % K;
                    int w = (K + b) * N + MUL[g][sv[x]];
                    if (vis[w] != stamp_) { vis[w] = stamp_; que[tail++] = w; }
                }
            } else {
                int b = v - K;
                for (int j = 0; j < DEG; j++) {
                    int x = incl[b][j];
                    int a = x / DEG;
                    int w = a * N + MUL[g][si[x]];
                    if (vis[w] != stamp_) { vis[w] = stamp_; que[tail++] = w; }
                }
            }
        }
    }
    return tail;
}

/* Translation symmetry: diameter <= D iff each base vertex (v, identity) reaches everything. */
static long cover_cost(void) {
    long V = 2L * K * GN;
    long c = 0;
    for (int v = 0; v < 2 * K; v++)
        c += V - bfs_count(v * GN);
    return c;
}

/* Simulated annealing over the voltages. Returns 1 with a zero-cost assignment in sv, else 0. */
static int anneal(double until) {
    const int iters = 6000;
    int nd = K * DEG;
    while (now() < until) {
        for (int x = 0; x < nd; x++) {
            int s;
            do { s = rndint(GN); } while (conflicts(x, s, 0));
            set_volt(x, s);
        }
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int x = rndint(nd);
            int s;
            do { s = rndint(GN); } while (conflicts(x, s, 1) || s == sv[x]);
            int old = sv[x];
            set_volt(x, s);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_volt(x, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ candidates */

static Cand pool[MAXCAND];
static int np = 0;

static void add_cand(int k, int N, int m, int t, int r) {
    if (np >= MAXCAND) return;
    pool[np].k = k; pool[np].N = N; pool[np].m = m; pool[np].t = t; pool[np].r = r;
    np++;
}

static int gcd_i(int a, int b) {
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

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    long ma = (long)x->k * x->N, mb = (long)y->k * y->N;
    return (ma > mb) - (ma < mb);
}

static void print_solution(Cand c, const int *sol) {
    setup_group(c.m, c.t, c.r);
    setup_base(c.k);
    for (int x = 0; x < K * DEG; x++) set_volt(x, sol[x]);
    int N = GN;
    printf("%d %d\n", 2 * K * N, K * N * DEG);
    for (int a = 0; a < K; a++)
        for (int g = 0; g < N; g++)
            for (int i = 0; i < DEG; i++) {
                int b = (a + i) % K;
                printf("%d %d\n", a * N + g, (K + b) * N + MUL[g][sv[a * DEG + i]]);
            }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int Mlo = atoi(argv[5]), Mhi = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (Mhi > MAXM) Mhi = MAXM;
    if (Mlo < 2) Mlo = 2;
    if (Mlo > Mhi) { printf("0 0\n"); return 0; }

    /* Enumerate (K, group) pairs with K*N in [Mlo, Mhi], N >= 2d. */
    for (int k = 1; k <= MAXK; k++) {
        int Nlo = (Mlo + k - 1) / k, Nhi = Mhi / k;
        if (Nlo < 2 * d) Nlo = 2 * d;
        if (Nhi > MAXN) Nhi = MAXN;
        for (int N = Nlo; N <= Nhi; N++) {
            add_cand(k, N, N, 1, 1);                    /* cyclic Z_N */
            for (int t = 2; t <= N / 2; t++) {
                if (N % t) continue;
                int m = N / t;
                if (m < 2) continue;
                for (int r = 1; r < m; r++) {
                    if (gcd_i(r, m) != 1) continue;
                    if (powmod(r, t, m) != 1 % m) continue;
                    add_cand(k, N, m, t, r);
                }
            }
        }
    }
    if (np == 0) { printf("0 0\n"); return 0; }

    /* Shuffle, then sort by order ascending so near-threshold orders come first. */
    for (int i = np - 1; i > 0; i--) {
        int j = rndint(i + 1);
        Cand tmp = pool[i]; pool[i] = pool[j]; pool[j] = tmp;
    }
    qsort(pool, (size_t)np, sizeof(Cand), cmp_cand);

    double TT = t_end - now();
    double slice0 = TT / 12.0;
    if (slice0 < 0.5) slice0 = 0.5;
    if (slice0 > 8.0) slice0 = 8.0;

    int bestM = Mlo - 1;
    int have = 0, done = 0;
    Cand bestC;
    static int bestSol[MAXDART];
    for (int pass = 0; pass < 100000 && !done; pass++) {
        int tried = 0;
        for (int ci = 0; ci < np; ci++) {
            int M = pool[ci].k * pool[ci].N;
            if (M <= bestM) continue;
            double rem = t_end - now();
            if (rem < 0.2) { done = 1; break; }
            tried = 1;
            double slice = slice0;
            if (slice > rem) slice = rem;
            setup_group(pool[ci].m, pool[ci].t, pool[ci].r);
            setup_base(pool[ci].k);
            if (anneal(now() + slice)) {
                bestM = M;
                have = 1;
                bestC = pool[ci];
                for (int x = 0; x < K * DEG; x++) bestSol[x] = sv[x];
            }
        }
        if (!tried) break;
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    print_solution(bestC, bestSol);
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

    # Search: multi-base voltage lifts over Z_m x| Z_t, with M = K*N in [mb/8, min(mb/2, 2040)].
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(mb // 8, 2)
        hi = min(mb // 2, 2040)
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
