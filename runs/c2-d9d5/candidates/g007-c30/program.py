"""Combined affine/semidirect voltage-lift search for the bipartite degree-diameter problem.

Merges the two parents' best ideas:
  * General K-orbit lifts (K = 1..4 left and right orbits, each right orbit receiving
    exactly d darts), so any regular dart assignment is allowed, not one fixed pattern.
  * Simulated annealing over dart targets (swaps) and voltages, with a duplicate-dart
    penalty so accepted states are simple graphs.
  * Left-translation symmetry: each orbit is transitive, so the diameter test needs
    only 2K BFS runs (from L^a_e and R^b_e).
  * Groups: semidirect products Z_m x| Z_k (element a*k+b, product (a,b)(c,e) =
    (a + r^b c, b+e), with r^k = 1 mod m). This covers cyclic, abelian and dihedral-type
    groups of every order N = m*k, not just the affine orders q*c. A fresh group and r
    are drawn at each restart.
  * Search over total vertex count 2KN: exponential probing upward from the best known
    order, then bisection between the last success and the first failure.

The C engine returns the largest valid graph it found. Python checks it with lib.is_valid
and keeps the Moore-type constructions as fallbacks.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit semidirect voltage lift search.
 * Usage: prog d D seed time_limit Vlo Vhi    (stdin ignored)
 * Searches (K, N) with Vlo <= 2KN <= Vhi, K in 1..4, group Z_m x| Z_k with m*k = N.
 * Vertices: left L^a_x = a*N + x (a < K), right R^b_y = K*N + b*N + y.
 * Dart t = a*d + i leaves left orbit a: L^a_x ~ R^{tb[t]}_{x * vg[t]}.
 * Output: "n m" then m lines "u v" for the largest graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXK 4
#define MAXD 32
#define MAXND (MAXK * MAXD)
#define MAXN 4800
#define MAXV (2 * MAXK * MAXN)
#define MAXCAND 24000
#define MAXDIV 512

typedef struct { int K, N; } Cand;

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

/* ------------------------------------------------------------ group Z_m x| Z_k */

static int GM, GK, GN, GR;
static int GPW[MAXN];   /* GPW[b] = r^b mod m */

static int powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return (int)r;
}

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GN = m * k;
    GR = r;
    GPW[0] = 1 % m;
    for (int b = 1; b < k; b++) GPW[b] = (GPW[b - 1] * r) % m;
}

/* Element a*k+b, product (a,b)(c,e) = (a + r^b c, b + e). */
static inline int gmul(int x, int y) {
    int a = x / GK, b = x - a * GK;
    int c = y / GK, e = y - c * GK;
    int na = (a + GPW[b] * c) % GM;
    int nb = b + e;
    if (nb >= GK) nb -= GK;
    return na * GK + nb;
}

/* Inverse of (a,b) is (-r^(-b) a, -b), with r^(-b) = r^(k-b). */
static inline int ginv(int x) {
    int a = x / GK, b = x - a * GK;
    int nb = (GK - b) % GK;
    int t = (GPW[nb] * a) % GM;
    int na = (GM - t) % GM;
    return na * GK + nb;
}

/* Random divisor k of N, m = N/k, and random r with gcd(r,m)=1, r^k = 1 mod m. */
static void pick_group(int N, int *mo, int *ko, int *ro) {
    int divs[MAXDIV];
    int nd_ = 0;
    for (int k = 1; k <= N && nd_ < MAXDIV; k++)
        if (N % k == 0) divs[nd_++] = k;
    int k = divs[rndint(nd_)];
    int m = N / k;
    if (m == 1) { *mo = 1; *ko = k; *ro = 0; return; }
    int valid[MAXN];
    int nv = 0;
    for (int r = 1; r < m; r++)
        if (gcd_int(r, m) == 1 && powmod(r, k, m) == 1) valid[nv++] = r;
    if (nv == 0) { *mo = m; *ko = k; *ro = 1; return; }
    *mo = m;
    *ko = k;
    *ro = valid[rndint(nv)];
}

/* ------------------------------------------------------------ lift state */

static int K, NK;                      /* NK = K*d darts */
static int tb[MAXND], vg[MAXND];       /* dart target orbit, voltage */
static int fwdT[MAXND][MAXN];          /* x * v */
static int bwdT[MAXND][MAXN];          /* y * v^-1 */
static int incT[MAXK][MAXD];           /* darts entering right orbit b */
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static void set_dart(int t, int x) {
    vg[t] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fwdT[t][g] = gmul(g, x);
        bwdT[t][g] = gmul(g, xi);
    }
}

static void rebuild_inc(void) {
    int cnt[MAXK];
    for (int b = 0; b < K; b++) cnt[b] = 0;
    for (int t = 0; t < NK; t++) {
        int b = tb[t];
        if (cnt[b] < d) incT[b][cnt[b]++] = t;
    }
}

/* Each right orbit receives exactly d darts, so the graph is d-regular. */
static void random_init(void) {
    int list[MAXND];
    int p = 0;
    for (int b = 0; b < K; b++)
        for (int i = 0; i < d; i++) list[p++] = b;
    for (int i = NK - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tmp = list[i]; list[i] = list[j]; list[j] = tmp;
    }
    for (int t = 0; t < NK; t++) tb[t] = list[t];
    rebuild_inc();
    for (int t = 0; t < NK; t++) set_dart(t, rndint(GN));
}

/* Darts of one left orbit with the same target and voltage give a parallel edge. */
static long dup_count(void) {
    long c = 0;
    for (int t1 = 0; t1 < NK; t1++)
        for (int t2 = t1 + 1; t2 < NK; t2++)
            if (t1 / d == t2 / d && tb[t1] == tb[t2] && vg[t1] == vg[t2]) c++;
    return c;
}

/* Number of vertices within distance D of s. */
static int bfs_reach(int s) {
    int N = GN, KN = K * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = s;
    vis[s] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < KN) {
                int a = v / N, x = v - a * N;
                for (int i = 0; i < d; i++) {
                    int t = a * d + i;
                    int u = KN + tb[t] * N + fwdT[t][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - KN, b = w / N, y = w - b * N;
                for (int j = 0; j < d; j++) {
                    int t = incT[b][j];
                    int u = (t / d) * N + bwdT[t][y];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left and right orbit representatives suffice (left translations are automorphisms
 * acting transitively on each orbit). Zero iff diameter <= D and the graph is simple. */
static long cover_cost(void) {
    int N = GN, V = 2 * K * N;
    long c = 0;
    for (int a = 0; a < K; a++) c += (long)(V - bfs_reach(a * N));
    for (int b = 0; b < K; b++) c += (long)(V - bfs_reach(K * N + b * N));
    return c + 1000L * dup_count();
}

/* ------------------------------------------------------------ best state */

static long bestV = 0;
static int bK, bm, bk, br;
static int bestTb[MAXND], bestVg[MAXND];

static void save_best(void) {
    long V = 2L * K * GN;
    if (V <= bestV) return;
    bestV = V;
    bK = K;
    bm = GM;
    bk = GK;
    br = GR;
    memcpy(bestTb, tb, sizeof(int) * (size_t)NK);
    memcpy(bestVg, vg, sizeof(int) * (size_t)NK);
}

/* Restarts with fresh random groups and assignments; simulated annealing inside.
 * Returns 1 with a cost-0 state (saved to best), 0 on timeout. */
static int search_cand(int Kc, int Nc, double until) {
    const int iters = 6000;
    K = Kc;
    NK = K * d;
    while (now() < until) {
        int m, k, r;
        pick_group(Nc, &m, &k, &r);
        set_group(m, k, r);
        random_init();
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            if (K > 1 && rnd01() < 0.4) {
                int t1 = rndint(NK), t2 = rndint(NK);
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
                int t = rndint(NK), x = rndint(GN);
                if (x == vg[t]) continue;
                int old = vg[t];
                set_dart(t, x);
                long c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else set_dart(t, old);
            }
        }
        if (cost == 0) {
            save_best();
            return 1;
        }
    }
    return 0;
}

/* ------------------------------------------------------------ candidates and phases */

static Cand cand[MAXCAND];
static int nc = 0;

static int cmp_cand(const void *pa, const void *pb) {
    const Cand *x = (const Cand *)pa, *y = (const Cand *)pb;
    long vx = 2L * x->K * x->N, vy = 2L * y->K * y->N;
    if (vx != vy) return vx < vy ? -1 : 1;
    return x->K - y->K;
}

static void build_cands(int Vlo, int Vhi) {
    nc = 0;
    for (int Kc = 1; Kc <= MAXK; Kc++) {
        int nlo = (Vlo + 2 * Kc - 1) / (2 * Kc);
        int nhi = Vhi / (2 * Kc);
        if (nlo < d) nlo = d;
        if (nlo < 2) nlo = 2;
        if (nhi > MAXN) nhi = MAXN;
        for (int N = nlo; N <= nhi && nc < MAXCAND; N++) {
            cand[nc].K = Kc;
            cand[nc].N = N;
            nc++;
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);
}

static int try_cand(int idx, double slice) {
    double rem = t_end - now();
    if (slice > rem) slice = rem;
    if (slice < 0.2) return 0;
    return search_cand(cand[idx].K, cand[idx].N, now() + slice);
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
    int Vlo = atoi(argv[5]), Vhi = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    build_cands(Vlo, Vhi);
    if (nc == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Phase 1: exponential probing upward in candidate index.
     * Invariant: lo_ok feasible (or -1), hi_bad infeasible (or nc). */
    int lo_ok = -1, hi_bad = nc, idx = 0, step = 1;
    while (now() < t_end && idx < hi_bad) {
        double rem = t_end - now();
        double slice = 0.15 * rem;
        if (slice < 2.0) slice = 2.0;
        if (try_cand(idx, slice)) {
            lo_ok = idx;
            if (idx == nc - 1) break;
            idx = idx + step;
            step *= 2;
            if (idx > nc - 1) idx = nc - 1;
        } else {
            hi_bad = idx;
            break;
        }
    }

    /* Phase 2: bisection between the last success and the first failure. */
    while (now() < t_end && lo_ok + 1 < hi_bad) {
        int mid = lo_ok + (hi_bad - lo_ok) / 2;
        double rem = t_end - now();
        double slice = 0.15 * rem;
        if (slice < 2.0) slice = 2.0;
        if (try_cand(mid, slice)) lo_ok = mid;
        else hi_bad = mid;
    }

    if (bestV == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Rebuild the best state and print it. */
    K = bK;
    NK = K * d;
    set_group(bm, bk, br);
    for (int t = 0; t < NK; t++) tb[t] = bestTb[t];
    for (int t = 0; t < NK; t++) set_dart(t, bestVg[t]);

    int N = GN, V = 2 * K * N, E = K * N * d;
    printf("%d %d\n", V, E);
    for (int a = 0; a < K; a++)
        for (int x = 0; x < N; x++)
            for (int i = 0; i < d; i++) {
                int t = a * d + i;
                int u = K * N + tb[t] * N + fwdT[t][x];
                printf("%d %d\n", a * N + x, u);
            }
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

    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.9 * time_limit - (time.monotonic() - t0) - 3.0
        vlo = best[0] + 1
        if budget > 2.0 and vlo <= mb:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), vlo, mb],
                                 stdin_graph=None, timeout=budget + 6.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
