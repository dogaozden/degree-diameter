"""Two-orbit affine-group lifts for the bipartite degree-diameter problem.

New idea in this version: a block lift with K = 2 orbits on each side.

Let G = F_q x| H be the affine group (H = subgroup of F_q^* of order c, N = q*c).
The graph has left orbits L^a (a = 0, 1) and right orbits R^b, each a copy of G, so
n = 4N. A dart (a, k) with target orbit b and shift s joins L^a_g to R^b_{g s}.
The dart pattern is the 2x2 block matrix [[x, d-x], [d-x, x]], so every left and right
orbit has degree d. Within one left orbit, the shifts that go to the same right orbit
are distinct, so the graph is simple.

Left translations are automorphisms, so each orbit is vertex-transitive. The diameter
test therefore needs only 2K BFS runs, one from a representative of each orbit.

This gives orders 4N, which are much finer than the single-orbit orders 2N. So the
search can reach totals just above the incumbent with groups that single-orbit lifts
cannot use. The C engine considers K = 2 and K = 1 candidates in ascending order of
total order. Each one is annealed from the incumbent connection pattern, with fresh
restarts on some rounds.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Two-orbit affine-group lift search.
 * Usage: prog d D seed time_limit lo hi
 * Accepts total vertex counts n = 2*K*N with K in {1,2}, lo < n <= hi.
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 256
#define MAXC 256
#define MAXN 4096
#define MAXD 32
#define MAXK 2
#define MAXV (2 * MAXK * MAXN)
#define MAXCAND 16384

typedef struct { int q, p, k, c, N, K, n; } Cand;

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

/* ------------------------------------------------------------ finite fields */

static int ADDT[MAXQ][MAXQ], MULT[MAXQ][MAXQ], NEGT[MAXQ];
static int built_q = -1;

static int factor_pp(int q, int *p, int *k) {
    int pp = 0;
    for (int f = 2; f * f <= q; f++)
        if (q % f == 0) { pp = f; break; }
    if (!pp) pp = q;
    int r = q, kk = 0;
    while (r % pp == 0) { r /= pp; kk++; }
    if (r != 1 || kk < 1) return 0;
    *p = pp;
    *k = kk;
    return 1;
}

static int polymul(int a, int b, int p, int k, const int *pw, const int *m) {
    int pa[16], pb[16], prod[32];
    for (int i = 0; i < k; i++) {
        pa[i] = (a / pw[i]) % p;
        pb[i] = (b / pw[i]) % p;
    }
    for (int i = 0; i < 2 * k; i++) prod[i] = 0;
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            prod[i + j] = (prod[i + j] + pa[i] * pb[j]) % p;
    for (int deg = 2 * k - 2; deg >= k; deg--) {
        int c = prod[deg];
        if (!c) continue;
        for (int i = 0; i < k; i++) {
            int idx = deg - k + i;
            prod[idx] = ((prod[idx] - c * m[i]) % p + p) % p;
        }
        prod[deg] = 0;
    }
    int r = 0;
    for (int i = 0; i < k; i++) r += prod[i] * pw[i];
    return r;
}

static void build_field(int q, int p, int k) {
    if (built_q == q) return;
    int pw[16];
    pw[0] = 1;
    for (int i = 1; i <= k; i++) pw[i] = pw[i - 1] * p;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            int r = 0;
            for (int i = 0; i < k; i++)
                r += (((a / pw[i]) % p + (b / pw[i]) % p) % p) * pw[i];
            ADDT[a][b] = r;
        }
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            if (ADDT[a][b] == 0) NEGT[a] = b;

    int found = 0;
    for (int code = 0; code < q && !found; code++) {
        int m[16];
        int t = code;
        for (int i = 0; i < k; i++) { m[i] = t % p; t /= p; }
        int ok = 1;
        for (int a = 1; a < q && ok; a++)
            for (int b = 1; b < q && ok; b++)
                if (polymul(a, b, p, k, pw, m) == 0) ok = 0;
        if (ok) {
            found = 1;
            for (int a = 0; a < q; a++)
                for (int b = 0; b < q; b++)
                    MULT[a][b] = polymul(a, b, p, k, pw, m);
        }
    }
    built_q = q;
}

/* ------------------------------------------------------------ group G = F_q x| H */

static int GQ, GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Element (a, h_j) is coded a*c + j, with h_j = g^(j*(q-1)/c). */
static void setup_group(int q, int p, int k, int c) {
    build_field(q, p, k);
    GQ = q;
    GC = c;
    GN = q * c;
    int g = -1;
    for (int g0 = 2; g0 < q && g < 0; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) g = g0;
    }
    PWG[0] = 1;
    for (int i = 1; i < q - 1; i++) PWG[i] = MULT[PWG[i - 1]][g];
    int step = (q - 1) / c;
    for (int j = 0; j < q; j++) hidx[j] = -1;
    for (int t = 0; t < c; t++) {
        Hel[t] = PWG[(t * step) % (q - 1)];
        hidx[Hel[t]] = t;
    }
    for (int j = 0; j < c; j++)
        for (int t = 0; t < c; t++)
            HM[j * c + t] = hidx[MULT[Hel[j]][Hel[t]]];
}

static inline int gmul(int x, int y) {
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static int ginv(int x) {
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

/* ------------------------------------------------------------ block lift state */

/* Left orbit a, element g -> vertex a*N + g.
 * Right orbit b, element h -> vertex K*N + b*N + h.
 * Dart (a,k) goes to right orbit DBt[a][k] with shift DS[a][k]:
 * L^a_g ~ R^b_{g*s}. Right vertex R^b_h ~ L^a_{h*s^-1}. */
static int K_ = 1, N_ = 1;
static int DBt[MAXK][MAXD];
static int DS[MAXK][MAXD];
static int DSi[MAXK][MAXD];
static int fwd[MAXK][MAXD][MAXN];
static int bwdv[MAXK][MAXD][MAXN];
static int incA[MAXK][MAXD], incK[MAXK][MAXD];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static int incDBt[MAXK][MAXD], incDS[MAXK][MAXD];
static int solDBt[MAXK][MAXD], solDS[MAXK][MAXD];
static int solK = 1, solN = 1, solCi = -1;

static void set_dart(int a, int k, int x) {
    DS[a][k] = x;
    DSi[a][k] = ginv(x);
    for (int g = 0; g < N_; g++) {
        fwd[a][k][g] = gmul(g, x);
        bwdv[a][k][g] = gmul(g, DSi[a][k]);
    }
}

/* Block pattern: K = 1 gives all d darts to orbit 0. K = 2 gives
 * [[x, d-x], [d-x, x]], so every left and right orbit has degree d. */
static void build_inc(void) {
    for (int b = 0; b < K_; b++) {
        int j = 0;
        for (int a = 0; a < K_; a++)
            for (int k = 0; k < d; k++)
                if (DBt[a][k] == b) { incA[b][j] = a; incK[b][j] = k; j++; }
    }
}

static void build_struct(int x) {
    for (int a = 0; a < K_; a++)
        for (int k = 0; k < d; k++) {
            int b = 0;
            if (K_ == 2) {
                if (a == 0) b = (k < x) ? 0 : 1;
                else b = (k < d - x) ? 0 : 1;
            }
            DBt[a][k] = b;
            DS[a][k] = -1;
        }
    build_inc();
}

/* Shift y conflicts if another dart of the same left orbit to the same right orbit has it. */
static int conflict(int a, int k, int y) {
    for (int k2 = 0; k2 < d; k2++)
        if (k2 != k && DBt[a][k2] == DBt[a][k] && DS[a][k2] == y) return 1;
    return 0;
}

static void random_dart(int a, int k) {
    int y;
    do { y = rndint(N_); } while (conflict(a, k, y));
    set_dart(a, k, y);
}

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int N = N_, K = K_;
    int base = K * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < base) {
                int a = v / N, g = v - a * N;
                for (int k = 0; k < d; k++) {
                    int u = base + DBt[a][k] * N + fwd[a][k][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int r = v - base;
                int b = r / N, h = r - b * N;
                for (int j = 0; j < d; j++) {
                    int a = incA[b][j], k = incK[b][j];
                    int u = a * N + bwdv[a][k][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Orbit transitivity: one BFS per orbit representative decides the diameter. */
static long cover_cost(void) {
    int V = 2 * K_ * N_;
    long c = 0;
    for (int a = 0; a < K_; a++) c += (long)(V - bfs_count(a * N_));
    for (int b = 0; b < K_; b++) c += (long)(V - bfs_count(K_ * N_ + b * N_));
    return c;
}

static void save_solution(void) {
    solK = K_;
    solN = N_;
    memcpy(solDBt, DBt, sizeof DBt);
    memcpy(solDS, DS, sizeof DS);
}

/* Iterated annealing. A fresh random structure is used on the first round and on
 * about 30% of later rounds. Other rounds perturb the incumbent (two darts changed)
 * at a lower starting temperature. Returns 1 on cost 0, 0 on timeout. */
static int search_struct(double until) {
    const int iters = 8000;
    int have = 0;
    long bestc = 0;
    while (now() < until) {
        int fresh = (!have) || (rnd01() < 0.3);
        if (fresh) {
            int x = (K_ == 2) ? rndint(d + 1) : d;
            build_struct(x);
            for (int a = 0; a < K_; a++)
                for (int k = 0; k < d; k++) random_dart(a, k);
        } else {
            memcpy(DBt, incDBt, sizeof DBt);
            build_inc();
            for (int a = 0; a < K_; a++)
                for (int k = 0; k < d; k++) set_dart(a, k, incDS[a][k]);
            for (int t = 0; t < 2; t++) {
                int a = rndint(K_), k = rndint(d);
                int y;
                do { y = rndint(N_); } while (conflict(a, k, y));
                set_dart(a, k, y);
            }
        }
        long cost = cover_cost();
        if (cost == 0) { save_solution(); return 1; }
        double c0 = (double)cost;
        double Ts = (fresh ? 0.05 : 0.02) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int a = rndint(K_), k = rndint(d);
            int y;
            do { y = rndint(N_); } while (conflict(a, k, y));
            int old = DS[a][k];
            set_dart(a, k, y);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_dart(a, k, old);
            }
        }
        if (cost == 0) { save_solution(); return 1; }
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(incDBt, DBt, sizeof DBt);
            memcpy(incDS, DS, sizeof DS);
        }
    }
    return 0;
}

static void print_solution(void) {
    int K = solK, N = solN;
    K_ = K;
    N_ = N;
    memcpy(DBt, solDBt, sizeof DBt);
    build_inc();
    for (int a = 0; a < K; a++)
        for (int k = 0; k < d; k++) set_dart(a, k, solDS[a][k]);
    printf("%d %d\n", 2 * K * N, K * N * d);
    for (int a = 0; a < K; a++)
        for (int g = 0; g < N; g++)
            for (int k = 0; k < d; k++)
                printf("%d %d\n", a * N + g, K * N + DBt[a][k] * N + fwd[a][k][g]);
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
    long lo = atol(argv[5]), hi = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < 2 * d || N > MAXN) continue;
            for (int K = 2; K >= 1; K--) {
                long n = 2L * K * N;
                if (n <= lo || n > hi) continue;
                if (nc < MAXCAND) {
                    Cand cd = {q, p, k, c, (int)N, K, (int)n};
                    cand[nc++] = cd;
                }
            }
        }
    }
    /* Ascending total order; at equal order, the 4N (K=2) candidate is tried first. */
    for (int i = 1; i < nc; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && (cand[j].n > t.n || (cand[j].n == t.n && cand[j].K < t.K))) {
            cand[j + 1] = cand[j];
            j--;
        }
        cand[j + 1] = t;
    }

    int best_n = 0;
    for (int ci = 0; ci < nc; ci++) {
        double rem = t_end - now();
        if (rem < 0.3) break;
        if (cand[ci].n <= best_n) continue;
        double slice = 0.2 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_group(cand[ci].q, cand[ci].p, cand[ci].k, cand[ci].c);
        K_ = cand[ci].K;
        N_ = cand[ci].N;
        if (search_struct(now() + slice)) {
            best_n = cand[ci].n;
            solCi = ci;
        }
    }

    if (solCi < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(cand[solCi].q, cand[solCi].p, cand[solCi].k, cand[solCi].c);
    print_solution();
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

    # Search: two-orbit (K=2) and one-orbit (K=1) affine-group lifts, total order in (lo, hi].
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0], mb // 5)
        hi = mb // 3
        if budget > 2.0 and lo < hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
