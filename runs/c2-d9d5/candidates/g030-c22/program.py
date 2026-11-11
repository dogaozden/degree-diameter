"""Combined affine voltage-lift search for the bipartite degree-diameter problem.

Merges two parents:
  * general K-orbit voltage lifts (K left and K right orbits over G = F_q x| H, each
    left orbit owning d darts, each right orbit receiving exactly d darts), with
    target-swap moves and a duplicate-dart penalty (from parent g005-c24);
  * pattern-based two-orbit initialisation with a random split parameter a, the
    single-orbit K = 1 family, binary search over group orders, and a final full
    BFS check for small graphs (from parent g005-c10).

Each dart-target assignment keeps right-orbit degrees exact, so the graph is
d-regular and bipartite. Left translations are automorphisms that are transitive
on each orbit, so diameter <= D is decided by 2K BFS runs from orbit representatives.
K = 1 runs first (2N vertices, cheap to evaluate), then K = 2 (4N vertices) with
the remaining time, and every phase only searches orders that beat the best total
found so far. The best valid graph wins; Python re-checks everything.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Affine K-orbit voltage lift search (K = 1 or 2).
 * Group G = F_q x| H, |G| = N = q*c, c >= 2, c | q-1.
 * Vertices: left L^a_x = a*N + x (a < K); right R^b_y = K*N + b*N + y.
 * Dart t = a*d + i leaves left orbit a: L^a_x ~ R^{tb[t]}_{x * vg[t]}.
 * Right orbit b receives exactly d darts, so the graph is d-regular.
 * Usage: prog d D seed time_limit lo1 hi1 lo2 hi2
 * Output: "n m" then m lines "u v", or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 512
#define MAXC 512
#define MAXN 8192
#define MAXD 32
#define MAXK 2
#define MAXND (MAXK * MAXD)
#define MAXV (2 * MAXK * MAXN)
#define MAXCAND 16384

typedef struct { int q, p, e, c, N; } Cand;

static int d, D, K, nd, GN, GC;
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

static int factor_pp(int q, int *p, int *e) {
    int pp = 0;
    for (int f = 2; f * f <= q; f++)
        if (q % f == 0) { pp = f; break; }
    if (!pp) pp = q;
    int r = q, kk = 0;
    while (r % pp == 0) { r /= pp; kk++; }
    if (r != 1 || kk < 1) return 0;
    *p = pp;
    *e = kk;
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

static void build_field(int q, int p, int e) {
    if (built_q == q) return;
    int pw[16];
    pw[0] = 1;
    for (int i = 1; i <= e; i++) pw[i] = pw[i - 1] * p;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            int r = 0;
            for (int i = 0; i < e; i++)
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
        for (int i = 0; i < e; i++) { m[i] = t % p; t /= p; }
        int ok = 1;
        for (int a = 1; a < q && ok; a++)
            for (int b = 1; b < q && ok; b++)
                if (polymul(a, b, p, e, pw, m) == 0) ok = 0;
        if (ok) {
            found = 1;
            for (int a = 0; a < q; a++)
                for (int b = 0; b < q; b++)
                    MULT[a][b] = polymul(a, b, p, e, pw, m);
        }
    }
    built_q = q;
}

/* ------------------------------------------------------------ group G = F_q x| H */

static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Element (a, h_j) coded as a*c + j, h_j = g^(j*(q-1)/c). */
static void setup_group(int q, int p, int e, int c) {
    build_field(q, p, e);
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

/* ------------------------------------------------------------ lift state */

static int tb[MAXND], vg[MAXND];
static int fw[MAXND][MAXN], bw[MAXND][MAXN];   /* x*g and y*x^-1 */
static int cnt_in[MAXK];
static int inc_t[MAXK][MAXD];                  /* darts entering right orbit b */
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static long bestTotal = 0;
static int bestK = 0;
static Cand bestCd;
static int bestTb[MAXND], bestVg[MAXND];

static Cand cl[MAXCAND];
static int ncl = 0;

static void set_dart(int t, int x) {
    vg[t] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fw[t][g] = gmul(g, x);
        bw[t][g] = gmul(g, xi);
    }
}

static void rebuild_inc(void) {
    for (int b = 0; b < K; b++) cnt_in[b] = 0;
    for (int t = 0; t < nd; t++) {
        int b = tb[t];
        if (cnt_in[b] < d) inc_t[b][cnt_in[b]++] = t;
    }
}

/* Start from a random balanced assignment (K = 2 also tries the two-orbit
 * split pattern with a random parameter a), then random voltages. */
static void init_state(void) {
    if (K == 2 && rndint(2) == 0) {
        int a = 1 + rndint(d / 2);
        for (int t = 0; t < d; t++) {
            tb[t] = (t < a) ? 0 : 1;
            tb[d + t] = (t < a) ? 1 : 0;
        }
    } else {
        int list[MAXND], p = 0;
        for (int b = 0; b < K; b++)
            for (int i = 0; i < d; i++) list[p++] = b;
        for (int i = nd - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = list[i]; list[i] = list[j]; list[j] = tmp;
        }
        for (int t = 0; t < nd; t++) tb[t] = list[t];
    }
    rebuild_inc();
    for (int t = 0; t < nd; t++) set_dart(t, rndint(GN));
}

/* Darts of one left orbit with equal target and voltage give a repeated edge. */
static long dup_count(void) {
    long c = 0;
    for (int t1 = 0; t1 < nd; t1++)
        for (int t2 = t1 + 1; t2 < nd; t2++)
            if (t1 / d == t2 / d && tb[t1] == tb[t2] && vg[t1] == vg[t2]) c++;
    return c;
}

/* Vertices reached within distance D from src. */
static int bfs_count(int src) {
    int BN = K * GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int a = v / GN, x = v % GN;
                for (int i = 0; i < d; i++) {
                    int t = a * d + i;
                    int u = BN + tb[t] * GN + fw[t][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - BN, b = w / GN, y = w % GN;
                for (int j = 0; j < d; j++) {
                    int t = inc_t[b][j];
                    int u = (t / d) * GN + bw[t][y];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Orbit representatives suffice: left translations are transitive on each orbit. */
static long cost_fn(void) {
    long V = 2L * K * GN;
    long c = 0;
    long dp = dup_count();
    for (int a = 0; a < K; a++) c += V - bfs_count(a * GN);
    for (int b = 0; b < K; b++) c += V - bfs_count(K * GN + b * GN);
    return c + 1000L * dp;
}

/* Annealing over target swaps (K > 1) and voltage changes. Returns 1 on cost 0. */
static int search_group(double until) {
    const int iters = 8000;
    while (now() < until) {
        init_state();
        long cost = cost_fn();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            if (K > 1 && rnd01() < 0.35) {
                int t1 = rndint(nd), t2 = rndint(nd);
                if (tb[t1] == tb[t2]) continue;
                int tmp = tb[t1]; tb[t1] = tb[t2]; tb[t2] = tmp;
                rebuild_inc();
                long c2 = cost_fn();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    tmp = tb[t1]; tb[t1] = tb[t2]; tb[t2] = tmp;
                    rebuild_inc();
                }
            } else {
                int t = rndint(nd), x = rndint(GN);
                if (x == vg[t]) continue;
                int old = vg[t];
                set_dart(t, x);
                long c2 = cost_fn();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    set_dart(t, old);
                }
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void record(Cand cd) {
    long total = 2L * K * cd.N;
    if (total <= bestTotal) return;
    bestTotal = total;
    bestK = K;
    bestCd = cd;
    for (int t = 0; t < nd; t++) {
        bestTb[t] = tb[t];
        bestVg[t] = vg[t];
    }
}

static void build_cands(long lo, long hi) {
    ncl = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, e;
        if (!factor_pp(q, &p, &e)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            if (ncl < MAXCAND) {
                Cand cd = {q, p, e, c, (int)N};
                cl[ncl++] = cd;
            }
        }
    }
    for (int i = 1; i < ncl; i++) {
        Cand t = cl[i];
        int j = i - 1;
        while (j >= 0 && cl[j].N > t.N) { cl[j + 1] = cl[j]; j--; }
        cl[j + 1] = t;
    }
}

/* Binary search over group orders, then extend upward. */
static void search_phase(int Kv, long lo, long hi, double until) {
    K = Kv;
    nd = K * d;
    build_cands(lo, hi);
    int a = 0, b = ncl - 1, bi = -1;
    long bn = 0;
    while (a <= b && now() < until) {
        int mid = (a + b) / 2;
        double rem = until - now();
        double slice = rem * 0.15;
        if (slice < 1.5) slice = 1.5;
        if (slice > rem) slice = rem;
        setup_group(cl[mid].q, cl[mid].p, cl[mid].e, cl[mid].c);
        if (search_group(now() + slice)) {
            record(cl[mid]);
            if (cl[mid].N > bn) { bn = cl[mid].N; bi = mid; }
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }
    if (bi < 0) return;
    int fails = 0, idx = bi + 1;
    while (idx < ncl && now() < until && fails < 2) {
        if (cl[idx].N <= bn) { idx++; continue; }
        double rem = until - now();
        double slice = rem * 0.6;
        if (slice < 1.5) slice = 1.5;
        if (slice > rem) slice = rem;
        setup_group(cl[idx].q, cl[idx].p, cl[idx].e, cl[idx].c);
        if (search_group(now() + slice)) {
            record(cl[idx]);
            bn = cl[idx].N;
            bi = idx;
            idx++;
            fails = 0;
        } else {
            idx++;
            fails++;
        }
    }
}

/* ------------------------------------------------------------ output */

static int adj[MAXV][MAXD];

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long lo[MAXK + 1], hi[MAXK + 1];
    for (int k = 1; k <= MAXK; k++) {
        lo[k] = atol(argv[3 + 2 * k]);
        hi[k] = atol(argv[4 + 2 * k]);
    }
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }

    /* K = 1 first (cheaper evaluations), then K = 2 with the remaining time. */
    for (int s = 0; s < 2; s++) {
        int Kv = (s == 0) ? 1 : 2;
        long e = lo[Kv];
        long need = bestTotal / (2L * Kv) + 1;
        if (need > e) e = need;
        if (e < 2L * d) e = 2L * d;
        long h = hi[Kv];
        if (h > MAXN - 1) h = MAXN - 1;
        double rem = t_end - now();
        if (rem < 1.0) break;
        double until = (s == 0) ? now() + rem * 0.5 : t_end;
        if (e <= h) search_phase(Kv, e, h, until);
    }

    if (bestTotal == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Rebuild the best graph. */
    K = bestK;
    nd = K * d;
    setup_group(bestCd.q, bestCd.p, bestCd.e, bestCd.c);
    for (int t = 0; t < nd; t++) tb[t] = bestTb[t];
    rebuild_inc();
    for (int t = 0; t < nd; t++) set_dart(t, bestVg[t]);

    int BN = K * GN, V = 2 * BN, E = BN * d;
    for (int v = 0; v < BN; v++) {
        int a = v / GN, x = v % GN;
        for (int i = 0; i < d; i++) {
            int t = a * d + i;
            adj[v][i] = BN + tb[t] * GN + fw[t][x];
        }
    }
    for (int w = BN; w < V; w++) {
        int b = (w - BN) / GN, y = (w - BN) % GN;
        for (int j = 0; j < d; j++) {
            int t = inc_t[b][j];
            adj[w][j] = (t / d) * GN + bw[t][y];
        }
    }

    /* Full BFS check from every vertex when cheap (a sanity net). */
    if (V <= 5000) {
        for (int s = 0; s < V; s++) {
            stamp_++;
            int head = 0, tail = 0;
            que[tail++] = s;
            vis[s] = stamp_;
            for (int lvl = 0; lvl < D && head < tail; lvl++) {
                int end = tail;
                while (head < end) {
                    int v = que[head++];
                    for (int k = 0; k < d; k++) {
                        int u = adj[v][k];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
                }
            }
            if (tail != V) {
                printf("0 0\n");
                return 0;
            }
        }
    }

    printf("%d %d\n", V, E);
    for (int v = 0; v < BN; v++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", v, adj[v][i]);
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

    # Affine voltage lifts: K = 1 gives 2N vertices, K = 2 gives 4N vertices.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
        lo1 = max(2 * d, best[0] // 2 + 1)
        hi1 = mb // 2
        lo2 = max(2 * d, best[0] // 4 + 1)
        hi2 = mb // 4
        if budget > 2.0 and (lo1 <= hi1 or lo2 <= hi2):
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, seed, round(budget, 2), lo1, hi1, lo2, hi2],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass  # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
