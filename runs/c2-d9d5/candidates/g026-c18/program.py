"""Random-base multi-orbit group lifts for the bipartite degree-diameter problem.

Bold change in this version: instead of a fixed two-orbit affine pattern over F_q x| H,
the C engine searches over
  * arbitrary groups Z_m x|_r Z_k of any order N = m*k (not just prime-power affine groups),
  * random d-regular bipartite base multigraphs on B + B orbits (B = 1..6, chosen per phase),
    re-randomised at every restart, with target-swap moves inside the annealing,
  * voltages with simple-graph constraints (darts to the same orbit get distinct voltages).

A lift with B orbits per side on a group of order N has 2BN vertices and is d-regular and
bipartite. Left translations are automorphisms, transitive on each left orbit, and the
diameter condition reduces to BFS from the 2B orbit representatives. The C engine re-checks
small outputs with a full BFS, and Python checks everything with lib.is_valid and keeps a
valid fallback (projective plane, Araujo-Lopez/GQ where applicable, or K_{d,d}).
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Random-base group lifts.
 * Group G = Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k).
 * B orbits per side. Left (i,g) ~ right (j, g*x) for each dart (i,t) with
 * tgt[i][t] = j and voltage x = vol[i][t]. Each right orbit receives exactly d darts.
 * Usage: prog d D seed time_limit lowTotal mbTotal
 * Output: "n m" then m lines "u v", or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXB 6
#define MAXD 32
#define MAXN 5000
#define MAXV (2 * MAXB * MAXN)

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
static long modpow(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* ------------------------------------------------------------ group */

static int GM, GK, GR, GN;
static int powR[MAXN];

static void setgroup(int m, int k, int r) {
    GM = m; GK = k; GR = r; GN = m * k;
    long p = 1 % m;
    for (int b = 0; b < k; b++) {
        powR[b] = (int)p;
        p = p * r % m;
    }
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int na = (a + powR[b] * c % GM) % GM;
    int nb = (b + e) % GK;
    return na * GK + nb;
}

static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int na = (GM - powR[nb] * a % GM) % GM;
    return na * GK + nb;
}

/* Random r with gcd(r,m)=1 and r^k = 1 mod m; falls back to r = 1 (abelian). */
static int pick_r(int m, int k) {
    if (m <= 2 || k == 1 || k > 64) return (m == 1) ? 0 : 1 % m;
    int start = 1 + rndint(m - 1);
    for (int s = 0; s < m - 1; s++) {
        int r = 1 + (start - 1 + s) % (m - 1);
        if (gcd_i(r, m) != 1) continue;
        if (modpow(r, k, m) == 1 % m) return r;
    }
    return 1;
}

/* Random factorisation N = m*k, preferring non-trivial k. */
static int pick_k(int N) {
    int divs[512], nd = 0;
    for (int k = 1; k <= N && nd < 512; k++)
        if (N % k == 0) divs[nd++] = k;
    if (nd > 2 && rnd01() < 0.85) return divs[1 + rndint(nd - 2)];
    return divs[rndint(nd)];
}

/* ------------------------------------------------------------ lift state */

static int B;
static int tgt[MAXB][MAXD], vol[MAXB][MAXD];
static int fw[MAXB][MAXD][MAXN], bw[MAXB][MAXD][MAXN];
static int incI[MAXB][MAXD], incT[MAXB][MAXD];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static int bestTotal = 0, bestB, bestM, bestK, bestR, bestN;
static int bestTgt[MAXB][MAXD], bestVol[MAXB][MAXD];

static void set_dart(int i, int t, int x) {
    vol[i][t] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fw[i][t][g] = gmul(g, x);
        bw[i][t][g] = gmul(g, xi);
    }
}

static void rebuild_inc(void) {
    int cnt[MAXB];
    for (int j = 0; j < B; j++) cnt[j] = 0;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            int j = tgt[i][t];
            incI[j][cnt[j]] = i;
            incT[j][cnt[j]] = t;
            cnt[j]++;
        }
}

/* Random base: every right orbit gets exactly d darts. */
static void random_base(void) {
    int slots[MAXB * MAXD], ns = 0;
    for (int j = 0; j < B; j++)
        for (int c = 0; c < d; c++) slots[ns++] = j;
    for (int i = ns - 1; i > 0; i--) {
        int r = rndint(i + 1);
        int tmp = slots[i]; slots[i] = slots[r]; slots[r] = tmp;
    }
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) tgt[i][t] = slots[i * d + t];
}

/* Darts of row i with the same target need distinct voltages (checks t2 < upto). */
static int dart_ok(int i, int t, int x, int upto) {
    for (int t2 = 0; t2 < upto; t2++)
        if (t2 != t && tgt[i][t2] == tgt[i][t] && vol[i][t2] == x) return 0;
    return 1;
}

static int row_ok(int i) {
    for (int t = 0; t < d; t++)
        for (int t2 = t + 1; t2 < d; t2++)
            if (tgt[i][t] == tgt[i][t2] && vol[i][t] == vol[i][t2]) return 0;
    return 1;
}

static int init_voltages(void) {
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            int x = 0, tries = 0;
            do {
                x = rndint(GN);
                tries++;
            } while (!dart_ok(i, t, x, t) && tries < 5000);
            if (tries >= 5000) return 0;
            set_dart(i, t, x);
        }
    return 1;
}

static void swap_targets(int i1, int t1, int i2, int t2) {
    int tmp = tgt[i1][t1];
    tgt[i1][t1] = tgt[i2][t2];
    tgt[i2][t2] = tmp;
    rebuild_inc();
}

/* BFS to depth D from src; returns the number of reached vertices. */
static int bfs_count(int src) {
    int N = GN, BN = B * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int i = v / N, g = v % N;
                for (int t = 0; t < d; t++) {
                    int u = BN + tgt[i][t] * N + fw[i][t][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - BN, j = w / N, y = w % N;
                for (int k = 0; k < d; k++) {
                    int i = incI[j][k], t = incT[j][k];
                    int u = i * N + bw[i][t][y];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached (representative, vertex) pairs over the 2B orbit representatives. */
static long cover_cost(void) {
    int N = GN, V = 2 * B * N;
    long cost = 0;
    for (int i = 0; i < B; i++) cost += (long)(V - bfs_count(i * N));
    for (int j = 0; j < B; j++) cost += (long)(V - bfs_count((B + j) * N));
    return cost;
}

static void save_best(void) {
    int total = 2 * B * GN;
    if (total <= bestTotal) return;
    bestTotal = total;
    bestB = B; bestM = GM; bestK = GK; bestR = GR; bestN = GN;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            bestTgt[i][t] = tgt[i][t];
            bestVol[i][t] = vol[i][t];
        }
}

/* Random restarts at order N with B orbits; each restart draws a new group and base.
 * Returns 1 with a cost-0 state saved to best, 0 on timeout. */
static int search_at(int Bv, int N, double until) {
    const int iters = 6000;
    B = Bv;
    while (now() < until) {
        int k = pick_k(N), m = N / k, r = pick_r(m, k);
        setgroup(m, k, r);
        random_base();
        rebuild_inc();
        if (!init_voltages()) continue;
        long cost = cover_cost();
        if (cost == 0) { save_best(); return 1; }
        double Ts = 0.05 * (double)cost + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            if (rndint(10) < 8) {
                int i = rndint(B), t = rndint(d);
                int x = 0, tries = 0;
                do {
                    x = rndint(GN);
                    tries++;
                } while (!dart_ok(i, t, x, d) && tries < 1000);
                if (tries >= 1000) continue;
                int old = vol[i][t];
                set_dart(i, t, x);
                long c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else set_dart(i, t, old);
            } else {
                int i1 = rndint(B), t1 = rndint(d), i2 = rndint(B), t2 = rndint(d);
                if (tgt[i1][t1] == tgt[i2][t2]) continue;
                swap_targets(i1, t1, i2, t2);
                if (!row_ok(i1) || !row_ok(i2)) {
                    swap_targets(i1, t1, i2, t2);
                    continue;
                }
                long c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else swap_targets(i1, t1, i2, t2);
            }
        }
        if (cost == 0) { save_best(); return 1; }
    }
    return 0;
}

/* Binary search over N in [lo, hi] for feasibility, then extend upward. */
static void search_phase(int Bv, int lo, int hi, double until) {
    if (lo < d) lo = d;
    if (hi > MAXN - 1) hi = MAXN - 1;
    if (lo > hi || now() >= until) return;
    double budget = until - now();
    double slice = budget / 10.0;
    if (slice < 0.6) slice = 0.6;
    int a = lo, b = hi, found = 0;
    while (a <= b && now() < until) {
        int mid = a + (b - a) / 2;
        double s = slice;
        if (now() + s > until) s = until - now();
        if (search_at(Bv, mid, now() + s)) { found = mid; a = mid + 1; }
        else b = mid - 1;
    }
    if (found) {
        int fails = 0;
        for (int N = found + 1; N <= hi && now() < until && fails < 3; N++) {
            double s = slice * 1.5;
            if (now() + s > until) s = until - now();
            if (search_at(Bv, N, now() + s)) fails = 0;
            else fails++;
        }
    }
}

/* ------------------------------------------------------------ main */

static int adj[MAXV][MAXD];

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long lowTotal = atol(argv[5]);
    long mbTotal = atol(argv[6]);

    double t0 = now();
    t_end = t0 + limit - 1.0;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }

    /* Phases: B = 2, 3, 4, then the best B (or 1) with the remaining time. */
    double fr[4] = {0.45, 0.25, 0.15, 0.15};
    double remsum = 1.0;
    for (int s = 0; s < 4; s++) {
        int Bv = (s < 3) ? (2 + s) : (bestTotal > 0 ? bestB : 1);
        double tnow = now();
        double until = tnow + (t_end - tnow) * fr[s] / remsum;
        remsum -= fr[s];
        if (until > t_end) until = t_end;
        long thr = lowTotal > bestTotal ? lowTotal : bestTotal;
        long M = 2L * Bv;
        long lo = (thr + M) / M;          /* ceil((thr+1)/M) */
        long hi = mbTotal / M;
        if (hi > MAXN - 1) hi = MAXN - 1;
        search_phase(Bv, (int)lo, (int)hi, until);
    }

    if (bestTotal == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Rebuild the best graph. */
    B = bestB;
    setgroup(bestM, bestK, bestR);
    int N = GN;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            tgt[i][t] = bestTgt[i][t];
            set_dart(i, t, bestVol[i][t]);
        }
    rebuild_inc();

    int BN = B * N, V = 2 * BN, E = BN * d;
    for (int v = 0; v < BN; v++) {
        int i = v / N, g = v % N;
        for (int t = 0; t < d; t++) adj[v][t] = BN + tgt[i][t] * N + fw[i][t][g];
    }
    for (int w = BN; w < V; w++) {
        int j = (w - BN) / N, y = (w - BN) % N;
        for (int k = 0; k < d; k++) {
            int i = incI[j][k], t = incT[j][k];
            adj[w][k] = i * N + bw[i][t][y];
        }
    }

    /* Full check from every vertex when cheap. */
    if (V <= 4000) {
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
        for (int t = 0; t < d; t++)
            printf("%d %d\n", v, adj[v][t]);
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

    # Random-base group lifts. The C engine only reports graphs strictly larger than
    # the lowTotal we pass, so the Python fallback is never replaced by a smaller graph.
    if d >= 2 and D >= 3:
        elapsed = time.monotonic() - t0
        budget = 0.85 * time_limit - elapsed - 2.0
        if budget > 3.0:
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, seed, round(budget, 2),
                                  best[0], lib.moore_bound(d, D)],
                                 stdin_graph=None, timeout=budget + 6.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
