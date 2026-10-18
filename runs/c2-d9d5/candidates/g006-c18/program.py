"""Semidirect-product voltage lifts for the bipartite degree-diameter problem.

Bold change in this version: the parent's engine used the affine groups F_q x| H.
This engine uses the metacyclic groups Z_m x|_r Z_k (r^k = 1 mod m), chosen freshly
at every restart from all (m, k, r) with m*k = N. Any group order N then has many
candidates, so the search no longer depends on prime-power structure.

Construction: each side is split into B orbits (B = 1 or 2) of a group G of order N.
Dart (i, t) has target orbit tgt[i][t] and voltage v, joining L_(i,g) to
R_(tgt, g*v). Left translations are automorphisms that are transitive on each orbit,
so the diameter is at most D iff BFS from L_(i,e) and R_(j,e) reaches every vertex
within D steps. Simulated annealing adjusts the voltages to drive that cost to zero.
The C engine re-checks the full graph (all BFS, duplicate neighbours) when it is
small enough, and never prints an invalid graph. Python checks everything with
lib.is_valid and falls back to K_{d,d} or a known construction.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Semidirect-product voltage lifts.
 * Group G = Z_m x|_r Z_k, element x = a*k + b, (a,b)(c,e) = (a + r^b c, b + e).
 * Usage: prog d D seed time_limit lo2 hi2 lo1 hi1
 * Output: "n m" then m lines "u v", or "0 0".
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
#define MAXB 2
#define MAXV (2 * MAXB * MAXN)
#define MAXGR 4096
#define ITERS 6000

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

/* ------------------------------------------------------------ group */

static int GM, GK, GN, curR;
static int PWR[MAXN];

static void setup_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GN = m * k;
    curR = r;
    PWR[0] = 1 % m;
    for (int b = 1; b < k; b++) PWR[b] = (int)((long long)PWR[b - 1] * r % m);
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x - a * GK;
    int c = y / GK, e = y - c * GK;
    int na = (a + PWR[b] * c) % GM;
    int nb = b + e;
    if (nb >= GK) nb -= GK;
    return na * GK + nb;
}

static int ginv(int x) {
    int a = x / GK, b = x - a * GK;
    int nb = (GK - b) % GK;
    int na = (GM - (PWR[nb] * a) % GM) % GM;
    return na * GK + nb;
}

/* Uniformly pick a group of order N among all (m, k, r) with m*k = N. */
static void pick_group(int N, int *pm, int *pk, int *pr) {
    static int cm[MAXGR], ck[MAXGR], cr[MAXGR];
    int cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (cnt < MAXGR) { cm[cnt] = 1; ck[cnt] = k; cr[cnt] = 0; cnt++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            if (cnt < MAXGR) { cm[cnt] = m; ck[cnt] = k; cr[cnt] = r; cnt++; }
        }
    }
    int idx = rndint(cnt);
    *pm = cm[idx];
    *pk = ck[idx];
    *pr = cr[idx];
}

/* ------------------------------------------------------------ lift state */

static int curB, curA;
static int tgt[MAXB][MAXD], vol[MAXB][MAXD];
static int fw[MAXB][MAXD][MAXN], bw[MAXB][MAXD][MAXN];
static int incI[MAXB][2 * MAXD], incT[MAXB][2 * MAXD];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static int bestTotal = 0, bestB, bestA, bestM, bestK, bestR, bestN;
static int bestVol[MAXB][MAXD];

static void set_pattern(int B, int a) {
    curB = B;
    curA = a;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            if (B == 1) tgt[i][t] = 0;
            else tgt[i][t] = ((i == 0) == (t < a)) ? 0 : 1;
            vol[i][t] = -1;
        }
    for (int j = 0; j < B; j++) {
        int cnt = 0;
        for (int i = 0; i < B; i++)
            for (int t = 0; t < d; t++)
                if (tgt[i][t] == j) {
                    incI[j][cnt] = i;
                    incT[j][cnt] = t;
                    cnt++;
                }
    }
}

static void set_dart(int i, int t, int x) {
    vol[i][t] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fw[i][t][g] = gmul(g, x);
        bw[i][t][g] = gmul(g, xi);
    }
}

/* Darts with the same (source orbit, target orbit) need distinct voltages. */
static int valid_value(int i, int t, int x) {
    for (int t2 = 0; t2 < d; t2++)
        if (t2 != t && tgt[i][t2] == tgt[i][t] && vol[i][t2] == x) return 0;
    return 1;
}

static int bfs_count(int src) {
    int N = GN, BN = curB * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int i = v / N, g = v - i * N;
                for (int t = 0; t < d; t++) {
                    int u = BN + tgt[i][t] * N + fw[i][t][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - BN, j = w / N, y = w - j * N;
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

/* Unreached vertices from the 2B orbit representatives (identity of each orbit). */
static long cover_cost(void) {
    int N = GN, V = 2 * curB * N;
    long cost = 0;
    for (int i = 0; i < curB; i++) cost += (long)(V - bfs_count(i * N));
    for (int j = 0; j < curB; j++) cost += (long)(V - bfs_count(curB * N + j * N));
    return cost;
}

static void record(int B, int N) {
    int total = 2 * B * N;
    if (total <= bestTotal) return;
    bestTotal = total;
    bestB = B;
    bestA = curA;
    bestN = N;
    bestM = GM;
    bestK = GK;
    bestR = curR;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) bestVol[i][t] = vol[i][t];
}

/* Random restarts with a fresh group and pattern each time; SA on voltages.
 * Returns 1 with cost 0 (state recorded), 0 on timeout. */
static int attempt(int B, int N, double until) {
    while (now() < until) {
        int m, k, r;
        pick_group(N, &m, &k, &r);
        setup_group(m, k, r);
        int a = (B == 1) ? d : 1 + rndint(d / 2);
        set_pattern(B, a);
        int ok = 1;
        for (int i = 0; i < B && ok; i++)
            for (int t = 0; t < d && ok; t++) {
                int x = -1;
                for (int tries = 0; tries < 2000; tries++) {
                    int c = rndint(N);
                    if (valid_value(i, t, c)) { x = c; break; }
                }
                if (x < 0) ok = 0;
                else set_dart(i, t, x);
            }
        if (!ok) continue;

        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < ITERS && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / ITERS);
            int i = rndint(B), t = rndint(d);
            int x = -1;
            for (int tries = 0; tries < 200; tries++) {
                int c = rndint(N);
                if (c != vol[i][t] && valid_value(i, t, c)) { x = c; break; }
            }
            if (x < 0) continue;
            int old = vol[i][t];
            set_dart(i, t, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_dart(i, t, old);
            }
        }
        if (cost == 0) {
            record(B, N);
            return 1;
        }
    }
    return 0;
}

/* Binary search for a feasible order, then extend upward from the largest success. */
static void search_phase(int B, int lo, int hi, double until) {
    if (lo > hi) return;
    int a = lo, b = hi, feasMax = 0;
    while (a <= b && now() < until) {
        int mid = a + (b - a) / 2;
        double rem = until - now();
        double slice = rem * 0.2;
        if (slice < 1.0) slice = (rem < 1.0) ? rem : 1.0;
        if (attempt(B, mid, now() + slice)) {
            if (mid > feasMax) feasMax = mid;
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }
    if (feasMax == 0) return;
    int fails = 0, N = feasMax + 1;
    while (N <= hi && fails < 3 && now() < until) {
        double rem = until - now();
        double slice = rem * 0.3;
        if (slice < 1.0) slice = (rem < 1.0) ? rem : 1.0;
        if (attempt(B, N, now() + slice)) fails = 0;
        else fails++;
        N++;
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo2 = atoi(argv[5]), hi2 = atoi(argv[6]);
    int lo1 = atoi(argv[7]), hi1 = atoi(argv[8]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (hi2 > MAXN - 1) hi2 = MAXN - 1;
    if (hi1 > MAXN - 1) hi1 = MAXN - 1;
    if (lo2 < 2 * d) lo2 = 2 * d;
    if (lo1 < 2 * d) lo1 = 2 * d;

    double T = t_end - t0;
    double tA = t0 + 0.35 * T;
    double tB = t0 + 0.7 * T;
    if (lo2 <= hi2) search_phase(2, lo2, hi2, tA);
    if (lo1 <= hi1) search_phase(1, lo1, hi1, tB);
    if (bestTotal == 0) {
        if (lo1 <= hi1) search_phase(1, lo1, hi1, t_end);
    } else if (bestB == 2) {
        int nlo = bestN + 1;
        if (nlo < lo2) nlo = lo2;
        if (nlo <= hi2) search_phase(2, nlo, hi2, t_end);
    } else {
        int nlo = bestN + 1;
        if (nlo < lo1) nlo = lo1;
        if (nlo <= hi1) search_phase(1, nlo, hi1, t_end);
    }

    if (bestTotal == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Rebuild the best graph from its recorded group and voltages. */
    int B = bestB, N = bestN;
    setup_group(bestM, bestK, bestR);
    set_pattern(B, bestA);
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) set_dart(i, t, bestVol[i][t]);

    int BN = B * N, V = 2 * BN, E = BN * d;
    static int adj[MAXV][MAXD];
    for (int v = 0; v < BN; v++) {
        int i = v / N, g = v - i * N;
        for (int t = 0; t < d; t++) adj[v][t] = BN + tgt[i][t] * N + fw[i][t][g];
    }
    for (int w = BN; w < V; w++) {
        int j = (w - BN) / N, y = (w - BN) - j * N;
        for (int k = 0; k < d; k++) {
            int i = incI[j][k], t = incT[j][k];
            adj[w][k] = i * N + bw[i][t][y];
        }
    }

    /* Simple-graph check: no repeated neighbour. */
    for (int v = 0; v < V; v++)
        for (int k = 0; k < d; k++)
            for (int k2 = 0; k2 < k; k2++)
                if (adj[v][k] == adj[v][k2]) {
                    printf("0 0\n");
                    return 0;
                }

    /* Full diameter check from every vertex when cheap; symmetry covers the rest. */
    if (V <= 6500) {
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

    # Semidirect-product lifts. Order N gives 4N vertices (B = 2) or 2N (B = 1).
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        lo2 = max(2 * d, best[0] // 4 + 1, mb // 16)
        hi2 = min(mb // 4, 3199)
        lo1 = max(2 * d, best[0] // 2 + 1, mb // 8)
        hi1 = min(mb // 4, 3199)
        if budget > 2.0 and (lo2 <= hi2 or lo1 <= hi1):
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2),
                                            lo2, hi2, lo1, hi1],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
