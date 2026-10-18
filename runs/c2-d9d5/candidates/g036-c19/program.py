"""Metacyclic multi-orbit lifts for the bipartite degree-diameter problem.

Change in this version: the group family is replaced. Instead of F_q x| H, the
search uses metacyclic groups G = Z_m x|_r Z_k (r^k = 1 mod m, gcd(r, m) = 1),
which include cyclic and abelian groups (r = 1). Group orders are free in
[lo, hi], so the search is no longer limited to prime-power-related orders. The
number of left and right orbits B is in {1, 2, 3, 4}, so the graph has 2*B*N
vertices.

Dart (i, t) with voltage v joins L_(i,g) to R_(tgt, g*v). Left translations are
automorphisms that are transitive on each orbit, so BFS from the 2B orbit
representatives decides the diameter. Simulated annealing over voltages, with
random base patterns, minimises the number of unreached (representative, vertex)
pairs. The C engine checks simplicity and, when small enough, a full BFS from
every vertex before printing. Python checks the result with lib.is_valid and
keeps a valid fallback (projective plane, Araujo-Lopez, or K_{d,d}).
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Metacyclic multi-orbit lifts. Group Z_m x|_r Z_k, element (a,b) coded a*k+b,
 * (a,b)(c,e) = (a + r^b c, b + e).
 * Usage: prog d D seed time_limit lowT maxT
 * Output: "n m" then m lines "u v", or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXB 4
#define MAXD 32
#define MAXN 4800
#define MAXCAND 170000

typedef struct { int m, k, r, N; } Cand;

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;
static int SA_ITERS = 8000;

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

/* ------------------------------------------------------------ metacyclic group */

static int GM, GK, GR, GN;
static int powR[MAXN];

static void setup_group(int m, int k, int r) {
    GM = m; GK = k; GR = r; GN = m * k;
    powR[0] = 1 % m;
    for (int b = 1; b < k; b++)
        powR[b] = (int)((long long)powR[b - 1] * r % m);
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int na = (int)((a + (long long)powR[b] * c) % GM);
    int nb = (b + e) % GK;
    return na * GK + nb;
}

static inline int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int na = (int)((GM - (long long)powR[nb] * a % GM) % GM);
    return na * GK + nb;
}

/* ------------------------------------------------------------ lift state */

static int curB;
static int tgt[MAXB][MAXD], vol[MAXB][MAXD];
static int fw[MAXB][MAXD][MAXN], bw[MAXB][MAXD][MAXN];
static int incI[MAXB][MAXD], incT[MAXB][MAXD];
static int vis[2 * MAXB * MAXN], que[2 * MAXB * MAXN];
static int stamp_ = 0;

static int bestTotal = 0, bestB, bestM, bestK, bestR;
static int bestTgt[MAXB][MAXD], bestVol[MAXB][MAXD];

static int base_connected(int B) {
    int seenL[MAXB], seenR[MAXB];
    for (int i = 0; i < B; i++) { seenL[i] = 0; seenR[i] = 0; }
    seenL[0] = 1;
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int i = 0; i < B; i++)
            for (int t = 0; t < d; t++) {
                int j = tgt[i][t];
                if (seenL[i] && !seenR[j]) { seenR[j] = 1; changed = 1; }
                if (seenR[j] && !seenL[i]) { seenL[i] = 1; changed = 1; }
            }
    }
    for (int i = 0; i < B; i++)
        if (!seenL[i] || !seenR[i]) return 0;
    return 1;
}

static int set_incidence(int B) {
    int cnt[MAXB];
    for (int j = 0; j < B; j++) cnt[j] = 0;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            int j = tgt[i][t];
            if (j < 0 || j >= B || cnt[j] >= d) return 0;
            incI[j][cnt[j]] = i;
            incT[j][cnt[j]] = t;
            cnt[j]++;
        }
    for (int j = 0; j < B; j++)
        if (cnt[j] != d) return 0;
    return 1;
}

static void random_pattern(int B) {
    for (;;) {
        for (int t = 0; t < d; t++) {
            int p[MAXB];
            for (int i = 0; i < B; i++) p[i] = i;
            for (int i = B - 1; i > 0; i--) {
                int r = rndint(i + 1);
                int tmp = p[i]; p[i] = p[r]; p[r] = tmp;
            }
            for (int i = 0; i < B; i++) tgt[i][t] = p[i];
        }
        if (base_connected(B) && set_incidence(B)) break;
    }
    curB = B;
}

/* Darts of the same (i, target) class need distinct voltages (simplicity). */
static int valid_value(int i, int t, int x, int limit) {
    for (int t2 = 0; t2 < limit; t2++)
        if (t2 != t && tgt[i][t2] == tgt[i][t] && vol[i][t2] == x) return 0;
    return 1;
}

static int simple_state(int B) {
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++)
            for (int t2 = 0; t2 < t; t2++)
                if (tgt[i][t2] == tgt[i][t] && vol[i][t2] == vol[i][t]) return 0;
    return 1;
}

static void set_dart(int i, int t, int x) {
    vol[i][t] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fw[i][t][g] = gmul(g, x);
        bw[i][t][g] = gmul(g, xi);
    }
}

/* BFS up to depth D from src; returns the number of vertices reached. */
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
                int i = v / N, g = v % N;
                for (int t = 0; t < d; t++) {
                    int u = BN + tgt[i][t] * N + fw[i][t][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - BN, j = w / N, x = w % N;
                for (int k = 0; k < d; k++) {
                    int i = incI[j][k], t = incT[j][k];
                    int u = i * N + bw[i][t][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

static long cover_cost(void) {
    int N = GN, V = 2 * curB * N;
    long cost = 0;
    for (int i = 0; i < curB; i++) cost += (long)(V - bfs_count(i * N));
    for (int j = 0; j < curB; j++) cost += (long)(V - bfs_count((curB + j) * N));
    return cost;
}

/* Simulated annealing over voltages with random base restarts.
 * Returns 1 with a simple cost-0 state in tgt/vol, 0 on timeout. */
static int search_group(int B, double until) {
    int N = GN;
    while (now() < until) {
        random_pattern(B);
        for (int i = 0; i < B; i++)
            for (int t = 0; t < d; t++) {
                int x, tries = 0;
                do { x = rndint(N); tries++; } while (!valid_value(i, t, x, t) && tries < 100000);
                set_dart(i, t, x);
            }
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < SA_ITERS && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / SA_ITERS);
            int i = rndint(B), t = rndint(d);
            int x, tries = 0;
            do { x = rndint(N); tries++; } while (!valid_value(i, t, x, d) && tries < 1000);
            if (tries >= 1000) continue;
            int old = vol[i][t];
            set_dart(i, t, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_dart(i, t, old);
            }
        }
        if (cost == 0 && simple_state(B)) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ candidates */

static Cand cand[MAXCAND];
static int nc = 0;
static int rlist[MAXN], olist[MAXN];

static int cmpN(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    return (x->N > y->N) - (x->N < y->N);
}

static void add_cand(int m, int k, int r) {
    if (nc < MAXCAND) {
        cand[nc].m = m;
        cand[nc].k = k;
        cand[nc].r = r;
        cand[nc].N = m * k;
        nc++;
    }
}

/* All (m, k, r) with lo <= m*k <= hi and r^k = 1 mod m, gcd(r, m) = 1.
 * r^k = 1 mod m iff ord(r) divides k. At most 4 random r per (m, k). */
static void build_cands(int lo, int hi) {
    nc = 0;
    for (int m = 1; m <= hi; m++) {
        int kmax = hi / m;
        int kmin = (lo + m - 1) / m;
        if (kmin < 1) kmin = 1;
        if (kmin > kmax) continue;
        if (m == 1) {
            for (int k = kmin; k <= kmax; k++) add_cand(1, k, 0);
            continue;
        }
        int cntR = 0;
        for (int r = 1; r < m; r++) {
            long long x = r;
            int t = 1;
            while (x != 1 && t < kmax) {
                x = x * r % m;
                t++;
            }
            if (x == 1) { rlist[cntR] = r; olist[cntR] = t; cntR++; }
        }
        for (int k = kmin; k <= kmax; k++) {
            int kept = 0, seen = 0, sel[4];
            for (int j = 0; j < cntR; j++) {
                if (k % olist[j]) continue;
                seen++;
                if (kept < 4) sel[kept++] = rlist[j];
                else {
                    int q = rndint(seen);
                    if (q < 4) sel[q] = rlist[j];
                }
            }
            for (int s = 0; s < kept; s++) add_cand(m, k, sel[s]);
        }
    }
    qsort(cand, nc, sizeof(Cand), cmpN);
}

static void range_of(int lo, int hi, int *ia, int *ib) {
    int a = 0, b = nc;
    while (a < b) {
        int mid = (a + b) / 2;
        if (cand[mid].N < lo) a = mid + 1; else b = mid;
    }
    *ia = a;
    a = 0; b = nc;
    while (a < b) {
        int mid = (a + b) / 2;
        if (cand[mid].N <= hi) a = mid + 1; else b = mid;
    }
    *ib = a;
}

static int lo_of(int B, long lowT) {
    long lo = lowT / (2 * B) + 1;
    if (lo < 2 * d) lo = 2 * d;
    return (int)lo;
}

static int hi_of(int B, long maxT) {
    long hi = maxT / (2 * B);
    if (hi > MAXN - 1) hi = MAXN - 1;
    return (int)hi;
}

static void record(int B, const Cand *c) {
    int total = 2 * B * c->N;
    if (total <= bestTotal) return;
    bestTotal = total;
    bestB = B;
    bestM = c->m;
    bestK = c->k;
    bestR = c->r;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            bestTgt[i][t] = tgt[i][t];
            bestVol[i][t] = vol[i][t];
        }
}

/* Binary search for a feasible candidate in [lo, hi], then extend upward. */
static void search_phase(int B, int lo, int hi, double until) {
    int ia, ib;
    range_of(lo, hi, &ia, &ib);
    if (ia >= ib) return;
    int a = ia, b = ib - 1, bestIdx = -1;
    while (a <= b && now() < until) {
        int mid = (a + b) / 2;
        double rem = until - now();
        double slice = rem * 0.15;
        if (slice < 1.5) slice = 1.5;
        if (slice > rem) slice = rem;
        setup_group(cand[mid].m, cand[mid].k, cand[mid].r);
        if (search_group(B, now() + slice)) {
            record(B, &cand[mid]);
            bestIdx = mid;
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }
    if (bestIdx < 0) return;
    int fails = 0, idx = bestIdx + 1;
    while (idx < ib && now() < until && fails < 2) {
        double rem = until - now();
        double slice = rem * 0.5;
        if (slice < 1.5) slice = 1.5;
        if (slice > rem) slice = rem;
        setup_group(cand[idx].m, cand[idx].k, cand[idx].r);
        if (search_group(B, now() + slice)) {
            record(B, &cand[idx]);
            bestIdx = idx;
            fails = 0;
        } else {
            fails++;
        }
        idx++;
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 7) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long lowT = atol(argv[5]);
    long maxT = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3 || t_end - t0 < 2.0) { printf("0 0\n"); return 0; }
    double span = t_end - t0;

    int lo_all = 1 << 30, hi_all = 0;
    for (int B = 1; B <= MAXB; B++) {
        int lo = lo_of(B, lowT), hi = hi_of(B, maxT);
        if (lo <= hi) {
            if (lo < lo_all) lo_all = lo;
            if (hi > hi_all) hi_all = hi;
        }
    }
    if (lo_all > hi_all) { printf("0 0\n"); return 0; }
    build_cands(lo_all, hi_all);

    static const int order[4] = {3, 2, 1, 4};
    static const double ends[4] = {0.35, 0.65, 0.85, 1.0};
    for (int p = 0; p < 4; p++) {
        int B = order[p];
        int lo = lo_of(B, lowT), hi = hi_of(B, maxT);
        if (lo <= hi) search_phase(B, lo, hi, t0 + ends[p] * span);
    }

    if (bestTotal == 0) { printf("0 0\n"); return 0; }

    /* Rebuild the best graph. */
    int B = bestB;
    setup_group(bestM, bestK, bestR);
    curB = B;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) tgt[i][t] = bestTgt[i][t];
    if (!set_incidence(B)) { printf("0 0\n"); return 0; }
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) set_dart(i, t, bestVol[i][t]);

    int N = GN, BN = B * N, V = 2 * BN, E = BN * d;
    static int adj[2 * MAXB * MAXN][MAXD];
    for (int v = 0; v < BN; v++) {
        int i = v / N, g = v % N;
        for (int t = 0; t < d; t++) adj[v][t] = BN + tgt[i][t] * N + fw[i][t][g];
    }
    for (int w = BN; w < V; w++) {
        int j = (w - BN) / N, x = (w - BN) % N;
        for (int k = 0; k < d; k++) {
            int i = incI[j][k], t = incT[j][k];
            adj[w][k] = i * N + bw[i][t][x];
        }
    }

    /* Simplicity: no repeated neighbour anywhere. */
    for (int v = 0; v < V; v++)
        for (int k = 0; k < d; k++)
            for (int l = 0; l < k; l++)
                if (adj[v][k] == adj[v][l]) { printf("0 0\n"); return 0; }

    /* Full diameter check when cheap; the symmetry argument covers the rest. */
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
            if (tail != V) { printf("0 0\n"); return 0; }
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

    # Metacyclic multi-orbit lifts. The C search only accepts totals above the
    # Python fallback, and the upper bound is the Moore bound capped for safety.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        maxT = min(mb, 12000)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
        if budget > 4.0:
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, seed, round(budget, 2), best[0], maxT],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
