"""Metacyclic-group two-orbit lifts for the bipartite degree-diameter problem.

New idea in this version: the parent only searches affine groups F_q x| H, which
exist for few orders. Here the C engine searches metacyclic groups
Z_m x|_r Z_k (element (a,b), (a,b)(c,d) = (a + r^b c, b + d), r^k = 1 mod m).
These exist for every order N = m*k, with k <= 24, and cover all orders in the
search window, including the orders between affine-group values where the
parent has no candidates. Cyclic (k = 1) and abelian (r = 1) groups are included.

Search changes: a binary search over the ORDER N (not over a sorted candidate
index), where each probe tries a few random groups of that order. A linear
extension then climbs above the best order and stops after two consecutive
failed orders. The two-orbit B = 2 phase gets a short slice first, since the
single-orbit phase is the one that wins for the target. Voltages are found by
simulated annealing on the number of unreached pairs from the representatives
L_e and R_e (left translations are automorphisms). Before output the C engine
re-checks the whole graph with a full BFS from every vertex when it is small
enough. Python checks the result with lib.is_valid and keeps a valid fallback.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Metacyclic two-orbit lifts.
 * Group G = Z_m x|_r Z_k, element (a,b) coded a*k+b, identity 0.
 * Left vertex (i,g) ~ right vertex (j, g*v) for each dart (i,t) with tgt[i][t] = j,
 * voltage v. Left translations are automorphisms, transitive on each orbit, so
 * BFS from L_(i,e) and R_(j,e) decides the diameter.
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

#define MAXN 4800
#define MAXD 32
#define MAXB 2
#define MAXK 24
#define MAXCAND 300000

typedef struct { int m, k, r, N; } Cand;

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
static double clampd(double x, double lo, double hi) {
    if (x < lo) x = lo;
    if (x > hi) x = hi;
    return x;
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

/* ------------------------------------------------------------ group Z_m x|_r Z_k */

static int GM = 1, GK = 1, GR = 1, GN = 1;
static int RPW[MAXK];   /* RPW[b] = r^b mod m */

static void setup_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GR = r;
    GN = m * k;
    long p = 1 % m;
    for (int b = 0; b < k; b++) {
        RPW[b] = (int)p;
        p = (p * r) % m;
    }
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int na = (int)((a + (long)RPW[b] * c) % GM);
    int nb = (b + e) % GK;
    return na * GK + nb;
}

static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int na = (int)(((long)GM - ((long)RPW[nb] * a) % GM) % GM);
    return na * GK + nb;
}

/* ------------------------------------------------------------ lift state */

static int curB, curA;
static int tgt[MAXB][MAXD], vol[MAXB][MAXD];
static int fw[MAXB][MAXD][MAXN], bw[MAXB][MAXD][MAXN];
static int incI[MAXB][2 * MAXD], incT[MAXB][2 * MAXD];
static int vis[2 * MAXB * MAXN], que[2 * MAXB * MAXN];
static int stamp_ = 0;

static int bestTotal = 0, bestB, bestA, bestM, bestK, bestR;
static int bestVol[MAXB][MAXD];

/* B = 1: all darts to R0. B = 2: L0 -> R0 (a darts), L0 -> R1 (d-a), L1 -> R0 (d-a), L1 -> R1 (a). */
static void set_pattern(int B, int a) {
    curB = B;
    curA = a;
    for (int t = 0; t < d; t++) {
        if (B == 1) {
            tgt[0][t] = 0;
        } else {
            tgt[0][t] = (t < a) ? 0 : 1;
            tgt[1][t] = (t < a) ? 1 : 0;
        }
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

/* Dart (i,t) has voltage x: fw maps g to g*x, bw maps y to y*x^-1. */
static void set_dart(int i, int t, int x) {
    vol[i][t] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fw[i][t][g] = gmul(g, x);
        bw[i][t][g] = gmul(g, xi);
    }
}

/* Darts into the same right orbit need distinct voltages so the graph stays simple. */
static int valid_value(int i, int t, int x, int limit) {
    for (int t2 = 0; t2 < limit; t2++)
        if (t2 != t && tgt[i][t2] == tgt[i][t] && vol[i][t2] == x) return 0;
    return 1;
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

/* Unreached pairs from the representatives L_(i,e) and R_(j,e). */
static long cover_cost(void) {
    int N = GN, V = 2 * curB * N;
    long cost = 0;
    for (int i = 0; i < curB; i++) cost += (long)(V - bfs_count(i * N));
    for (int j = 0; j < curB; j++) cost += (long)(V - bfs_count((curB + j) * N));
    return cost;
}

/* Simulated annealing over the voltages for the group already set up.
 * Returns 1 with a cost-0 state left in vol/curA, 0 on timeout. */
static int search_group(double until) {
    int N = GN, B = curB;
    const int iters = 8000;
    while (now() < until) {
        int a = (B == 1) ? d : 1 + rndint(d / 2);
        set_pattern(B, a);
        for (int i = 0; i < B; i++)
            for (int t = 0; t < d; t++) {
                int x, tries = 0;
                do { x = rndint(N); tries++; } while (!valid_value(i, t, x, t) && tries < 100000);
                set_dart(i, t, x);
            }
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
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
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ candidate groups */

static Cand cand[MAXCAND];
static int nc = 0;

static int cmpN(const void *x, const void *y) {
    const Cand *p = x, *q = y;
    if (p->N != q->N) return p->N - q->N;
    if (p->k != q->k) return p->k - q->k;
    return p->r - q->r;
}

static void add_cand(int m, int k, int r) {
    if (nc >= MAXCAND) return;
    cand[nc].m = m;
    cand[nc].k = k;
    cand[nc].r = r;
    cand[nc].N = m * k;
    nc++;
}

/* Every order N in [lo, hi] gets the cyclic group, the abelian groups Z_m x Z_k,
 * and up to two random non-abelian metacyclic groups per (m, k) with r^k = 1 mod m. */
static void build_cands(int lo, int hi) {
    nc = 0;
    for (int N = lo; N <= hi; N++) {
        add_cand(N, 1, 1);
        for (int k = 2; k <= MAXK && k <= N / 2; k++) {
            if (N % k) continue;
            int m = N / k;
            if (m < 2) continue;
            add_cand(m, k, 1);
            int cntv = 0, s1 = -1, s2 = -1;
            for (int r = 2; r < m; r++) {
                if (powmod(r, k, m) != 1 % m) continue;
                cntv++;
                if (cntv == 1) {
                    s1 = r;
                } else if (cntv == 2) {
                    s2 = r;
                } else {
                    int j = rndint(cntv);
                    if (j == 0) s1 = r;
                    else if (j == 1) s2 = r;
                }
            }
            if (s1 > 0) add_cand(m, k, s1);
            if (s2 > 0) add_cand(m, k, s2);
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmpN);
}

static int lower_bound_N(int v) {
    int lo = 0, hi = nc;
    while (lo < hi) {
        int mid = (lo + hi) / 2;
        if (cand[mid].N < v) lo = mid + 1;
        else hi = mid;
    }
    return lo;
}

/* Save the current state if it beats the best total. */
static void record(int B, const Cand *cd) {
    int total = 2 * B * cd->N;
    if (total <= bestTotal) return;
    bestTotal = total;
    bestB = B;
    bestA = curA;
    bestM = cd->m;
    bestK = cd->k;
    bestR = cd->r;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) bestVol[i][t] = vol[i][t];
}

/* Binary search over the order N (each probe tries random groups of that order),
 * then extend upward one order at a time until two orders in a row fail. */
static void search_phase(int B, int lo, int hi, double until) {
    build_cands(lo, hi);
    if (nc == 0) return;
    curB = B;
    double len = until - now();
    if (len <= 0) return;

    int bestN = 0;
    int L = lo, H = hi;
    while (L <= H && now() < until) {
        int mid = (L + H) / 2;
        int s = lower_bound_N(mid), e = lower_bound_N(mid + 1);
        if (s >= e) { H = mid - 1; continue; }
        int ok = 0;
        for (int t = 0; t < 2 && !ok && now() < until; t++) {
            int pick = s + rndint(e - s);
            double rem = until - now();
            double slice = clampd(0.03 * len, 1.5, rem);
            setup_group(cand[pick].m, cand[pick].k, cand[pick].r);
            if (search_group(now() + slice)) {
                record(B, &cand[pick]);
                ok = 1;
            }
        }
        if (ok) {
            bestN = mid;
            L = mid + 1;
        } else {
            H = mid - 1;
        }
    }
    if (bestN == 0) return;

    int fails = 0, N = bestN + 1;
    while (N <= hi && now() < until && fails < 2) {
        int s = lower_bound_N(N), e = lower_bound_N(N + 1);
        int ok = 0;
        for (int t = 0; t < 3 && !ok && s < e && now() < until; t++) {
            int pick = s + rndint(e - s);
            double rem = until - now();
            double slice = clampd(0.1 * len, 1.5, rem);
            setup_group(cand[pick].m, cand[pick].k, cand[pick].r);
            if (search_group(now() + slice)) {
                record(B, &cand[pick]);
                ok = 1;
            }
        }
        if (ok) fails = 0;
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

    double span = t_end - t0;
    if (lo2 <= hi2) search_phase(2, lo2, hi2, t0 + 0.12 * span);
    if (bestTotal / 2 + 1 > lo1) lo1 = bestTotal / 2 + 1;
    if (lo1 <= hi1 && now() < t_end) search_phase(1, lo1, hi1, t_end);

    if (bestTotal == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Rebuild the best graph. */
    setup_group(bestM, bestK, bestR);
    set_pattern(bestB, bestA);
    for (int i = 0; i < bestB; i++)
        for (int t = 0; t < d; t++) set_dart(i, t, bestVol[i][t]);

    int N = GN, BN = bestB * N, V = 2 * BN, E = BN * d;
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

    /* Full BFS from every vertex when cheap, so the output is never invalid. */
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

    # Metacyclic lifts. Order N gives 4N vertices (B = 2) or 2N (B = 1).
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        lo2 = max(2 * d, best[0] // 4 + 1, mb // 16)
        hi2 = mb // 4
        lo1 = max(2 * d, best[0] // 2 + 1, mb // 8)
        hi1 = mb // 2
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
