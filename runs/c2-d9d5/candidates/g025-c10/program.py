"""Metacyclic multi-orbit affine lifts for the bipartite degree-diameter problem.

Change in this version: the lift group is no longer F_q x| H. Each candidate group
is the metacyclic group G = Z_m x|_r Z_k with |G| = N = m*k and r^k = 1 mod m,
gcd(r, m) = 1. Elements are (a, b) coded as a*k + b, with (a,b)(c,e) = (a + r^b c, b + e).
Every order N has at least the cyclic group (r = 1), so the search covers every
order, not only the orders of finite fields. Non-abelian choices (r != 1) are
sampled at random.

A base multigraph with B orbits per side (B in {1, 2, 3}) is drawn at random. Dart
(i, t) with voltage v joins L_(i,g) to R_(tgt, g*v). Left translations are
automorphisms, transitive on each orbit, so BFS from the 2B orbit representatives
decides the diameter. Simulated annealing over voltages drives the uncovered count
to zero. The C engine checks simplicity and, for small graphs, runs a full BFS from
every vertex before printing. Python re-checks with lib.is_valid and keeps a valid
fallback.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Metacyclic multi-orbit lifts over G = Z_m x|_r Z_k, B in {1,2,3} orbits per side.
 * Usage: prog d D seed time_limit lo3 hi3 lo1 hi1 lo2 hi2
 * Output: "n m" then m lines "u v", or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXB 3
#define MAXD 32
#define MAXN 4800
#define MAXV (2 * MAXB * MAXN)
#define MAXVAR 8192

typedef struct { int m, k, r; } Var;

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;
static int LO[4], HI[4];

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
static int powmod_i(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* ------------------------------------------------------------ group Z_m x|_r Z_k */

static int GM, GK, GR, GN;
static int pwr[MAXN];   /* pwr[b] = r^b mod m */

static void setup_group(Var v) {
    GM = v.m;
    GK = v.k;
    GR = v.r;
    GN = GM * GK;
    pwr[0] = 1 % GM;
    for (int b = 1; b < GK; b++)
        pwr[b] = (int)((long long)pwr[b - 1] * GR % GM);
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int na = (int)((a + (long long)pwr[b] * c) % GM);
    int nb = (b + e) % GK;
    return na * GK + nb;
}

static inline int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int t = (int)((long long)pwr[nb] * a % GM);
    int na = (GM - t) % GM;
    return na * GK + nb;
}

/* All admissible groups of order N: m*k = N, m >= 3, r^k = 1 mod m, gcd(r, m) = 1. */
static Var vars[MAXVAR];
static int nvar = 0;

static void make_vars(int N) {
    nvar = 0;
    for (int k = 1; k <= N; k++) {
        if (N % k) continue;
        int m = N / k;
        if (m < 3) continue;
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod_i(r, k, m) != 1 % m) continue;
            if (nvar < MAXVAR) {
                vars[nvar].m = m;
                vars[nvar].k = k;
                vars[nvar].r = r;
                nvar++;
            }
        }
    }
}

/* ------------------------------------------------------------ lift state */

static int curB;
static int tgt[MAXB][MAXD], vol[MAXB][MAXD];
static int fw[MAXB][MAXD][MAXN], bw[MAXB][MAXD][MAXN];
static int incI[MAXB][MAXD], incT[MAXB][MAXD];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static int bestTotal = 0, bestB, bestN, bestGM, bestGK, bestGR;
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

/* Annealing over voltages for one fixed group; restarts draw new bases.
 * Returns 1 with a simple cost-0 state in tgt/vol, 0 on timeout. */
static int search_var(Var v, int B, double until) {
    setup_group(v);
    curB = B;
    int N = GN;
    const int iters = 10000;
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
        if (cost == 0 && simple_state(B)) return 1;
    }
    return 0;
}

/* Try several random groups of order N until one succeeds or time runs out. */
static int search_N(int B, int N, double until) {
    make_vars(N);
    if (nvar == 0) return 0;
    while (now() < until) {
        Var v = vars[rndint(nvar)];
        double rem = until - now();
        double chunk = rem * 0.35;
        if (chunk < 0.6) chunk = 0.6;
        if (chunk > rem) chunk = rem;
        if (search_var(v, B, now() + chunk)) return 1;
    }
    return 0;
}

static void record(int B, int N) {
    int total = 2 * B * N;
    if (total <= bestTotal) return;
    bestTotal = total;
    bestB = B;
    bestN = N;
    bestGM = GM;
    bestGK = GK;
    bestGR = GR;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            bestTgt[i][t] = tgt[i][t];
            bestVol[i][t] = vol[i][t];
        }
}

static int feasible(int B, int N, double until) {
    if (search_N(B, N, until)) {
        record(B, N);
        return 1;
    }
    return 0;
}

/* Binary search for a feasible order in [lo, hi]. */
static void search_phase(int B, int lo, int hi, double until) {
    if (lo > hi) return;
    int a = lo, b = hi;
    while (a <= b && now() < until) {
        int mid = a + (b - a) / 2;
        double rem = until - now();
        double slice = rem * 0.25;
        if (slice < 1.5) slice = 1.5;
        if (slice > rem) slice = rem;
        if (feasible(B, mid, now() + slice))
            a = mid + 1;
        else
            b = mid - 1;
    }
}

/* Extend the best family upward from its current order. */
static void extend(int B, int hi, double until) {
    if (bestTotal == 0 || bestB != B) return;
    int fails = 0, N = bestN + 1;
    while (N <= hi && now() < until && fails < 3) {
        double rem = until - now();
        double slice = rem * 0.4;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (feasible(B, N, now() + slice)) {
            fails = 0;
            N = bestN + 1;
        } else {
            fails++;
            N++;
        }
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 11) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo3 = atoi(argv[5]), hi3 = atoi(argv[6]);
    int lo1 = atoi(argv[7]), hi1 = atoi(argv[8]);
    int lo2 = atoi(argv[9]), hi2 = atoi(argv[10]);
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (hi3 > MAXN - 1) hi3 = MAXN - 1;
    if (hi1 > MAXN - 1) hi1 = MAXN - 1;
    if (hi2 > MAXN - 1) hi2 = MAXN - 1;
    if (lo3 < 2 * d) lo3 = 2 * d;
    if (lo1 < 2 * d) lo1 = 2 * d;
    if (lo2 < 2 * d) lo2 = 2 * d;
    LO[1] = lo1; HI[1] = hi1;
    LO[2] = lo2; HI[2] = hi2;
    LO[3] = lo3; HI[3] = hi3;

    double span = t_end - t0;

    /* Phase A: B = 3 (6N vertices). */
    search_phase(3, lo3, hi3, t0 + 0.40 * span);
    /* Phase B: B = 1 (2N vertices). */
    search_phase(1, lo1, hi1, t0 + 0.55 * span);
    /* Phase C: B = 2 (4N vertices). */
    search_phase(2, lo2, hi2, t0 + 0.70 * span);
    /* Phase D: extend the best family with the remaining time. */
    if (bestTotal > 0) extend(bestB, HI[bestB], t_end);

    if (bestTotal == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Rebuild the best graph. */
    int B = bestB;
    Var bv = {bestGM, bestGK, bestGR};
    setup_group(bv);
    curB = B;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) tgt[i][t] = bestTgt[i][t];
    if (!set_incidence(B)) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) set_dart(i, t, bestVol[i][t]);

    int N = GN, BN = B * N, V = 2 * BN, E = BN * d;
    static int adj[MAXV][MAXD];
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
                if (adj[v][k] == adj[v][l]) {
                    printf("0 0\n");
                    return 0;
                }

    /* Full diameter check from every vertex when cheap. */
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

    # Metacyclic multi-orbit lifts: B = 3 gives 6N vertices, B = 1 gives 2N, B = 2 gives 4N.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        # Leave room for the one-time C compile and the Python checks.
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 3.0
        lo3 = max(2 * d, best[0] // 6 + 1, mb // 24)
        hi3 = mb // 6
        lo1 = max(2 * d, best[0] // 2 + 1, mb // 8)
        hi1 = mb // 2
        lo2 = max(2 * d, mb // 16)
        hi2 = mb // 4
        if budget > 4.0 and (lo3 <= hi3 or lo1 <= hi1 or lo2 <= hi2):
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, seed, round(budget, 2),
                                  lo3, hi3, lo1, hi1, lo2, hi2],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
