"""Metacyclic Cayley-type bipartite lifts for the bipartite degree-diameter problem.

Bold change from the parent: instead of affine groups F_q x| C_c with two orbits,
this version uses single-orbit lifts over every metacyclic group Z_m x|_r Z_k
(gcd(r, m) = 1, r^k = 1 mod m). The graph has vertices L_x and R_y, x, y in G, and
d distinct darts g_1..g_d with L_x ~ R_{x g_i}. Left and right multiplication are
the automorphisms that make each side transitive, so diameter <= D is decided by
two BFS runs (from L_e and R_e). The search is simulated annealing over the dart
set, run over many group orders N in a narrow window just above the current best
(which is 2N vertices). Groups of order N are sampled at random, so the search is
not limited to prime-power fields. Fallbacks are K_{d,d}, PG(2,q) incidence,
Araujo-Pardo-Lopez and W(q), and every result is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Metacyclic single-orbit Cayley bipartite search.
 * Usage: prog d D seed time_limit lo hi
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 * Vertices: left x in [0,N), right N+y, edges x -- N + x*g_i.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4000
#define MAXD 32

static int d, D, N;
static double t_end;
static uint64_t rs = 88172645463325252ULL;
static uint16_t *MUL = NULL;
static int *INV = NULL, *RP = NULL, *YA = NULL, *YE = NULL;
static int g[MAXD];
static int vis[2 * MAXN];
static int que[2 * MAXN];
static int stamp_ = 0;

static int have_best = 0, bestN = 0, bestM = 0, bestK = 0, bestR = 0;
static int bestG[MAXD];

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
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
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

static int valid_triple(int m, int k, int r) {
    if (gcd_i(r, m) != 1) return 0;
    return powmod(r, k, m) == 1 % m;
}

/* Uniformly pick a metacyclic triple (m, k, r) with m*k = Nv. */
static int pick_group(int Nv, int *pm, int *pk, int *pr) {
    long cnt = 0;
    for (int k = 1; k <= Nv; k++) {
        if (Nv % k) continue;
        int m = Nv / k;
        for (int r = 0; r < m; r++)
            if (valid_triple(m, k, r)) cnt++;
    }
    if (cnt == 0) return 0;
    long t = (long)(rnd() % (uint64_t)cnt);
    for (int k = 1; k <= Nv; k++) {
        if (Nv % k) continue;
        int m = Nv / k;
        for (int r = 0; r < m; r++) {
            if (valid_triple(m, k, r)) {
                if (t == 0) {
                    *pm = m;
                    *pk = k;
                    *pr = r;
                    return 1;
                }
                t--;
            }
        }
    }
    return 0;
}

/* Element (a, b) is coded a*k + b; (a,b)(c,e) = (a + r^b c, b + e). */
static void build_group(int m, int k, int r) {
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long long)RP[b - 1] * r % m);
    for (int y = 0; y < N; y++) {
        YA[y] = y / k;
        YE[y] = y % k;
    }
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        long long rb = RP[b];
        for (int y = 0; y < N; y++) {
            int na = (int)(((long long)a + rb * YA[y]) % m);
            MUL[(size_t)x * N + y] = (uint16_t)(na * k + (b + YE[y]) % k);
        }
    }
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++)
            if (MUL[(size_t)x * N + y] == 0) {
                INV[x] = y;
                break;
            }
    }
}

/* Number of vertices reached within distance D of src. */
static int bfs_reach(int src) {
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < N) {
                const uint16_t *row = MUL + (size_t)v * N;
                for (int i = 0; i < d; i++) {
                    int u = N + row[g[i]];
                    if (vis[u] != stamp_) {
                        vis[u] = stamp_;
                        que[tail++] = u;
                    }
                }
            } else {
                const uint16_t *row = MUL + (size_t)(v - N) * N;
                for (int i = 0; i < d; i++) {
                    int u = row[INV[g[i]]];
                    if (vis[u] != stamp_) {
                        vis[u] = stamp_;
                        que[tail++] = u;
                    }
                }
            }
        }
    }
    return tail;
}

/* Unreached vertices from L_e and R_e; zero iff the graph has diameter <= D. */
static long cover_cost(void) {
    long V = 2L * N;
    return (V - bfs_reach(0)) + (V - bfs_reach(N));
}

static void random_init(void) {
    for (int i = 0; i < d; i++) {
        int x, ok;
        do {
            x = rndint(N);
            ok = 1;
            for (int j = 0; j < i; j++)
                if (g[j] == x) {
                    ok = 0;
                    break;
                }
        } while (!ok);
        g[i] = x;
    }
}

/* One annealing run from a random dart set. Returns 1 on success (g holds the solution). */
static int sa_run(double until, int iters) {
    random_init();
    long cost = cover_cost();
    if (cost == 0) return 1;
    double c0 = (double)cost;
    double Ts = 0.05 * c0 + 1.0, Te = 0.3;
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 15) == 0 && now() > until) return 0;
        double T = Ts * pow(Te / Ts, (double)it / iters);
        int i = rndint(d), x = rndint(N);
        int dup = 0;
        for (int j = 0; j < d; j++)
            if (g[j] == x) {
                dup = 1;
                break;
            }
        if (dup) continue;
        int old = g[i];
        g[i] = x;
        long c2 = cover_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
        else g[i] = old;
    }
    return cost == 0;
}

/* Try order Nv with random metacyclic groups until success or time runs out. */
static int try_N(int Nv, double until) {
    N = Nv;
    while (now() < until) {
        int m, k, r;
        if (!pick_group(Nv, &m, &k, &r)) return 0;
        build_group(m, k, r);
        if (sa_run(until, 6000)) {
            if (Nv > bestN) {
                bestN = Nv;
                bestM = m;
                bestK = k;
                bestR = r;
                memcpy(bestG, g, sizeof(int) * (size_t)d);
                have_best = 1;
            }
            return 1;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.85 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    if (lo < d) lo = d;
    if (hi > MAXN) hi = MAXN;
    if (lo > hi) {
        printf("0 0\n");
        return 0;
    }
    MUL = malloc(sizeof(uint16_t) * (size_t)MAXN * MAXN);
    INV = malloc(sizeof(int) * MAXN);
    RP = malloc(sizeof(int) * MAXN);
    YA = malloc(sizeof(int) * MAXN);
    YE = malloc(sizeof(int) * MAXN);
    if (!MUL || !INV || !RP || !YA || !YE) {
        printf("0 0\n");
        return 0;
    }

    /* Phase 1: binary search over the order window. */
    int li = lo, hiI = hi;
    while (li <= hiI && now() < t_end) {
        int mid = li + (hiI - li) / 2;
        double rem = t_end - now();
        double slice = rem * 0.25;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (try_N(mid, now() + slice))
            li = mid + 1;
        else
            hiI = mid - 1;
    }

    /* Phase 2: spend leftover time on orders just above the best. */
    int fails = 0;
    int idx = have_best ? bestN + 1 : lo;
    while (idx <= hi && now() < t_end && fails < 2) {
        double rem = t_end - now();
        double slice = rem * 0.5;
        if (slice > rem) slice = rem;
        if (try_N(idx, now() + slice))
            fails = 0;
        else
            fails++;
        idx++;
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    N = bestN;
    build_group(bestM, bestK, bestR);
    memcpy(g, bestG, sizeof(int) * (size_t)d);
    printf("%d %d\n", 2 * N, N * d);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, N + (int)MUL[(size_t)x * N + g[i]]);
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


def _meta_search(d, D, seed, budget, lo, hi):
    """Run the C metacyclic Cayley search; returns (n, edges)."""
    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                     stdin_graph=None, timeout=budget + 8.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    def left():
        return time_limit - (time.monotonic() - t0)

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
        # Single-orbit metacyclic Cayley lifts: 2N vertices, N just above the current best.
        lo = max(best[0] // 2 + 1, d, 2)
        hi = min(mb // 2, 4000, max(lo, lo * 4 // 3 + 10))
        budget = 0.8 * left() - 2.0
        if budget > 2.0 and lo <= hi:
            try:
                consider(_meta_search(d, D, seed, budget, lo, hi))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
