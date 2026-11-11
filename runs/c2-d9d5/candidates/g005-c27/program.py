"""Base-voltage lift search over semidirect groups for the bipartite degree-diameter problem.

Replaces the affine-group Haar engine with a broader family. The base graph has B
vertices per side (B = 1, 2, 3). Each A-vertex has d darts, and dart t of A_i goes to
B_{perm_t(i)} with a voltage v[i][t] in a group G = Z_m x| Z_k. The lift has vertices
(A_i, x) and (B_j, y), with edges (A_i, x) ~ (B_j, x*v) for each dart. Constraints:

- Every vertex has degree exactly d and the graph is bipartite.
- Darts into the same B-fibre use distinct voltages, so the graph is simple.
- G acts by left translation, so diameter <= D reduces to 2B BFS runs, one per base vertex.

The C engine picks random semidirect products Z_m x| Z_k of each target order, random
base permutations and voltages, and runs simulated annealing on the number of
unreached (vertex, root) pairs. Each base size B gets a binary search over the group
order, and leftover time is spent trying one order above the best feasible one.

Python keeps the projective-plane, Araujo-Lopez and W(q) baselines and the K_{d,d}
fallback. Every returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Base-voltage lift search over Z_m x| Z_k.
 * Usage: prog d D seed time_limit lo_n hi_n     (stdin ignored)
 * Output: "n m" then m lines "u v" for the best graph found, or "0 0".
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
#define MAXV (1 << 18)
#define MAXN (MAXV / 2)

static int d, D, B, N, V;
static int gm, gk, gr;
static int pw[MAXN];
static int perm[MAXD][MAXB], pinv[MAXD][MAXB];
static int vv[MAXB][MAXD], vi[MAXB][MAXD];
static int visA[MAXV], queueA[MAXV];
static int stampc = 0;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static int bestTotal = 0, bestB = 0, bestN = 0, bestm = 0, bestk = 0, bestr = 0;
static int bestperm[MAXD][MAXB], bestvv[MAXB][MAXD];

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

static long long gcd_ll(long long a, long long b) {
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Group Z_m x| Z_k, element (a, b) coded as a*k + b, (a,b)(c,e) = (a + r^b c, b + e). */
static void set_group(int m, int kk, int r) {
    gm = m;
    gk = kk;
    gr = r;
    pw[0] = 1 % m;
    for (int b = 1; b < kk; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
}

static inline int gmul(int x, int y) {
    int a = x / gk, b = x - a * gk;
    int c = y / gk, e = y - c * gk;
    long long na = ((long long)a + (long long)pw[b] * c) % gm;
    int nb = b + e;
    if (nb >= gk) nb -= gk;
    return (int)na * gk + nb;
}

static inline int ginv(int x) {
    int a = x / gk, b = x - a * gk;
    int nb = (gk - b) % gk;
    long long na = (gm - ((long long)pw[nb] * a) % gm) % gm;
    return (int)na * gk + nb;
}

/* Uniformly random semidirect product of order N with m >= 2 (cyclic Z_N included). */
static int pick_group(int Nv, int *om, int *ok, int *orr) {
    int cnt = 0;
    for (int m = 2; m <= Nv; m++) {
        if (Nv % m) continue;
        int kk = Nv / m;
        for (int r = 1; r < m; r++) {
            if (gcd_ll(r, m) != 1) continue;
            if (powmod(r, kk, m) != 1) continue;
            cnt++;
            if (rndint(cnt) == 0) { *om = m; *ok = kk; *orr = r; }
        }
    }
    return cnt;
}

static void new_perms(void) {
    for (int t = 0; t < d; t++) {
        int arr[MAXB];
        for (int i = 0; i < B; i++) arr[i] = i;
        for (int i = B - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = arr[i]; arr[i] = arr[j]; arr[j] = tmp;
        }
        for (int i = 0; i < B; i++) {
            perm[t][i] = arr[i];
            pinv[t][arr[i]] = i;
        }
    }
}

/* True if dart t of A_i with voltage g clashes with an earlier dart u < lim. */
static int conflict(int i, int t, int g, int lim) {
    for (int u = 0; u < lim; u++)
        if (u != t && perm[u][i] == perm[t][i] && vv[i][u] == g) return 1;
    return 0;
}

static void init_volt(void) {
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            int g;
            do { g = rndint(N); } while (conflict(i, t, g, t));
            vv[i][t] = g;
            vi[i][t] = ginv(g);
        }
}

/* Number of vertices within distance D of root. */
static int bfs_reach(int root) {
    stampc++;
    int head = 0, tail = 0;
    queueA[tail++] = root;
    visA[root] = stampc;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int u = queueA[head++];
            int f = u / N, x = u - f * N;
            if (f < B) {
                for (int t = 0; t < d; t++) {
                    int w = (B + perm[t][f]) * N + gmul(x, vv[f][t]);
                    if (visA[w] != stampc) { visA[w] = stampc; queueA[tail++] = w; }
                }
            } else {
                int j = f - B;
                for (int t = 0; t < d; t++) {
                    int i = pinv[t][j];
                    int w = i * N + gmul(x, vi[i][t]);
                    if (visA[w] != stampc) { visA[w] = stampc; queueA[tail++] = w; }
                }
            }
        }
    }
    return tail;
}

/* Sum over the 2B fibre roots of the vertices not reached within D. */
static long cover_cost(void) {
    long c = 0;
    for (int f = 0; f < 2 * B; f++) c += (long)(V - bfs_reach(f * N));
    return c;
}

static void save_best(void) {
    bestTotal = 2 * B * N;
    bestB = B;
    bestN = N;
    bestm = gm;
    bestk = gk;
    bestr = gr;
    memcpy(bestperm, perm, sizeof(perm));
    memcpy(bestvv, vv, sizeof(vv));
}

/* Random restarts with simulated annealing for base size Bv and group order Nv.
 * Returns 1 if a valid lift was found before `until`. */
static int probe(int Bv, int Nv, double until) {
    B = Bv;
    N = Nv;
    V = 2 * B * N;
    const int iters = 5000;
    while (now() < until) {
        int m, kk, r;
        if (!pick_group(N, &m, &kk, &r)) return 0;
        set_group(m, kk, r);
        new_perms();
        init_volt();
        long cost = cover_cost();
        if (cost > 0) {
            double c0 = (double)cost;
            double Ts = 0.05 * c0 + 1.0, Te = 0.3;
            for (int it = 0; it < iters && cost > 0; it++) {
                if ((it & 15) == 0 && now() > until) break;
                double T = Ts * pow(Te / Ts, (double)it / iters);
                int i = rndint(B), t = rndint(d);
                int g = rndint(N);
                if (conflict(i, t, g, d)) continue;
                int old = vv[i][t], oldi = vi[i][t];
                vv[i][t] = g;
                vi[i][t] = ginv(g);
                long c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    vv[i][t] = old;
                    vi[i][t] = oldi;
                }
            }
        }
        if (cost == 0) {
            if (2 * B * N > bestTotal) save_best();
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
    long lo_n = atol(argv[5]), hi_n = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (hi_n > MAXV) hi_n = MAXV;

    int loN[MAXB + 1], hiN[MAXB + 1], bestNB[MAXB + 1];
    int nactive = 0;
    for (int b = 1; b <= MAXB; b++) {
        bestNB[b] = 0;
        long lo = lo_n / (2L * b) + 1;   /* 2bN must beat lo_n */
        long hi = hi_n / (2L * b);
        if (lo < d + 1) lo = d + 1;
        loN[b] = (int)lo;
        hiN[b] = (int)hi;
        if (lo <= hi) nactive++;
    }

    /* Phase 1: per base size, binary search for the largest feasible order. */
    int done = 0;
    for (int b = 1; b <= MAXB; b++) {
        if (loN[b] > hiN[b]) continue;
        double share = (t_end - now()) / (double)(nactive - done);
        done++;
        double tb_end = now() + share;
        int lo = loN[b], hi = hiN[b];
        while (lo <= hi && now() < tb_end) {
            int mid = lo + (hi - lo) / 2;
            double rem = tb_end - now();
            double slice = rem * 0.35;
            if (slice < 0.5) slice = 0.5;
            if (slice > rem) slice = rem;
            if (probe(b, mid, now() + slice)) {
                if (mid > bestNB[b]) bestNB[b] = mid;
                lo = mid + 1;
            } else {
                hi = mid - 1;
            }
        }
    }

    /* Phase 2: leftover time on one order above the best feasible for each base size. */
    int rr = MAXB;
    while (now() < t_end - 0.5) {
        int pick = -1;
        for (int s = 1; s <= MAXB && pick < 0; s++) {
            int b = 1 + ((rr - 1 + s) % MAXB);
            if (loN[b] > hiN[b]) continue;
            int target = bestNB[b] > 0 ? bestNB[b] + 1 : loN[b];
            if (target <= hiN[b]) pick = b;
        }
        if (pick < 0) break;
        rr = pick;
        int target = bestNB[pick] > 0 ? bestNB[pick] + 1 : loN[pick];
        double rem = t_end - now();
        double slice = rem * 0.5;
        if (slice < 0.5) slice = 0.5;
        if (slice > rem) slice = rem;
        if (probe(pick, target, now() + slice)) bestNB[pick] = target;
    }

    if (bestTotal == 0) {
        printf("0 0\n");
        return 0;
    }
    B = bestB;
    N = bestN;
    V = 2 * B * N;
    set_group(bestm, bestk, bestr);
    memcpy(perm, bestperm, sizeof(perm));
    memcpy(vv, bestvv, sizeof(vv));
    printf("%d %d\n", 2 * B * N, B * N * d);
    for (int i = 0; i < B; i++)
        for (int x = 0; x < N; x++)
            for (int t = 0; t < d; t++)
                printf("%d %d\n", i * N + x, (B + perm[t][i]) * N + gmul(x, vv[i][t]));
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

    # Base-voltage lifts over semidirect groups. Needs n = 2BN <= moore bound.
    if d >= 2 and D >= 3 and d <= 32:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        if budget > 2.0 and best[0] < mb:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0], mb],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
