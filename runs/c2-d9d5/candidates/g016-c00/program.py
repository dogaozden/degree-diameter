"""Multi-orbit bi-Cayley lift search for the bipartite degree-diameter problem.

Change of construction: the parent searched single-orbit Haar graphs (B = 1) over
affine groups F_q x| H. This version uses B orbits per side. Vertices are (i, g) on
the left and (j, h) on the right, with i, j in 0..B-1 and g, h in a group G of order N.
Each of the d "rounds" t is a permutation sigma_t of {0..B-1}, and it contributes one dart
(i, sigma_t(i), s) per left orbit i, where s in G is a voltage. Edge: (i, g) ~ (j, g*s).
Every left and right vertex then has degree d, and the graph is bipartite with 2BN
vertices. Simplicity holds because darts that share an orbit pair get distinct voltages.

G ranges over semidirect products Z_m x| Z_k (cyclic when r = 1), with the group and
the orbit structure both random. Left translations are automorphisms, so the diameter
check needs only 2B BFS runs (one from each orbit base vertex). Simulated annealing
minimises the total number of vertices left uncovered. The target order is found by
bisection over the total vertex count, with random B on each attempt.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit bi-Cayley lift search over semidirect groups Z_m x| Z_k.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXB 6
#define MAXD 32
#define MAXDART (MAXB * MAXD)
#define MAXV 8192
#define MAXE 400000

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

/* Group multiplication table and inverses for the current group (order NN). */
static int MT[MAXN * MAXN];
static int INV[MAXN];
static int NN;   /* orbit size = group order */
static int Bn;   /* orbits per side */

/* Darts: index t*B + i is the dart of round t from left orbit i to right orbit perm_t(i). */
static int dart_i[MAXDART], dart_j[MAXDART], dart_s[MAXDART];
static int Ldarts[MAXB][MAXD], Rdarts[MAXB][MAXD];
static int fw[MAXDART][MAXN], bw[MAXDART][MAXN];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static int best_n = 0, best_m = 0;
static int best_eu[MAXE], best_ev[MAXE];

/* Semidirect product Z_m x| Z_k with r^k = 1 mod m, gcd(r, m) = 1.
 * Element (a, b) is coded as a*k + b; (a, b)(c, e) = (a + r^b c, b + e). */
static void setup_group(int N) {
    NN = N;
    int divs[MAXN], nd = 0;
    for (int x = 1; x <= N; x++)
        if (N % x == 0) divs[nd++] = x;
    int k = divs[rndint(nd)];
    int m = N / k;
    int r = 0;
    if (m > 1) {
        r = 1;
        for (int tr = 0; tr < 200; tr++) {
            int c = 1 + rndint(m - 1);
            if (gcd_i(c, m) != 1) continue;
            long x = 1;
            for (int e = 0; e < k; e++) x = x * c % m;
            if (x == 1) { r = c; break; }
        }
    }
    int pw[MAXN];
    pw[0] = (m > 1) ? 1 : 0;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            int na = (a + pw[b] * c) % m;
            int nb = (b + e) % k;
            MT[x * N + y] = na * k + nb;
        }
    }
    for (int x = 0; x < N; x++) {
        INV[x] = 0;
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INV[x] = y; break; }
    }
}

/* Random round permutations give a balanced orbit structure: each left and right orbit
 * has exactly d darts. */
static void setup_structure(void) {
    int B = Bn;
    int nL[MAXB], nR[MAXB];
    for (int i = 0; i < MAXB; i++) { nL[i] = 0; nR[i] = 0; }
    for (int t = 0; t < d; t++) {
        int p[MAXB];
        for (int i = 0; i < B; i++) p[i] = i;
        for (int i = B - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < B; i++) {
            int idx = t * B + i;
            dart_i[idx] = i;
            dart_j[idx] = p[i];
            dart_s[idx] = -1;
        }
    }
    for (int idx = 0; idx < B * d; idx++) {
        int i = dart_i[idx], j = dart_j[idx];
        Ldarts[i][nL[i]++] = idx;
        Rdarts[j][nR[j]++] = idx;
    }
}

/* True if voltage s for dart idx does not repeat on another dart of the same orbit pair. */
static int ok_volt(int idx, int s) {
    int nd = Bn * d;
    for (int o = 0; o < nd; o++)
        if (o != idx && dart_i[o] == dart_i[idx] && dart_j[o] == dart_j[idx] && dart_s[o] == s)
            return 0;
    return 1;
}

static void set_dart(int idx, int s) {
    dart_s[idx] = s;
    int si = INV[s];
    for (int g = 0; g < NN; g++) {
        fw[idx][g] = MT[g * NN + s];
        bw[idx][g] = MT[g * NN + si];
    }
}

/* Vertices: left (i, g) = i*NN + g; right (j, h) = Bn*NN + j*NN + h.
 * Left (i,g) ~ right (j, g*s) for each dart (i, j, s). */
static int bfs_count(int src) {
    int BN = Bn * NN;
    int V = 2 * BN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail && tail < V; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int i = v / NN, g = v % NN;
                for (int k = 0; k < d; k++) {
                    int t = Ldarts[i][k];
                    int u = BN + dart_j[t] * NN + fw[t][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - BN;
                int j = w / NN, h = w % NN;
                for (int k = 0; k < d; k++) {
                    int t = Rdarts[j][k];
                    int u = dart_i[t] * NN + bw[t][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left translations and right translations are automorphisms, so one BFS per orbit
 * base vertex decides the diameter. Cost = number of uncovered (source, target) pairs. */
static long cost_all(void) {
    int BN = Bn * NN;
    int V = 2 * BN;
    long c = 0;
    for (int i = 0; i < Bn; i++) c += V - bfs_count(i * NN);
    for (int j = 0; j < Bn; j++) c += V - bfs_count(BN + j * NN);
    return c;
}

static void save_solution(void) {
    int BN = Bn * NN;
    int m = 0;
    for (int t = 0; t < Bn * d; t++)
        for (int g = 0; g < NN; g++) {
            best_eu[m] = dart_i[t] * NN + g;
            best_ev[m] = BN + dart_j[t] * NN + fw[t][g];
            m++;
        }
    best_n = 2 * BN;
    best_m = m;
}

/* Restart simulated annealing with fresh random groups and structures until success
 * or the deadline. Returns 1 on success (solution saved). */
static int attempt(int B, int N, double until) {
    Bn = B;
    int nd = B * d;
    while (now() < until) {
        setup_group(N);
        setup_structure();
        for (int idx = 0; idx < nd; idx++) {
            int s;
            do { s = rndint(N); } while (!ok_volt(idx, s));
            set_dart(idx, s);
        }
        long cost = cost_all();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        const int iters = 6000;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int idx = rndint(nd);
            int old = dart_s[idx];
            int s;
            do { s = rndint(N); } while (s == old || !ok_volt(idx, s));
            set_dart(idx, s);
            long c2 = cost_all();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_dart(idx, old);
            }
        }
        if (cost == 0) {
            save_solution();
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
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (hi > MAXV) hi = MAXV;
    if (lo < 2 * (d + 1)) lo = 2 * (d + 1);

    /* Bisection over the total vertex count T = 2*B*N, with random B per attempt.
     * Invariant: candidates lie in (bestT, hiT]. */
    int bestT = lo - 1, hiT = hi;
    while (now() < t_end - 0.3) {
        if (bestT >= hi) break;
        if (hiT <= bestT) {
            hiT = bestT + 8;
            if (hiT > hi) hiT = hi;
        }
        int mid = (bestT + 1 + hiT) / 2;
        int B = 0, Nt = 0, found = 0;
        for (int tr = 0; tr < 30 && !found; tr++) {
            int Bc = 1 + rndint(MAXB);
            int Nmin = bestT / (2 * Bc) + 1;
            if (Nmin < d + 1) Nmin = d + 1;
            int Nt0 = (mid + Bc) / (2 * Bc);
            if (Nt0 < Nmin) Nt0 = Nmin;
            if (Nt0 > MAXN) continue;
            if (2 * Bc * Nt0 > hi) continue;
            B = Bc;
            Nt = Nt0;
            found = 1;
        }
        if (!found) break;
        double rem = t_end - now();
        if (rem < 0.3) break;
        double slice = 0.25 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        int T2 = 2 * B * Nt;
        if (attempt(B, Nt, now() + slice)) {
            bestT = T2;
        } else {
            if (T2 - 1 < hiT) hiT = T2 - 1;
        }
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++)
        printf("%d %d\n", best_eu[i], best_ev[i]);
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

    # Search: multi-orbit bi-Cayley lifts over semidirect groups.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] // 2 + 1, mb // 8)
        hi = mb // 3
        if budget > 2.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
