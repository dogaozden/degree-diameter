"""Multi-orbit random-like voltage lifts for the bipartite degree-diameter problem.

Change in this version: the single-orbit (K = 1) affine lifts that gave the
parent's record are kept as the first stage, but most of the time now goes to
lifts with K left orbits and K right orbits over small groups (K = 3, 4, 6, 8).
Each lift is d-regular and bipartite with 2*K*|G| vertices. Left translations
are automorphisms, so the diameter check needs only 2K BFS runs from orbit
representatives. Larger K gives many more free voltages, so the search is much
closer to random regular graphs, which are the main reason to expect orders
above the single-orbit record.

Groups are semidirect products Z_m x|_r Z_k (affine F_p x| C_k, dihedral, or
cyclic), passed to C as a list. The C engine binary-searches the list with
simulated annealing for each probe. The best valid graph found wins. The
fallbacks (K_{d,d}, projective-plane incidence, Araujo-Pardo-Lopez, and W(q)
for D = 4) are always checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Generic bi-Cayley voltage-lift search over Z_m x|_r Z_k with K orbits.
 * Usage: prog d D seed time_limit K      (stdin: "G 2G" then G group records,
 *   each record is two lines "m k" and "r N", with m*k = N, sorted by N).
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 * Vertex layout: left L^a_x = a*N + x, right R^b_y = K*N + b*N + y.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXK 16
#define MAXD 16
#define MAXND (MAXK * MAXD)
#define MAXN 4096
#define MAXV (2 * MAXK * MAXN)
#define MAXG 40000

static int K, d, D;
static int GORD, GM, GK;
static int PW[MAXN];          /* PW[b] = r^b mod m */
static int nd;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static int tb[MAXND], vg[MAXND];
static int fwd[MAXND][MAXN], bwd[MAXND][MAXN];
static int inc[MAXK][MAXD], cnt_in[MAXK];
static int stv[MAXND], sgv[MAXND];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static int gN[MAXG], gm[MAXG], gk[MAXG], gr[MAXG];
static int NGR = 0;

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

/* Group Z_m x|_r Z_k, element (a, b) coded as a*k + b, (a,b)(c,e) = (a + r^b c, b + e). */
static int set_group(int N, int m, int k, int r) {
    if (m < 1 || k < 1 || N > MAXN || (long)m * k != N) return 0;
    GORD = N;
    GM = m;
    GK = k;
    int cur = 1 % m;
    for (int b = 0; b < k; b++) {
        PW[b] = cur;
        cur = (int)((long)cur * (r % m) % m);
    }
    return cur == 1 % m;
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x - a * GK, c = y / GK, e = y - c * GK;
    int na = (a + (int)((long)PW[b] * c % GM)) % GM;
    int nb = b + e;
    if (nb >= GK) nb -= GK;
    return na * GK + nb;
}

static inline int ginv(int x) {
    int a = x / GK, b = x - a * GK;
    int nb = (GK - b) % GK;
    int na = (int)(((long)(GM - PW[nb]) % GM) * a % GM);
    return na * GK + nb;
}

/* Dart t leaves left orbit t/d: L_x ~ R^{tb[t]}_{x g}. */
static void set_dart(int t, int g) {
    vg[t] = g;
    int ig = ginv(g);
    for (int x = 0; x < GORD; x++) {
        fwd[t][x] = gmul(x, g);
        bwd[t][x] = gmul(x, ig);
    }
}

static void rebuild_inc(void) {
    for (int b = 0; b < K; b++) cnt_in[b] = 0;
    for (int t = 0; t < nd; t++) {
        int b = tb[t];
        if (cnt_in[b] < d) inc[b][cnt_in[b]++] = t;
    }
}

static void random_init(void) {
    int list[MAXND], p = 0;
    for (int b = 0; b < K; b++)
        for (int i = 0; i < d; i++) list[p++] = b;
    for (int i = nd - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tmp = list[i];
        list[i] = list[j];
        list[j] = tmp;
    }
    for (int t = 0; t < nd; t++) tb[t] = list[t];
    rebuild_inc();
    for (int t = 0; t < nd; t++) set_dart(t, rndint(GORD));
}

static long dup_count(void) {
    long c = 0;
    for (int t1 = 0; t1 < nd; t1++)
        for (int t2 = t1 + 1; t2 < nd; t2++)
            if (t1 / d == t2 / d && tb[t1] == tb[t2] && vg[t1] == vg[t2]) c++;
    return c;
}

/* Number of vertices within distance D of src. */
static int bfs_reach(int src) {
    int V2 = K * GORD;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < V2) {
                int a = v / GORD, x = v - a * GORD;
                for (int i = 0; i < d; i++) {
                    int t = a * d + i;
                    int u = V2 + tb[t] * GORD + fwd[t][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - V2;
                int b = w / GORD, y = w - b * GORD;
                for (int j = 0; j < d; j++) {
                    int t = inc[b][j];
                    int u = (t / d) * GORD + bwd[t][y];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left and right translations are automorphisms, transitive on each orbit,
 * so one BFS per orbit representative decides the diameter. */
static long cover_cost(void) {
    long V = 2L * K * GORD;
    long c = 0;
    for (int a = 0; a < K; a++) c += V - bfs_reach(a * GORD);
    for (int b = 0; b < K; b++) c += V - bfs_reach(K * GORD + b * GORD);
    return c + 1000L * dup_count();
}

static void save_state(void) {
    memcpy(stv, tb, sizeof(int) * (size_t)nd);
    memcpy(sgv, vg, sizeof(int) * (size_t)nd);
}

static int search_group(double until) {
    const int iters = 5000;
    while (now() < until) {
        random_init();
        long cost = cover_cost();
        if (cost == 0) { save_state(); return 1; }
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.2;
        for (int it = 0; it < iters; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            if (K > 1 && rnd01() < 0.4) {
                int t1 = rndint(nd), t2 = rndint(nd);
                if (tb[t1] == tb[t2]) continue;
                int tmp = tb[t1];
                tb[t1] = tb[t2];
                tb[t2] = tmp;
                rebuild_inc();
                long c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    tmp = tb[t1];
                    tb[t1] = tb[t2];
                    tb[t2] = tmp;
                    rebuild_inc();
                }
            } else {
                int t = rndint(nd), g = rndint(GORD);
                if (g == vg[t]) continue;
                int old = vg[t];
                set_dart(t, g);
                long c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else set_dart(t, old);
            }
            if (cost == 0) { save_state(); return 1; }
        }
    }
    return 0;
}

static void print_best(int gi, const int *btb, const int *bvg) {
    set_group(gN[gi], gm[gi], gk[gi], gr[gi]);
    for (int t = 0; t < nd; t++) tb[t] = btb[t];
    rebuild_inc();
    for (int t = 0; t < nd; t++) set_dart(t, bvg[t]);
    int N = GORD;
    printf("%d %d\n", 2 * K * N, K * N * d);
    for (int a = 0; a < K; a++)
        for (int x = 0; x < N; x++)
            for (int i = 0; i < d; i++) {
                int t = a * d + i;
                int u = K * N + tb[t] * N + fwd[t][x];
                printf("%d %d\n", a * N + x, u);
            }
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    K = atoi(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.95 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2 || K < 1 || K > MAXK) {
        printf("0 0\n");
        return 0;
    }
    nd = K * d;

    int hn = 0, hm = 0;
    if (scanf("%d %d", &hn, &hm) != 2) hm = 0;
    int G = hm / 2;
    for (int g = 0; g < G; g++) {
        int m1, k1, r1, N1;
        if (scanf("%d %d %d %d", &m1, &k1, &r1, &N1) != 4) break;
        if (NGR >= MAXG) break;
        if (m1 < 1 || k1 < 1 || N1 < 2 || N1 > MAXN || (long)m1 * k1 != N1) continue;
        gm[NGR] = m1;
        gk[NGR] = k1;
        gr[NGR] = r1;
        gN[NGR] = N1;
        NGR++;
    }

    static int bt[MAXND], bv[MAXND];
    int bestGi = -1, bestN = 0;

    /* Phase 1: binary search over the sorted group list, fixed share per probe. */
    int li = 0, hi = NGR - 1;
    while (li <= hi && now() < t_end) {
        int mid = (li + hi) / 2;
        double rem = t_end - now();
        double slice = rem * 0.3;
        if (slice < 0.5) slice = 0.5;
        if (slice > rem) slice = rem;
        int ok = 0;
        if (set_group(gN[mid], gm[mid], gk[mid], gr[mid])) ok = search_group(now() + slice);
        if (ok) {
            if (gN[mid] > bestN) {
                bestN = gN[mid];
                bestGi = mid;
                memcpy(bt, stv, sizeof(int) * (size_t)nd);
                memcpy(bv, sgv, sizeof(int) * (size_t)nd);
            }
            li = mid + 1;
        } else {
            hi = mid - 1;
        }
    }

    /* Phase 2: leftover time on the next orders above the best. */
    int fails = 0;
    int idx = (bestGi < 0) ? 0 : bestGi + 1;
    while (idx < NGR && now() < t_end && fails < 2) {
        if (gN[idx] <= bestN) { idx++; continue; }
        double rem = t_end - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        int ok = 0;
        if (set_group(gN[idx], gm[idx], gk[idx], gr[idx])) ok = search_group(now() + slice);
        if (ok) {
            bestN = gN[idx];
            bestGi = idx;
            memcpy(bt, stv, sizeof(int) * (size_t)nd);
            memcpy(bv, sgv, sizeof(int) * (size_t)nd);
            fails = 0;
        } else {
            fails++;
        }
        idx++;
    }

    if (bestGi < 0) {
        printf("0 0\n");
        return 0;
    }
    print_best(bestGi, bt, bv);
    return 0;
}
'''


def _is_prime(n):
    """Trial-division primality test."""
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def _prim_root(p):
    """A primitive root modulo the odd prime p."""
    fac = []
    x = p - 1
    f = 2
    while f * f <= x:
        if x % f == 0:
            fac.append(f)
            while x % f == 0:
                x //= f
        f += 1
    if x > 1:
        fac.append(x)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    return 1


def _divisors(n):
    """Sorted divisors of n."""
    ds = set()
    i = 1
    while i * i <= n:
        if n % i == 0:
            ds.add(i)
            ds.add(n // i)
        i += 1
    return sorted(ds)


def _group_for(N):
    """Return (m, k, r) with group Z_m x|_r Z_k of order N = m*k, preferring affine F_p x| C_k."""
    for k in _divisors(N):
        if k < 2:
            continue
        p = N // k
        if p >= 3 and (p - 1) % k == 0 and _is_prime(p):
            g = _prim_root(p)
            return p, k, pow(g, (p - 1) // k, p)
    if N % 2 == 0 and N // 2 >= 3:
        m = N // 2
        return m, 2, m - 1
    return N, 1, 1


def _pack_groups(lo, hi):
    """Group records for orders lo..hi, packed as lib graph text: G, then 2G pairs."""
    pairs = []
    for N in range(lo, hi + 1):
        m, k, r = _group_for(N)
        pairs.append((m, k))
        pairs.append((r, N))
    return len(pairs) // 2, pairs


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


def _run_orbit_search(d, D, seed, budget, lo, hi, K):
    """Run the C engine for K orbits and group orders in [lo, hi]; returns (n, edges)."""
    G, pairs = _pack_groups(lo, hi)
    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), K],
                     stdin_graph=(G, pairs), timeout=budget + 3.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.85 * time_limit - 3.0

    def left():
        return deadline - time.monotonic()

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
        if n > 0 and n > best[0] and lib.is_valid(n, e, d, D):
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

    if d >= 2 and D >= 3 and d <= 16:
        mb = lib.moore_bound(d, D)
        # Stage order: K = 1 first (reproduces the single-orbit record region),
        # then the multi-orbit lifts. Unused time flows to the later stages.
        stages = [(1, 0.35), (4, 0.25), (6, 0.20), (3, 0.12), (8, 0.08)]
        for i, (K, frac) in enumerate(stages):
            rem = left()
            if rem < 3.0:
                break
            fsum = sum(f for _, f in stages[i:])
            budget = rem * frac / fsum
            lo = max(3, best[0] // (2 * K) + 1)
            hi = min(mb // (2 * K), 4096)
            if lo > hi or budget < 3.0:
                continue
            try:
                consider(_run_orbit_search(d, D, seed + 17 * i, budget, lo, hi, K))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
