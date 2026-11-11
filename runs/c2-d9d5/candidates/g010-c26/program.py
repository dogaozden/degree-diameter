"""Metacyclic-group Haar lifts for the bipartite degree-diameter problem.

Change from the parent: the group family is different. The parent searched Haar graphs over
F_q x| H (field-based affine groups). This version searches metacyclic groups
G = Z_m x|_r Z_k, with r^k = 1 (mod m) and gcd(r, m) = 1. Those include cyclic groups
(r = 1, k = 1), direct products (r = 1), and genuinely non-abelian metacyclic groups.
For each order N = m*k in an ascending range, the C engine enumerates every valid (m, k, r),
shuffles them, and tries a few at random.

Construction: take a d-element set S in G and the bipartite Haar graph with L_g ~ R_{g*s}
for s in S. This graph is d-regular, bipartite and simple. Left translations act transitively
on each side, so the diameter check reduces to two BFS runs, from L_e and R_e.

Search: iterated annealing over S. Each round perturbs the incumbent (two elements replaced)
and anneals from a lower starting temperature.

Safety: every candidate is checked with lib.is_valid. If the search fails, the Python side
falls back to earlier constructions, and finally to K_{d,d}, which is valid for every D >= 2.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Metacyclic group Haar lift search.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * Group element (a, b) is coded a*k + b, with product (a, b)(c, e) = (a + r^b c, b + e).
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 32
#define MAXT 4096

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
static long gcdl(long a, long b) {
    while (b) {
        long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/* ------------------------------------------------------------ group Z_m x|_r Z_k */

static int GM, GK, GR, GN;
static int RP[MAXN];   /* RP[b] = r^b mod m for 0 <= b < k */

static void setup_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GR = r;
    GN = m * k;
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int na = (int)(((long)a + (long)RP[b] * c) % GM);
    int nb = b + e;
    if (nb >= GK) nb -= GK;
    return na * GK + nb;
}

static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int na = (int)((GM - (long)RP[nb] * a % GM) % GM);
    return na * GK + nb;
}

/* Enumerate all valid (m, k, r) with m*k = N, m >= 2, r in [1, m), gcd(r, m) = 1, r^k = 1. */
static int cm[MAXT], ck[MAXT], cr[MAXT];

static int enum_group(int N) {
    int cnt = 0;
    for (int k = 1; k <= N / 2; k++) {
        if (N % k) continue;
        int m = N / k;
        for (int r = 1; r < m && cnt < MAXT; r++) {
            if (gcdl(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cm[cnt] = m;
            ck[cnt] = k;
            cr[cnt] = r;
            cnt++;
        }
    }
    return cnt;
}

/* ------------------------------------------------------------ Haar graph state */

static int S[MAXD], Sinv[MAXD], bestS[MAXD];
static int fwd[MAXD][MAXN], bwd[MAXD][MAXN];
static int vis[2 * MAXN], que[2 * MAXN];
static int stamp_ = 0;

/* Vertices: L_g = g (0..N-1), R_h = N + h. L_g ~ R_{g s}, so R_h ~ L_{h s^-1}. */
static void set_s(int i, int x) {
    S[i] = x;
    Sinv[i] = ginv(x);
    for (int g = 0; g < GN; g++) {
        fwd[i][g] = gmul(g, x);
        bwd[i][g] = gmul(g, Sinv[i]);
    }
}

static int bfs_count(int src) {
    int N = GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int u = N + fwd[i][v];
                    if (vis[u] != stamp_) {
                        vis[u] = stamp_;
                        que[tail++] = u;
                    }
                }
            } else {
                int h = v - N;
                for (int i = 0; i < d; i++) {
                    int u = bwd[i][h];
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

/* Left translations are automorphisms and act transitively on each side,
 * so two BFS runs (from L_e and R_e) decide the diameter. */
static long cover_cost(void) {
    int V = 2 * GN;
    return (long)(V - bfs_count(0)) + (long)(V - bfs_count(GN));
}

static int in_S(int x, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == x) return 1;
    return 0;
}

/* Iterated annealing over S (size d) in the current group.
 * Round 1 starts from a random set. Later rounds start from the incumbent with two
 * elements replaced, at a lower starting temperature.
 * Returns 1 when cost 0 is reached (diameter <= D), 0 on timeout or failure. */
static int search_group(double until) {
    int N = GN;
    const int iters = 8000;
    int have = 0;
    long bestc = 0;
    int incS[MAXD];
    while (now() < until) {
        if (!have) {
            for (int i = 0; i < d; i++) {
                int x;
                do { x = rndint(N); } while (in_S(x, i));
                set_s(i, x);
            }
        } else {
            for (int i = 0; i < d; i++) set_s(i, incS[i]);
            for (int t = 0; t < 2; t++) {
                int i = rndint(d), x;
                do { x = rndint(N); } while (in_S(x, d));
                set_s(i, x);
            }
        }
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(d);
            int x;
            do { x = rndint(N); } while (in_S(x, d));
            int old = S[i];
            set_s(i, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_s(i, old);
            }
        }
        if (cost == 0) return 1;
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(incS, S, sizeof(int) * (size_t)d);
        }
    }
    return 0;
}

static void print_result(void) {
    int N = GN;
    printf("%d %d\n", 2 * N, N * d);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + fwd[i][g]);
}

/* ------------------------------------------------------------ main */

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
    if (hi > MAXN - 1) hi = MAXN - 1;
    if (lo < 2 * d) lo = 2 * d;

    int bestN = 0, bm = 0, bk = 0, br = 0;
    int bestS_loc[MAXD];

    /* Ascending over orders. For each order, shuffle its valid groups and try a few.
     * Each attempt gets about 10% of the remaining time (at least 0.8 s), so the
     * budget is spread across many orders instead of being spent on one. */
    for (int N = lo; N <= hi; N++) {
        if (N <= bestN) continue;
        double rem = t_end - now();
        if (rem < 0.3) break;
        int cnt = enum_group(N);
        if (cnt == 0) continue;
        for (int i = cnt - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tm = cm[i]; cm[i] = cm[j]; cm[j] = tm;
            int tk = ck[i]; ck[i] = ck[j]; ck[j] = tk;
            int tr = cr[i]; cr[i] = cr[j]; cr[j] = tr;
        }
        int tries = cnt < 2 ? cnt : 2;
        for (int t = 0; t < tries; t++) {
            rem = t_end - now();
            if (rem < 0.3) break;
            double slice = 0.1 * rem;
            if (slice < 0.8) slice = 0.8;
            if (slice > rem) slice = rem;
            setup_group(cm[t], ck[t], cr[t]);
            if (search_group(now() + slice)) {
                bestN = GN;
                bm = cm[t];
                bk = ck[t];
                br = cr[t];
                memcpy(bestS_loc, S, sizeof(int) * (size_t)d);
                break;
            }
        }
    }

    if (!bestN) {
        printf("0 0\n");
        return 0;
    }
    setup_group(bm, bk, br);
    for (int i = 0; i < d; i++) set_s(i, bestS_loc[i]);
    print_result();
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

    # Search: Haar graphs over metacyclic groups Z_m x|_r Z_k.
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
