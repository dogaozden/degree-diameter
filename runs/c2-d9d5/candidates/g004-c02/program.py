"""Metacyclic voltage-lift search for the bipartite degree-diameter problem.

Idea: a new construction family, replacing the parent's Haar graphs on F_q x| H.
A base graph has K left and K right vertices (K = 1..4). Each left base vertex has
d darts, and the dart multiset is balanced so every right base vertex also has d
darts. Each dart carries a voltage in a group G = Z_m x|_r Z_s, with
r^s = 1 mod m and gcd(r, m) = 1. The lift has 2KN vertices, where N = |G|. Left
vertex (u, x) joins right vertex (v, x*g) for every dart u -> v with voltage g.

G acts by left translation on each fibre, so diameter <= D reduces to BFS from the
2K base roots (u, e). Simulated annealing moves voltages and swaps dart targets,
and penalises duplicate darts. Candidates are (K, m, s, r) with vertex count in a
window, tried in ascending order, and the largest valid lift found is returned.

Python keeps the projective-plane, Araujo-Lopez and W(q) baselines and the K_{d,d}
fallback. Every returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Metacyclic voltage-lift search.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo, hi bound the vertex count 2*K*|G| (strictly above lo, at most hi).
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXK 4
#define MAXJ (MAXK * MAXD)
#define MAXN 1400
#define MAXV (2 * MAXK * MAXN)
#define MAXCAND 200000

typedef struct { int K, m, s, r, N, V; unsigned key; } Cand;

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

/* ------------------------------------------------------------ group Z_GM x|_r Z_GS */

static int GM, GS, GN;
static int PW[MAXN];

static void setup_group(int m, int s, int r) {
    GM = m;
    GS = s;
    GN = m * s;
    PW[0] = 1 % m;
    for (int b = 1; b < s; b++) PW[b] = (int)((long long)PW[b - 1] * r % m);
}

/* (a, b)(c, e) = (a + r^b c, b + e); element code a*GS + b. */
static inline int gmul(int x, int y) {
    int a = x / GS, b = x % GS, c = y / GS, e = y % GS;
    int na = (a + PW[b] * c) % GM;
    int nb = (b + e) % GS;
    return na * GS + nb;
}

/* Inverse of (a, b) is (-r^(-b) a, -b). */
static int ginv(int x) {
    int a = x / GS, b = x % GS;
    int nb = (GS - b) % GS;
    int na = (GM - (PW[nb] * a) % GM) % GM;
    return na * GS + nb;
}

/* ------------------------------------------------------------ lift state */

static int K;                       /* base vertices per side */
static int tgt[MAXJ], volt[MAXJ];   /* dart j: left block j/d, right target tgt[j], voltage volt[j] */
static int fwd[MAXJ][MAXN], bwd[MAXJ][MAXN];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;
static int inl[MAXK][MAXD];         /* darts entering right base vertex v */
static int incnt[MAXK];

static void set_volt(int j, int g) {
    volt[j] = g;
    int gi = ginv(g);
    for (int x = 0; x < GN; x++) {
        fwd[j][x] = gmul(x, g);
        bwd[j][x] = gmul(x, gi);
    }
}

/* BFS from a vertex id; returns the number of vertices within distance D. */
static int bfs(int src) {
    int N = GN, KN = K * N;
    if (stamp_ == 0x7fffffff) {
        memset(vis, 0, sizeof(vis));
        stamp_ = 0;
    }
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < KN) {
                int u = v / N, x = v % N;
                for (int t = 0; t < d; t++) {
                    int j = u * d + t;
                    int w = KN + tgt[j] * N + fwd[j][x];
                    if (vis[w] != stamp_) { vis[w] = stamp_; que[tail++] = w; }
                }
            } else {
                int rr = v - KN, vv = rr / N, y = rr % N;
                for (int c = 0; c < incnt[vv]; c++) {
                    int j = inl[vv][c];
                    int w = (j / d) * N + bwd[j][y];
                    if (vis[w] != stamp_) { vis[w] = stamp_; que[tail++] = w; }
                }
            }
        }
    }
    return tail;
}

/* Cost = unreached (root, vertex) pairs over the 2K base roots, plus a penalty for
 * duplicate darts (same left block, same target, same voltage). Cost 0 means a
 * valid simple graph of diameter <= D. */
static long cost_eval(void) {
    int N = GN, J = K * d, KN = K * N, V = 2 * KN;
    long dup = 0;
    for (int u = 0; u < K; u++)
        for (int t1 = 0; t1 < d; t1++)
            for (int t2 = t1 + 1; t2 < d; t2++) {
                int j1 = u * d + t1, j2 = u * d + t2;
                if (tgt[j1] == tgt[j2] && volt[j1] == volt[j2]) dup++;
            }
    for (int v = 0; v < K; v++) incnt[v] = 0;
    for (int j = 0; j < J; j++) {
        int v = tgt[j];
        inl[v][incnt[v]++] = j;
    }
    long cost = 0;
    for (int root = 0; root < 2 * K; root++)
        cost += (long)(V - bfs(root * N));
    return cost + dup * (long)V;
}

/* Balanced random start: every right base vertex receives exactly d darts. */
static void init_cfg(void) {
    int J = K * d, tmp[MAXJ], idx = 0;
    for (int v = 0; v < K; v++)
        for (int t = 0; t < d; t++) tmp[idx++] = v;
    for (int i = J - 1; i > 0; i--) {
        int k = rndint(i + 1);
        int t = tmp[i]; tmp[i] = tmp[k]; tmp[k] = t;
    }
    for (int j = 0; j < J; j++) {
        tgt[j] = tmp[j];
        set_volt(j, rndint(GN));
    }
}

/* Simulated annealing over voltages and dart-target swaps for the current K and group.
 * Returns 1 when cost 0 is reached (state left in tgt/volt), 0 on timeout. */
static int search_cfg(double until) {
    const int iters = 4000;
    int J = K * d;
    while (now() < until) {
        init_cfg();
        long cost = cost_eval();
        if (cost == 0) return 1;
        double Ts = 0.05 * (double)cost + 2.0, Te = 0.2;
        for (int it = 0; it < iters; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int j = rndint(J);
            if (rnd() & 1) {
                int old = volt[j];
                int ng = rndint(GN);
                if (ng == old) continue;
                set_volt(j, ng);
                long c2 = cost_eval();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    set_volt(j, old);
                }
            } else {
                int j2 = rndint(J);
                if (tgt[j] == tgt[j2]) continue;
                int t = tgt[j]; tgt[j] = tgt[j2]; tgt[j2] = t;
                long c2 = cost_eval();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    t = tgt[j]; tgt[j] = tgt[j2]; tgt[j2] = t;
                }
            }
            if (cost == 0) return 1;
        }
    }
    return 0;
}

/* ------------------------------------------------------------ candidates */

static Cand cand[MAXCAND];

static int build_candidates(long lo, long hi) {
    int nc = 0;
    for (int KK = 1; KK <= MAXK; KK++) {
        for (long N = 1; N <= MAXN; N++) {
            long V = 2L * KK * N;
            if (V <= lo || V > hi) continue;
            for (int s = 1; s <= N; s++) {
                if (N % s) continue;
                int m = (int)(N / s);
                for (int r = 0; r < m; r++) {
                    if (gcd_i(r, m) != 1) continue;
                    if (powmod(r, s, m) != 1 % m) continue;
                    if (nc >= MAXCAND) return nc;
                    Cand c;
                    c.K = KK;
                    c.m = m;
                    c.s = s;
                    c.r = r;
                    c.N = (int)N;
                    c.V = (int)V;
                    c.key = (unsigned)rnd();
                    cand[nc++] = c;
                }
            }
        }
    }
    return nc;
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
    if (x->key != y->key) return x->key < y->key ? -1 : 1;
    return 0;
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
    long lo = atol(argv[5]), hi = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.85 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (hi > MAXV) hi = MAXV;
    if (lo < 2) lo = 2;
    if (hi <= lo) {
        printf("0 0\n");
        return 0;
    }

    int nc = build_candidates(lo, hi);
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    long bestV = lo;
    int have = 0;
    Cand bestc;
    static int bestTgt[MAXJ], bestVolt[MAXJ];
    for (int ci = 0; ci < nc; ci++) {
        if (now() > t_end) break;
        Cand c = cand[ci];
        if (c.V <= bestV) continue;
        double rem = t_end - now();
        int left = nc - ci;
        double slice = rem / left * 2.0;
        if (slice < 0.3) slice = 0.3;
        if (slice > rem) slice = rem;
        K = c.K;
        setup_group(c.m, c.s, c.r);
        if (search_cfg(now() + slice)) {
            bestV = c.V;
            bestc = c;
            have = 1;
            int J = K * d;
            memcpy(bestTgt, tgt, sizeof(int) * (size_t)J);
            memcpy(bestVolt, volt, sizeof(int) * (size_t)J);
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }

    /* Rebuild the best lift and verify it before printing. */
    K = bestc.K;
    setup_group(bestc.m, bestc.s, bestc.r);
    int J = K * d;
    for (int j = 0; j < J; j++) {
        tgt[j] = bestTgt[j];
        set_volt(j, bestVolt[j]);
    }
    if (cost_eval() != 0) {
        printf("0 0\n");
        return 0;
    }
    int N = GN, KN = K * N;
    printf("%d %d\n", 2 * KN, J * N);
    for (int j = 0; j < J; j++) {
        int u = j / d;
        for (int x = 0; x < N; x++)
            printf("%d %d\n", u * N + x, KN + tgt[j] * N + fwd[j][x]);
    }
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

    # New search: metacyclic voltage lifts with a K-vertex base (K = 1..4).
    if d >= 3 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 4.0
        lo = max(best[0], int(0.12 * mb))
        hi = min(mb, int(0.4 * mb) + 1)
        if budget > 3.0 and lo < hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
