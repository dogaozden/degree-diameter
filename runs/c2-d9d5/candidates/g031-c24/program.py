"""Base-lift search over semidirect groups for the bipartite degree-diameter problem.

Construction (new in this version): instead of a single-vertex-pair Haar graph, use a
d-regular bipartite base multigraph on B + B vertices, given as d permutations sigma_k of
{0..B-1} (dart (k, i) runs from left i to right sigma_k(i)). Each dart carries a voltage g
in G = Z_m x| Z_k. The lift has vertices (i, x) on the left and (j, y) on the right, with
(i, x) ~ (sigma_k(i), x*g_{k,i}). This is d-regular and bipartite. Left multiplication by G
is an automorphism that is transitive on each fibre, so the diameter check needs only 2B BFS
runs, one from (i, e) for each base vertex. The C engine anneals over permutations and
voltages jointly, restarting from the incumbent with a few random moves.

Fallbacks: PG(2, d-1) incidence graph, the Araujo-Lopez graph, W(q) for D = 4, and K_{d,d}.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Base-lift search over semidirect groups.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo, hi bound the total vertex count 2*B*|G|. Output "n m" then m edges, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXB 4
#define MAXV 16384
#define MAXCAND 300000
#define MAXK 8192

typedef struct { int b, m, k, r, N; uint32_t key; } Cand;

static int d, D, B;
static int gm, gk, gr, gG;
static int pw[MAXK];
static int TO[MAXD][MAXB], VO[MAXD][MAXB];
static int PRE[MAXD][MAXB], IVO[MAXD][MAXB];
static int BTO[MAXD][MAXB], BVO[MAXD][MAXB];
static int INC_TO[MAXD][MAXB], INC_VO[MAXD][MAXB];
static int BEST_TO[MAXD][MAXB], BEST_VO[MAXD][MAXB];
static int vis[MAXV], que[MAXV];
static int stampv = 0;
static Cand cand[MAXCAND];
static int nc = 0;
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

static long gcdl(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}
static long powmodl(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* ------------------------------------------------------------ group Z_m x| Z_k
 * Element (a, c) is coded a*k + c. Product: (a1,c1)(a2,c2) = (a1 + r^c1 a2, c1 + c2). */

static void set_group(int m, int k, int r) {
    gm = m; gk = k; gr = r; gG = m * k;
    pw[0] = 1 % m;
    for (int c = 1; c < k; c++) pw[c] = (int)((long long)pw[c - 1] * r % m);
}

static inline int gmul(int x, int y) {
    int a1 = x / gk, c1 = x - a1 * gk;
    int a2 = y / gk, c2 = y - a2 * gk;
    int a = (a1 + (int)(((long long)pw[c1] * a2) % gm)) % gm;
    int c = c1 + c2;
    if (c >= gk) c -= gk;
    return a * gk + c;
}

static int ginv(int x) {
    int a = x / gk, c = x - a * gk;
    int c2 = (gk - c) % gk;
    int t = (int)((long long)pw[c2] * a % gm);
    int a2 = (gm - t) % gm;
    return a2 * gk + c2;
}

/* ------------------------------------------------------------ lift state
 * Left vertex (i, x) = i*G + x; right vertex (j, y) = (B + j)*G + y.
 * Dart (k, i): left i ~ right TO[k][i] with voltage VO[k][i]. */

static void derive(void) {
    for (int k = 0; k < d; k++)
        for (int i = 0; i < B; i++) {
            PRE[k][TO[k][i]] = i;
            IVO[k][i] = ginv(VO[k][i]);
        }
}

/* Number of vertices within distance D of src. */
static int bfs_reach(int src) {
    int G = gG, b = B, bG = B * gG;
    stampv++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stampv;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < bG) {
                int i = v / G, x = v - i * G;
                for (int k = 0; k < d; k++) {
                    int w = (b + TO[k][i]) * G + gmul(x, VO[k][i]);
                    if (vis[w] != stampv) { vis[w] = stampv; que[tail++] = w; }
                }
            } else {
                int j = (v - bG) / G;
                int y = v - (b + j) * G;
                for (int k = 0; k < d; k++) {
                    int i = PRE[k][j];
                    int w = i * G + gmul(y, IVO[k][i]);
                    if (vis[w] != stampv) { vis[w] = stampv; que[tail++] = w; }
                }
            }
        }
    }
    return tail;
}

/* Cost 0 iff the lift is simple (no parallel darts with equal voltage) and has diameter <= D.
 * Left-multiplication is transitive on each fibre, so one BFS per base vertex suffices. */
static long cost_of(void) {
    derive();
    long c = 0;
    for (int i = 0; i < B; i++)
        for (int k = 0; k < d; k++)
            for (int l = k + 1; l < d; l++)
                if (TO[k][i] == TO[l][i] && VO[k][i] == VO[l][i]) c += 40;
    long V = 2L * B * gG;
    for (int i = 0; i < B; i++) c += V - bfs_reach(i * gG);
    for (int j = 0; j < B; j++) c += V - bfs_reach((B + j) * gG);
    return c;
}

static void random_state(void) {
    for (int k = 0; k < d; k++) {
        for (int i = 0; i < B; i++) TO[k][i] = i;
        for (int i = B - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = TO[k][i]; TO[k][i] = TO[k][j]; TO[k][j] = t;
        }
        for (int i = 0; i < B; i++) VO[k][i] = rndint(gG);
    }
}

/* Move: either change one voltage, or swap two targets within one permutation
 * (which keeps every base vertex degree equal to d). */
static void propose(void) {
    if (B == 1 || rnd01() < 0.5) {
        int k = rndint(d), i = rndint(B);
        VO[k][i] = rndint(gG);
    } else {
        int k = rndint(d);
        int i = rndint(B);
        int i2 = rndint(B - 1);
        if (i2 >= i) i2++;
        int t = TO[k][i]; TO[k][i] = TO[k][i2]; TO[k][i2] = t;
    }
}

/* Iterated annealing for the current group and base size B.
 * Returns 1 with TO/VO holding a cost-0 lift, 0 on timeout. */
static int anneal(double until) {
    int have = 0;
    long incc = 0;
    while (now() < until) {
        if (!have) {
            random_state();
        } else {
            memcpy(TO, INC_TO, sizeof TO);
            memcpy(VO, INC_VO, sizeof VO);
            for (int t = 0; t < 3; t++) propose();
        }
        long cur = cost_of();
        if (cur == 0) return 1;
        double Ts = 0.1 * (double)cur + 2.0, Te = 0.3;
        const int iters = 6000;
        for (int it = 0; it < iters; it++) {
            if ((it & 31) == 0 && now() > until) break;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            memcpy(BTO, TO, sizeof TO);
            memcpy(BVO, VO, sizeof VO);
            propose();
            long c2 = cost_of();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
                if (cur == 0) return 1;
            } else {
                memcpy(TO, BTO, sizeof TO);
                memcpy(VO, BVO, sizeof VO);
            }
        }
        if (!have || cur < incc) {
            have = 1;
            incc = cur;
            memcpy(INC_TO, TO, sizeof TO);
            memcpy(INC_VO, VO, sizeof VO);
        }
    }
    return 0;
}

static void add_cand(int b, long m, long k, long r) {
    if (nc >= MAXCAND) return;
    Cand c;
    c.b = b;
    c.m = (int)m;
    c.k = (int)k;
    c.r = (int)r;
    c.N = (int)(2L * b * m * k);
    c.key = (uint32_t)rnd();
    cand[nc++] = c;
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    if (x->N != y->N) return x->N < y->N ? -1 : 1;
    if (x->key != y->key) return x->key < y->key ? -1 : 1;
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
    long lo = atol(argv[5]), hi = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (hi > MAXV / 2) hi = MAXV / 2;
    if (lo < 4) lo = 4;
    if (hi < lo) {
        printf("0 0\n");
        return 0;
    }

    /* Candidates: base size b in {2..MAXB}, group Z_m x| Z_k of order n with 2*b*n in [lo, hi]. */
    for (int b = 2; b <= MAXB; b++) {
        long nlo = (lo + 2L * b - 1) / (2L * b);
        long nhi = hi / (2L * b);
        if (nlo < 2) nlo = 2;
        for (long n = nlo; n <= nhi; n++) {
            for (long k = 1; k <= n; k++) {
                if (n % k) continue;
                long m = n / k;
                if (k == 1) {
                    if (m >= 2) add_cand(b, m, 1, 1);        /* cyclic */
                } else if (m == 1) {
                    add_cand(b, 1, k, 0);                    /* Z_k */
                } else {
                    for (long r = 1; r < m; r++) {
                        if (gcdl(r, m) != 1) continue;
                        if (powmodl(r, k, m) != 1 % m) continue;
                        add_cand(b, m, k, r);
                    }
                }
            }
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Ascending order: successes move the bar up, so each attempt gets a bounded slice. */
    int bestN = 0, bestb = 0, bestm = 0, bestk = 0, bestr = 0;
    for (int ci = 0; ci < nc; ci++) {
        double rem = t_end - now();
        if (rem < 0.3) break;
        Cand c = cand[ci];
        if (c.N <= bestN) continue;
        double slice = 0.15 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > 4.0) slice = 4.0;
        if (slice > rem) slice = rem;
        set_group(c.m, c.k, c.r);
        B = c.b;
        if (anneal(now() + slice)) {
            bestN = c.N;
            bestb = c.b;
            bestm = c.m;
            bestk = c.k;
            bestr = c.r;
            memcpy(BEST_TO, TO, sizeof TO);
            memcpy(BEST_VO, VO, sizeof VO);
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    set_group(bestm, bestk, bestr);
    B = bestb;
    int n = 2 * B * gG;
    int m = d * B * gG;
    printf("%d %d\n", n, m);
    for (int i = 0; i < B; i++)
        for (int x = 0; x < gG; x++)
            for (int k = 0; k < d; k++)
                printf("%d %d\n", i * gG + x,
                       (B + BEST_TO[k][i]) * gG + gmul(x, BEST_VO[k][i]));
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

    # Search: base-lift graphs over Z_m x| Z_k with 2 to 4 base vertices per side.
    if d >= 3 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
        lo = max(best[0] + 1, mb // 5)
        hi = mb // 2
        if budget > 3.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
