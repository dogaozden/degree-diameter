"""Multi-orbit metacyclic voltage lifts for the bipartite degree-diameter problem.

This version replaces the affine-group Haar search with a different family. The base
graph has B left and B right vertices (B in 1..4). Left base vertex u has d darts, and
dart (u, t) goes to right base vertex (u + t) mod B. Each dart carries a voltage s in
G = Z_m x|_r Z_k, a metacyclic group of order N = m*k. The lift has 2*B*N vertices:
L(u, g) ~ R(v, g*s) for each dart (u, t) with target v. The lift is d-regular and
bipartite, and left translation is an automorphism. So diameter <= D reduces to 2B BFS
runs, one from each base vertex's identity element. The C engine anneals the voltages
to minimise the uncovered (vertex, distance) pairs. It tries candidates in ascending
order of order, starting above the current best, and makes repeated passes with fresh
random starts.

Risk: this family is different from the parent's, so if it fails to beat the current
best order, the program falls back to the Python constructions and K_{d,d}. Those are
valid but much smaller, so this is a high-risk replacement for the d=9, D=5 target.
Every returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit metacyclic voltage lift search.
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

#define MAXN 4096
#define MAXB 4
#define MAXD 32
#define MAXV (2 * MAXB * MAXN)
#define MAXCAND 300000
#define KMAX 12

typedef struct { int m, k, r, b, N, T; unsigned key; } Cand;

static int d, D;
static int B, N, M_, K_;
static int POW[MAXN];
static int TV[MAXB * MAXD];
static int INE[MAXB * MAXD];
static int SV[MAXB * MAXD], SI[MAXB * MAXD];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;
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

/* ------------------------------------------------------------ group Z_m x| Z_k */

/* Element (a, i) is coded as a*K_ + i. Product: (a, i)(c, j) = (a + r^i c, i + j). */
static inline int gmul(int x, int y) {
    int a = x / K_, i = x % K_, c = y / K_, j = y % K_;
    int na = (a + POW[i] * c) % M_;
    int nj = i + j;
    if (nj >= K_) nj -= K_;
    return na * K_ + nj;
}

/* Inverse of (a, i) is (-r^(-i) a, -i). Since r^K_ = 1, r^(-i) = r^ni with ni = K_ - i. */
static inline int ginv(int x) {
    int a = x / K_, i = x % K_;
    int ni = (K_ - i) % K_;
    int na = (M_ - (int)((long)POW[ni] * a % M_)) % M_;
    return na * K_ + ni;
}

/* ------------------------------------------------------------ lifted graph state */

/* Vertices: L(u, g) = u*N + g, R(v, h) = B*N + v*N + h.
 * Dart e = u*d + t goes from base left u to base right (u + t) mod B, voltage SV[e].
 * Edge L(u, g) ~ R(TV[e], g*SV[e]). Each right base vertex v has exactly d in-darts. */

static void setup(const Cand *c) {
    B = c->b;
    N = c->N;
    M_ = c->m;
    K_ = c->k;
    POW[0] = 1 % M_;
    for (int i = 1; i < K_; i++) POW[i] = (int)((long)POW[i - 1] * c->r % M_);
    for (int u = 0; u < B; u++)
        for (int t = 0; t < d; t++) TV[u * d + t] = (u + t) % B;
    int cnt[MAXB] = {0};
    for (int u = 0; u < B; u++)
        for (int t = 0; t < d; t++) {
            int v = (u + t) % B;
            INE[v * d + cnt[v]++] = u * d + t;
        }
    for (int e = 0; e < B * d; e++) { SV[e] = -1; SI[e] = -1; }
}

/* Number of vertices within distance D of src. */
static int reach(int src) {
    stamp_++;
    int BN = B * N;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int x = que[head++];
            if (x < BN) {
                int u = x / N, g = x % N;
                for (int t = 0; t < d; t++) {
                    int e = u * d + t;
                    int y = BN + TV[e] * N + gmul(g, SV[e]);
                    if (vis[y] != stamp_) { vis[y] = stamp_; que[tail++] = y; }
                }
            } else {
                int z = x - BN;
                int v = z / N, h = z % N;
                for (int j = 0; j < d; j++) {
                    int e = INE[v * d + j];
                    int w = (e / d) * N + gmul(h, SI[e]);
                    if (vis[w] != stamp_) { vis[w] = stamp_; que[tail++] = w; }
                }
            }
        }
    }
    return tail;
}

/* Vertex-transitivity on each base orbit: BFS from one identity per base vertex. */
static long cover_cost(void) {
    int V = 2 * B * N;
    long c = 0;
    for (int u = 0; u < B; u++) c += V - reach(u * N);
    for (int v = 0; v < B; v++) c += V - reach(B * N + v * N);
    return c;
}

/* Voltage x on dart e must differ from the voltages of other darts with the same target. */
static int dup_ok(int e, int x) {
    int u = e / d, t = e % d;
    int tg = (u + t) % B;
    for (int t2 = 0; t2 < d; t2++) {
        if (t2 == t) continue;
        if ((u + t2) % B == tg && SV[u * d + t2] == x) return 0;
    }
    return 1;
}

static int init_random(void) {
    for (int e = 0; e < B * d; e++) {
        int tries = 0, x;
        do {
            x = rndint(N);
            tries++;
        } while (!dup_ok(e, x) && tries < 100000);
        if (tries >= 100000) return 0;
        SV[e] = x;
        SI[e] = ginv(x);
    }
    return 1;
}

/* Simulated annealing over the voltages. Returns 1 when cost 0 is reached, 0 on timeout. */
static int search_cand(double until) {
    while (now() < until) {
        if (!init_random()) return 0;
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.2;
        const int iters = 3000;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 7) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int e = rndint(B * d);
            int x, tries = 0;
            do {
                x = rndint(N);
                tries++;
            } while ((x == SV[e] || !dup_ok(e, x)) && tries < 200);
            if (tries >= 200) continue;
            int old = SV[e], oldi = SI[e];
            SV[e] = x;
            SI[e] = ginv(x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                SV[e] = old;
                SI[e] = oldi;
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ candidates */

static Cand cand[MAXCAND];
static int nc = 0;

static void add_cand(int m, int k, int r, int b, int Nn) {
    if (nc >= MAXCAND) return;
    Cand c = {m, k, r, b, Nn, 2 * b * Nn, (unsigned)(rnd() & 0xffffffffu)};
    cand[nc++] = c;
}

static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long a, long e, long m) {
    long r = 1 % m;
    a %= m;
    while (e) {
        if (e & 1) r = r * a % m;
        a = a * a % m;
        e >>= 1;
    }
    return r;
}

static int cmp_cand(const void *pa, const void *pb) {
    const Cand *a = pa, *b = pb;
    if (a->T != b->T) return a->T < b->T ? -1 : 1;
    if (a->key != b->key) return a->key < b->key ? -1 : 1;
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
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    if (hi > 2 * MAXB * MAXN) hi = 2 * MAXB * MAXN;
    if (lo < 4 * d) lo = 4 * d;
    if (lo > hi) {
        printf("0 0\n");
        return 0;
    }

    /* Enumerate candidates: base size b, group order N, group Z_m x| Z_k with k <= KMAX. */
    for (int b = 1; b <= MAXB; b++) {
        long Nlo = (lo + 2L * b - 1) / (2L * b);
        long Nhi = hi / (2L * b);
        if (Nlo < 2L * d) Nlo = 2L * d;
        if (Nhi > MAXN) Nhi = MAXN;
        for (long Nn = Nlo; Nn <= Nhi; Nn++) {
            for (int k = 1; k <= KMAX && k <= Nn; k++) {
                if (Nn % k) continue;
                int m = (int)(Nn / k);
                if (m < 2) continue;
                if (k == 1) {
                    add_cand(m, 1, 1, b, (int)Nn);
                    continue;
                }
                for (int r = 1; r < m; r++) {
                    if (gcdi(r, m) != 1) continue;
                    if (powmod(r, k, m) != 1 % m) continue;
                    add_cand(m, k, r, b, (int)Nn);
                }
            }
        }
    }
    if (nc == 0) {
        printf("0 0\n");
        return 0;
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Ascending passes: each attempt gets 10% of the remaining time, clamped to [0.6, 5] s.
     * Candidates that failed earlier are retried with fresh random starts on later passes. */
    int bestT = 0, bestc = -1;
    int bestSV[MAXB * MAXD];
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            if (cand[ci].T <= bestT) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = 0.1 * rem;
            if (slice < 0.6) slice = 0.6;
            if (slice > 5.0) slice = 5.0;
            if (slice > rem) slice = rem;
            setup(&cand[ci]);
            if (search_cand(now() + slice)) {
                bestT = cand[ci].T;
                bestc = ci;
                memcpy(bestSV, SV, sizeof(SV));
            }
        }
        if (!tried || t_end - now() < 0.3) break;
    }

    if (bestc < 0) {
        printf("0 0\n");
        return 0;
    }
    setup(&cand[bestc]);
    memcpy(SV, bestSV, sizeof(SV));
    for (int e = 0; e < B * d; e++) SI[e] = ginv(SV[e]);

    printf("%d %d\n", 2 * B * N, B * N * d);
    for (int u = 0; u < B; u++)
        for (int g = 0; g < N; g++)
            for (int t = 0; t < d; t++) {
                int e = u * d + t;
                int x = u * N + g;
                int y = B * N + TV[e] * N + gmul(g, SV[e]);
                printf("%d %d\n", x, y);
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


def _search(d, D, seed, budget, lo, hi):
    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                     stdin_graph=None, timeout=budget + 8.0)
    return lib.parse_graph_text(text)


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

    # Search: multi-orbit lifts over metacyclic groups, starting above the current best.
    if d >= 3 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, mb // 4)
        hi = min(mb, int(1.6 * lo) + 2 * d, 16000)
        if budget > 3.0 and lo <= hi:
            try:
                consider(_search(d, D, seed, budget, lo, hi))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
