import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (safe fallbacks, always considered first).
# ----------------------------------------------------------------------------

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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bipartite d-regular graphs.
#
# Start: Haar graph of Z_m with d random shifts (d-regular, bipartite).
# Move: double edge swap (a1-b1, a2-b2) -> (a1-b2, a2-b1). This keeps every
# degree and the bipartition, and is NOT restricted to any group structure.
# Cost: number of unordered vertex pairs at distance > D, computed exactly
# with bitset ball expansion. Cost 0 means a valid graph.
# The engine tries m upward from m_start, keeps the largest success, and
# steps m down when an attempt at a new size fails before any success.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXW 64
#define MAXDEG 32

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int d = 3, DD = 3, M = 0, N = 0, W = 0;
static int adj[MAXN][MAXDEG];
static int bestadj[MAXN][MAXDEG];
static int best_m = 0;
static uint64_t bufA[MAXN * MAXW], bufB[MAXN * MAXW];
static double deadline = 0.0;

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > DD. */
static long long cost(void) {
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++)
        cur[(size_t)v * W + (size_t)(v / 64)] |= 1ULL << (v % 64);
    for (int r = 0; r < DD; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int t = 0; t < d; t++) {
                const uint64_t *u = cur + (size_t)adj[v][t] * W;
                for (int w = 0; w < W; w++) dst[w] |= u[w];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *s = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(s[w]);
        bad += N - c;
    }
    return bad / 2;
}

/* Haar graph of Z_m with d distinct random shifts. A-side = 0..M-1, B-side = M..N-1. */
static void setup_haar(int m) {
    M = m;
    N = 2 * m;
    W = (N + 63) / 64;
    int sh[MAXDEG];
    int k = 0;
    while (k < d) {
        int s = rint_(M), ok = 1;
        for (int t = 0; t < k; t++)
            if (sh[t] == s) ok = 0;
        if (ok) sh[k++] = s;
    }
    for (int i = 0; i < M; i++)
        for (int t = 0; t < d; t++)
            adj[i][t] = M + (i + sh[t]) % M;
    for (int j = 0; j < M; j++)
        for (int t = 0; t < d; t++)
            adj[M + j][t] = ((j - sh[t]) % M + M) % M;
}

static int has_edge(int a, int b) {
    for (int t = 0; t < d; t++)
        if (adj[a][t] == b) return 1;
    return 0;
}

static void set_nb(int v, int oldu, int newu) {
    for (int t = 0; t < d; t++)
        if (adj[v][t] == oldu) {
            adj[v][t] = newu;
            return;
        }
}

/* Double swap: a1-b1 and a2-b2 become a1-b2 and a2-b1 (a1,a2 in A). */
static void do_swap(int a1, int x, int a2, int y, int b1, int b2) {
    adj[a1][x] = b2;
    adj[a2][y] = b1;
    set_nb(b1, a1, a2);
    set_nb(b2, a2, a1);
}

/* Simulated annealing until cost 0 or time `until`. Returns 1 on success. */
static int anneal(double until) {
    double ts = now_s();
    double span = until - ts;
    if (span <= 0) span = 1e-3;
    long long cur = cost();
    const double T0 = 1.5, T1 = 0.05;
    while (cur > 0) {
        double now = now_s();
        if (now >= until) break;
        double fr = (now - ts) / span;
        double T = T0 * pow(T1 / T0, fr);
        int a1 = rint_(M), a2 = rint_(M);
        if (a1 == a2) continue;
        int x = rint_(d), y = rint_(d);
        int b1 = adj[a1][x], b2 = adj[a2][y];
        if (b1 == b2 || has_edge(a1, b2) || has_edge(a2, b1)) continue;
        do_swap(a1, x, a2, y, b1, b2);
        long long nc = cost();
        long long delta = nc - cur;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            do_swap(a1, x, a2, y, b2, b1);
        }
    }
    return cur == 0;
}

int main(int argc, char **argv) {
    d = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int m = argc > 5 ? atoi(argv[5]) : 2 * d;

    if (d < 1 || d > MAXDEG || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    deadline = now_s() + tl;
    if (m < d) m = d;
    if (m > MAXN / 2) m = MAXN / 2;

    while (now_s() < deadline) {
        double rem = deadline - now_s();
        double slice = rem * 0.35;
        if (slice < 1.5) slice = rem;
        setup_haar(m);
        int ok = anneal(now_s() + slice);
        if (ok) {
            memcpy(bestadj, adj, sizeof(adj));
            best_m = m;
            m++;
            if (m > MAXN / 2) break;
        } else {
            if (best_m > 0) break;
            m -= (m / 100 > 1) ? m / 100 : 1;
            if (m < d) break;
        }
    }

    if (best_m == 0) {
        printf("0 0\n");
        return 0;
    }
    int n = 2 * best_m;
    long cnt = (long)best_m * d;
    printf("%d %ld\n", n, cnt);
    for (int i = 0; i < best_m; i++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", i, bestadj[i][t]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue.
# ----------------------------------------------------------------------------

def _search(d, D, seed, budget, m_start):
    """One C annealing run. Returns (n, edges) if a valid graph was produced, else None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", m_start],
                        timeout=budget + 4.0)
        n, e = lib.parse_graph_text(out)
        if n > 0 and lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        pass
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.88 * time_limit, time_limit - 5.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions first.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bold change: unstructured annealing over d-regular bipartite graphs,
    # started near the Moore-bound fraction that the record suggests.
    # The C side steps m down if the target size is not reached.
    if d >= 3 and D >= 3:
        remaining = deadline - time.monotonic() - 1.0
        if remaining >= 3.0:
            moore = lib.moore_bound(d, D)
            target_m = max(d, int(0.365 * moore) // 2 + 1)
            target_m = min(target_m, 2000)
            res = _search(d, D, seed, remaining, target_m)
            if res is not None:
                consider(*res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
