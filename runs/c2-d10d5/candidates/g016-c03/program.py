import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New engine: random bipartite d-regular graphs, repaired by double-edge
# switches. Each switch keeps the graph simple, bipartite and d-regular. The
# cost is the number of ordered vertex pairs at distance > D, computed with
# bitset BFS. Simulated annealing drives the cost to zero. The order N is
# searched by bisection: grow while annealing succeeds, shrink after failures.
# Every returned graph is checked by lib.is_valid in Python.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs;
static uint64_t rnd64(void) {
    uint64_t x = rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rs = x;
    return x * 2685821657736338717ULL;
}
static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}
static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int DEG, DIAM;
static int M, N, W;          /* N = 2M vertices, A = 0..M-1, B = M..2M-1 */
static int *nbr;             /* nbr[v*DEG + s] = global id of s-th neighbour */
static int *bestnbr;
static int *perm;
static uint64_t *bufA, *bufB;
static double g_end;
static int best_N;

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of ordered pairs (v, u) with dist(v, u) > DIAM. */
static int64_t eval_cost(void) {
    uint64_t *cur = bufA, *nxt = bufB;
    size_t total = (size_t)N * (size_t)W;
    memset(cur, 0, sizeof(uint64_t) * total);
    for (int v = 0; v < N; v++)
        cur[(size_t)v * W + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(uint64_t) * (size_t)W);
            for (int s = 0; s < DEG; s++) {
                const uint64_t *c2 = cur + (size_t)nbr[v * DEG + s] * W;
                for (int w = 0; w < W; w++) o[w] |= c2[w];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    int64_t bad = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *c = cur + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += popc64(c[w]);
        bad += N - cnt;
    }
    return bad;
}

static int has_edge(int a, int bg) {
    for (int s = 0; s < DEG; s++)
        if (nbr[a * DEG + s] == bg) return 1;
    return 0;
}

/* Does A vertex i already have B index bidx among its slots < j? */
static int slot_conflict(int i, int bidx, int j) {
    int bg = M + bidx;
    for (int s = 0; s < j; s++)
        if (nbr[i * DEG + s] == bg) return 1;
    return 0;
}

/* Random simple bipartite DEG-regular graph: one random perfect matching per slot. */
static int gen_random(void) {
    int restarts = 0;
    for (int j = 0; j < DEG; j++) {
        int ok_slot = 0;
        while (!ok_slot) {
            if (++restarts > 2000) return 0;
            for (int i = 0; i < M; i++) perm[i] = i;
            for (int i = M - 1; i > 0; i--) {
                int k = rndint(i + 1);
                int t = perm[i];
                perm[i] = perm[k];
                perm[k] = t;
            }
            ok_slot = 1;
            for (int i = 0; i < M && ok_slot; i++) {
                int fixed = 0;
                for (int t = 0; t < 100; t++) {
                    if (!slot_conflict(i, perm[i], j)) {
                        fixed = 1;
                        break;
                    }
                    int k = rndint(M);
                    if (k == i) continue;
                    if (!slot_conflict(i, perm[k], j) && !slot_conflict(k, perm[i], j)) {
                        int tp = perm[i];
                        perm[i] = perm[k];
                        perm[k] = tp;
                        fixed = 1;
                        break;
                    }
                }
                if (!fixed) ok_slot = 0;
            }
        }
        for (int i = 0; i < M; i++) {
            nbr[i * DEG + j] = M + perm[i];
            nbr[(M + perm[i]) * DEG + j] = i;
        }
    }
    return 1;
}

static void replace_in(int b, int oldA, int newA) {
    for (int s = 0; s < DEG; s++) {
        if (nbr[b * DEG + s] == oldA) {
            nbr[b * DEG + s] = newA;
            return;
        }
    }
}

/* Anneal for a fixed order n_try until cost 0 or the slice ends. */
static int attempt(int n_try, double slice_end) {
    M = n_try / 2;
    N = 2 * M;
    W = (N + 63) / 64;
    if (!gen_random()) return 0;

    int64_t cost = eval_cost();
    double t0 = now_s();
    double span = slice_end - t0;
    if (span < 0.05) span = 0.05;

    while (cost > 0) {
        double tn = now_s();
        if (tn > slice_end || tn > g_end) break;
        double frac = (tn - t0) / span;
        if (frac > 1.0) frac = 1.0;
        double T = 2.0 * (1.0 - frac) + 0.05;

        int a1 = rndint(M), j = rndint(DEG);
        int a2 = rndint(M), k = rndint(DEG);
        if (a1 == a2) continue;
        int b1 = nbr[a1 * DEG + j];
        int b2 = nbr[a2 * DEG + k];
        if (b1 == b2) continue;
        if (has_edge(a1, b2) || has_edge(a2, b1)) continue;

        nbr[a1 * DEG + j] = b2;
        nbr[a2 * DEG + k] = b1;
        replace_in(b1, a1, a2);
        replace_in(b2, a2, a1);

        int64_t c2 = eval_cost();
        int64_t delta = c2 - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cost = c2;
        } else {
            nbr[a1 * DEG + j] = b1;
            nbr[a2 * DEG + k] = b2;
            replace_in(b1, a2, a1);
            replace_in(b2, a1, a2);
        }
    }

    if (cost == 0) {
        memcpy(bestnbr, nbr, sizeof(int) * (size_t)N * DEG);
        best_N = N;
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 7) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    int start_n = atoi(argv[3]);
    int maxn = atoi(argv[4]);
    unsigned long long seed = strtoull(argv[5], NULL, 10);
    double TL = atof(argv[6]);

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    g_end = now_s() + TL - 0.5;

    if (DEG < 3 || DIAM < 3 || maxn < 2 * DEG + 2) {
        printf("0 0\n");
        return 0;
    }
    maxn -= maxn % 2;
    int Wmax = (maxn + 63) / 64;
    nbr = malloc(sizeof(int) * (size_t)maxn * DEG);
    bestnbr = malloc(sizeof(int) * (size_t)maxn * DEG);
    perm = malloc(sizeof(int) * (size_t)(maxn / 2 + 1));
    bufA = malloc(sizeof(uint64_t) * (size_t)maxn * Wmax);
    bufB = malloc(sizeof(uint64_t) * (size_t)maxn * Wmax);
    if (!nbr || !bestnbr || !perm || !bufA || !bufB) {
        printf("0 0\n");
        return 0;
    }

    int found = 0;
    int lo = 0, hi = 0;
    int N_try = start_n - start_n % 2;
    if (N_try < 2 * DEG + 2) N_try = 2 * DEG + 2;
    if (N_try > maxn) N_try = maxn;

    while (1) {
        double rem = g_end - now_s();
        if (rem < 0.3) break;
        double slice = rem * 0.35;
        if (slice < 1.0) slice = rem;
        double slice_end = now_s() + slice;

        int ok = attempt(N_try, slice_end);
        if (ok) {
            found = 1;
            lo = N_try;
            if (lo >= maxn) break;
            if (hi == 0) {
                int step = N_try / 30;
                if (step < 2) step = 2;
                N_try = N_try + step;
            } else {
                if (hi - lo <= 2) break;
                N_try = (lo + hi) / 2;
            }
        } else {
            if (now_s() >= g_end) break;
            hi = N_try;
            if (lo == 0) {
                N_try = (int)(N_try * 0.93);
            } else {
                if (hi - lo <= 2) break;
                N_try = (lo + hi) / 2;
            }
        }
        if (N_try > maxn) N_try = maxn;
        N_try -= N_try % 2;
        if (N_try < 2 * DEG + 2) break;
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    int halfA = best_N / 2;
    long long m = (long long)halfA * DEG;
    printf("%d %lld\n", best_N, m);
    for (int a = 0; a < halfA; a++)
        for (int s = 0; s < DEG; s++)
            printf("%d %d\n", a, bestnbr[a * DEG + s]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions (kept as calibration and as the first candidates).
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
# Main build.
# ----------------------------------------------------------------------------

_MAXN = 12000  # keeps C memory and per-evaluation time bounded


def _random_regular_search(d, D, start_n, maxn, seed, seconds):
    text = lib.run_c(C_SOURCE,
                     [d, D, start_n, maxn, int(seed) & 0x7FFFFFFF, round(seconds, 2)],
                     timeout=seconds + 10.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + budget

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

    # Main search: random regular bipartite graphs repaired by edge switches.
    if d >= 3 and D >= 3:
        remaining = deadline - time.monotonic()
        moore = lib.moore_bound(d, D)
        maxn = min(moore, _MAXN)
        maxn -= maxn % 2
        if remaining > 3.0 and maxn >= 2 * d + 2:
            guess = int(0.27 * moore)
            start_n = max(best_n + 2, min(maxn, guess))
            start_n -= start_n % 2
            try:
                n2, e2 = _random_regular_search(d, D, start_n, maxn, seed, remaining - 1.0)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
