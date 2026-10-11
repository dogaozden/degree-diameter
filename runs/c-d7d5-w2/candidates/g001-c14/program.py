import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: Haar graphs of abelian groups.
#
# Group G = Z_A x Z_B (element i*B + j), A*B = G. Choose a d-set S in G and
# join A_x to B_{x+s} for s in S. This is a d-regular bipartite graph on 2G
# vertices, and translations are automorphisms, so it has diameter <= D iff
# BFS from A_0 and from B_0 reaches everything within D steps.
#
# Search: simulated annealing over S (replace one element). Cost = unreached
# (source, vertex) pairs from A_0 and B_0. The window [lo, hi] is climbed
# adaptively: candidates are base + 1 + random step, where the step fraction
# grows after successes and shrinks after failures.
#
# Usage: prog d D lo hi seed slice_seconds
# Prints a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int DEG, DIAM, A_, B_, G;
static int *S, *NS, *nbA, *nbB, *qa, *qb, *bestS;
static uint32_t *vis;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static inline int addg(int x, int y) {
    int i = x / B_, j = x % B_, k = y / B_, l = y % B_;
    int ii = i + k; if (ii >= A_) ii -= A_;
    int jj = j + l; if (jj >= B_) jj -= B_;
    return ii * B_ + jj;
}

static inline int negg(int x) {
    int i = x / B_, j = x % B_;
    int ii = i ? A_ - i : 0;
    int jj = j ? B_ - j : 0;
    return ii * B_ + jj;
}

static void set_col(int k) {
    int s = S[k], ns = NS[k];
    for (int x = 0; x < G; x++) {
        nbA[(size_t)x * DEG + k] = G + addg(x, s);
        nbB[(size_t)x * DEG + k] = addg(x, ns);
    }
}

static int reach_from(int src) {
    if (stamp == 0xFFFFFFFFu) {
        memset(vis, 0, sizeof(uint32_t) * (size_t)(2 * G));
        stamp = 0;
    }
    stamp++;
    int *cur = qa, *nxt = qb;
    int fn = 1, reached = 1;
    cur[0] = src;
    vis[src] = stamp;
    for (int lv = 0; lv < DIAM && fn > 0; lv++) {
        int nn = 0;
        for (int q = 0; q < fn; q++) {
            int u = cur[q];
            const int *nb = (u < G) ? nbA + (size_t)u * DEG : nbB + (size_t)(u - G) * DEG;
            for (int t = 0; t < DEG; t++) {
                int v = nb[t];
                if (vis[v] != stamp) {
                    vis[v] = stamp;
                    nxt[nn++] = v;
                }
            }
        }
        reached += nn;
        int *tmp = cur; cur = nxt; nxt = tmp;
        fn = nn;
    }
    return reached;
}

static int cost_fn(void) {
    int r1 = reach_from(0);
    int r2 = reach_from(G);
    return (2 * G - r1) + (2 * G - r2);
}

static int anneal(clock_t dl) {
    for (int k = 0; k < DEG; k++) {
        int t;
        for (;;) {
            t = rndint(G);
            int dup = 0;
            for (int j = 0; j < k; j++) if (S[j] == t) { dup = 1; break; }
            if (!dup) break;
        }
        S[k] = t;
        NS[k] = negg(t);
    }
    for (int k = 0; k < DEG; k++) set_col(k);
    int cur = cost_fn();
    if (cur == 0) return 1;

    const int RL = 20000;
    long it = 0;
    for (;;) {
        if ((it & 63) == 0 && clock() >= dl) return 0;
        double T = 2.0 * (1.0 - (double)(it % RL) / RL) + 0.03;
        it++;
        int k = rndint(DEG);
        int t = -1;
        for (int tries = 0; tries < 100; tries++) {
            int c = rndint(G), dup = 0;
            for (int j = 0; j < DEG; j++) if (S[j] == c) { dup = 1; break; }
            if (!dup) { t = c; break; }
        }
        if (t < 0) continue;
        int old = S[k], oldn = NS[k];
        S[k] = t;
        NS[k] = negg(t);
        set_col(k);
        int nc = cost_fn();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            S[k] = old;
            NS[k] = oldn;
            set_col(k);
        }
        if (cur == 0) return 1;
    }
}

int main(int argc, char **argv) {
    if (argc < 7) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    int lo = atoi(argv[3]), hi = atoi(argv[4]);
    uint64_t seed = strtoull(argv[5], NULL, 10);
    double slice = atof(argv[6]);
    if (DEG < 1 || DIAM < 1 || lo < DEG || hi < lo) { printf("0 0\n"); return 0; }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;

    int maxG = hi;
    S = malloc(sizeof(int) * DEG);
    NS = malloc(sizeof(int) * DEG);
    bestS = malloc(sizeof(int) * DEG);
    nbA = malloc(sizeof(int) * (size_t)maxG * DEG);
    nbB = malloc(sizeof(int) * (size_t)maxG * DEG);
    vis = calloc(2 * (size_t)maxG, sizeof(uint32_t));
    qa = malloc(sizeof(int) * 2 * (size_t)maxG);
    qb = malloc(sizeof(int) * 2 * (size_t)maxG);
    if (!S || !NS || !bestS || !nbA || !nbB || !vis || !qa || !qb) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    clock_t tend = t0 + (clock_t)(slice * CLOCKS_PER_SEC);
    int base = lo - 1, bestG = 0, bestA = 0, bestB = 0;
    double frac = 0.05;

    while (clock() < tend && base < hi) {
        int span = (int)(base * frac);
        if (span < 1) span = 1;
        int g = base + 1 + rndint(span);
        if (g > hi) g = hi;
        int divs[256];
        int nd = 0;
        for (int x = 1; x <= g && nd < 256; x++) if (g % x == 0) divs[nd++] = x;
        int b = (rnd01() < 0.4) ? 1 : divs[rndint(nd)];
        A_ = g / b;
        B_ = b;
        G = g;

        double rem = (double)(tend - clock()) / CLOCKS_PER_SEC;
        double ch = slice / 10.0;
        if (ch < 0.3) ch = 0.3;
        if (ch > rem) ch = rem;
        clock_t dl = clock() + (clock_t)(ch * CLOCKS_PER_SEC);

        if (anneal(dl)) {
            base = g;
            bestG = g; bestA = A_; bestB = B_;
            memcpy(bestS, S, sizeof(int) * DEG);
            frac *= 1.25;
            if (frac > 0.08) frac = 0.08;
        } else {
            frac *= 0.7;
            if (frac < 0.001) frac = 0.001;
        }
    }

    if (bestG == 0) { printf("0 0\n"); return 0; }
    A_ = bestA; B_ = bestB; G = bestG;
    memcpy(S, bestS, sizeof(int) * DEG);
    for (int k = 0; k < DEG; k++) { NS[k] = negg(S[k]); set_col(k); }
    if (cost_fn() != 0) { printf("0 0\n"); return 0; }

    printf("%d %d\n", 2 * G, G * DEG);
    for (int x = 0; x < G; x++) {
        for (int k = 0; k < DEG; k++) {
            printf("%d %d\n", x, G + addg(x, S[k]));
        }
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact / safe constructions.
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
# Driver. Haar graphs H(G, S) of abelian groups are the main search family.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ap = lib.araujo_lopez_graph(d - 2)
                consider(ap[0], ap[1])
            except (ValueError, RuntimeError):
                pass

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: Haar graphs of Z_A x Z_B with a d-set S, climbing the
    # group order. Every success is a strict improvement over `best`.
    if d >= 2 and D >= 2:
        M = lib.moore_bound(d, D)
        hi = M // 2
        lo = max(d, best[0] // 2)
        remaining = deadline - time.monotonic()
        if lo < hi and remaining > 3.0:
            slice_s = remaining - 2.0
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, lo, hi, seed, f"{slice_s:.2f}"],
                    timeout=slice_s + 15.0,
                )
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
