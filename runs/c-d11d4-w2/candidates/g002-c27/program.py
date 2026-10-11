import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: Cayley-Haar graphs over non-abelian groups.
#
# A "base 2" lift with d darts (a_x ~ b_{x*g_i}) over a group G is a bipartite
# d-regular graph on 2|G| vertices, and it is a Cayley-type graph, so it needs
# only d voltages instead of a whole base graph. Vertices are a_x = x and
# b_y = |G| + y. G = Z_m x| Z_k with element (a, b) coded a*k + b and product
# (a, b)(c, d) = (a + r^b c, b + d), r^k = 1 mod m.
#
# C side: simulated annealing over the d distinct voltages. Cost = number of
# vertex pairs at distance > D (bitset ball propagation). When cost reaches 0
# the graph is printed.
#
# Python side: bisect on |G| between a feasible fallback and the Moore half
# bound. Each probe tries a few groups of that order. The best valid graph
# found is returned, with K_{d,d} or a generalized quadrangle / projective
# plane as the fallback. Every result is checked with lib.is_valid.
# ----------------------------------------------------------------------------

MAX_G = 1200

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 1200
#define MAXV (2 * MAXG)
#define WMAX ((MAXV + 63) / 64)
#define MAXD 32
#define MAXK 64

static int GM, GK, GR, GN, DEG, DIAM;
static int pw[MAXK];
static int vg[MAXD];
static int adj[MAXV][MAXD];
static int dg[MAXV];
static int BOK;
static uint64_t BA[MAXV * WMAX], BB[MAXV * WMAX];
static uint64_t rs = 1;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nextr() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* (a,b)*(c,d) = (a + r^b c, b + d) in Z_m x| Z_k, element coded a*k+b */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, d = y % GK;
    return ((a + pw[b] * c) % GM) * GK + (b + d) % GK;
}

/* a_x = x, b_y = GN + y; dart g joins a_x to b_{x*g}. */
static void build(void) {
    int n = 2 * GN;
    BOK = 1;
    for (int v = 0; v < n; v++) dg[v] = 0;
    for (int x = 0; x < GN; x++) {
        for (int i = 0; i < DEG; i++) {
            int y = GN + gmul(x, vg[i]);
            if (dg[x] >= DEG || dg[y] >= DEG) {
                BOK = 0;
                continue;
            }
            adj[x][dg[x]++] = y;
            adj[y][dg[y]++] = x;
        }
    }
}

static long long cost(void) {
    if (!BOK) return 1000000000LL;
    int n = 2 * GN;
    int W = (n + 63) >> 6;
    uint64_t *cur = BA, *nxt = BB, *tmp;
    memset(BA, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++)
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            uint64_t *s = cur + (size_t)v * W;
            memcpy(o, s, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < dg[v]; i++) {
                uint64_t *t = cur + (size_t)adj[v][i] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        uint64_t *s = cur + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(s[w]);
        bad += n - cnt;
    }
    return bad / 2;
}

int main(int argc, char **argv) {
    if (argc < 8) {
        fprintf(stderr, "usage: prog m k r d D seed time\n");
        return 1;
    }
    GM = atoi(argv[1]);
    GK = atoi(argv[2]);
    GR = atoi(argv[3]);
    DEG = atoi(argv[4]);
    DIAM = atoi(argv[5]);
    unsigned long long seed = strtoull(argv[6], NULL, 10);
    double tl = atof(argv[7]);
    if (GM < 1 || GK < 1 || GK > MAXK) {
        printf("0 0\n");
        return 0;
    }
    GN = GM * GK;
    if (GN < 2 || GN > MAXG || DEG < 1 || DEG > MAXD || DEG >= GN || DIAM < 1 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    GR = ((GR % GM) + GM) % GM;
    rs = seed * 0x9E3779B97F4A7C15ULL + 4242ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();
    pw[0] = 1 % GM;
    for (int b = 1; b < GK; b++) pw[b] = (pw[b - 1] * GR) % GM;

    for (int i = 0; i < DEG; i++) {
        int g, ok;
        do {
            g = rnd(GN);
            ok = 1;
            for (int j = 0; j < i; j++)
                if (vg[j] == g) { ok = 0; break; }
        } while (!ok);
        vg[i] = g;
    }
    build();
    if (!BOK) {
        printf("0 0\n");
        return 0;
    }
    long long cur = cost();
    clock_t t0 = clock();
    double frac = 0.0;
    long long it = 0;
    while (cur != 0) {
        if ((it & 7) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= tl) break;
            frac = el / tl;
        }
        it++;
        int i = rnd(DEG);
        int old = vg[i];
        int g, ok;
        do {
            g = rnd(GN);
            ok = 1;
            for (int j = 0; j < DEG; j++)
                if (vg[j] == g) { ok = 0; break; }
        } while (!ok);
        vg[i] = g;
        build();
        long long c2 = cost();
        double dl = (double)(c2 - cur) / ((double)cur + 1.0);
        double T = 0.02 + 0.1 * (1.0 - frac);
        if (dl <= 0 || rnd01() < exp(-dl / T)) {
            cur = c2;
        } else {
            vg[i] = old;
            build();
        }
    }

    if (cur == 0) {
        printf("%d %d\n", 2 * GN, GN * DEG);
        for (int x = 0; x < GN; x++)
            for (int i = 0; i < DEG; i++)
                printf("%d %d\n", x, GN + gmul(x, vg[i]));
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _groups_of_order(G, rng, max_groups=4):
    """Candidate groups Z_m x| Z_k of order G as (m, k, r) triples, shuffled and capped."""
    cands = []
    for k in range(1, min(G, 12) + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            cands.append((m, 1, 1))
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        for r in rng.sample(rs, min(3, len(rs))):
            cands.append((m, k, r))
    rng.shuffle(cands)
    return cands[:max_groups]


def _run_group(d, D, m, k, r, seed, budget):
    """Run the C annealer for one group; return a validated (n, edges) or None."""
    out = lib.run_c(C_SOURCE, [m, k, r, d, D, seed, f"{budget:.2f}"],
                    timeout=budget + 5.0)
    n, edges = lib.parse_graph_text(out)
    if n == 0 or not edges:
        return None
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return None


def _cayley_bisect(d, D, lo, hi, rng, end, seed):
    """Bisect the group order G (graph has 2G vertices) over (lo, hi].

    Each probe tries a few groups of order mid. Success moves lo up, failure
    moves hi down. Returns the largest valid graph found, or None.
    """
    best = None
    probe = 0
    while lo < hi and time.monotonic() < end - 1.0:
        mid = (lo + hi + 1) // 2
        groups = _groups_of_order(mid, rng, 4)
        if not groups:
            hi = mid - 1
            continue
        remaining = end - time.monotonic()
        budget = min(max(1.5, 0.25 * remaining), 8.0)
        per = budget / len(groups)
        got = None
        for m, k, r in groups:
            if time.monotonic() >= end - 0.5:
                break
            probe += 1
            try:
                got = _run_group(d, D, m, k, r, seed * 1000 + probe, per)
            except Exception:
                got = None
            if got is not None:
                break
        if got is not None:
            best = got
            lo = mid
        else:
            hi = mid - 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Calibration: D = 3 with d - 1 a prime power is the Moore-optimal incidence graph.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, e0, d, D):
            return n0, e0

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Structured fallbacks: projective plane for D = 3, W(q) for D >= 4.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if q <= 40 and lib.is_prime_power(q):
                n1, e1 = lib.projective_plane_incidence(q)
                consider(n1, e1)
                break
    if D >= 4 and d >= 5:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: Cayley-Haar graphs over semidirect products, bisected on |G|.
    end = start + 0.85 * tl - 1.0
    hi = min(lib.moore_bound(d, D) // 2, MAX_G)
    lo = max(best_n // 2, d)
    if hi > lo and time.monotonic() < end:
        got = _cayley_bisect(d, D, lo, hi, rng, end, seed)
        if got is not None:
            consider(got[0], got[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
