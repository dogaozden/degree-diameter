import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New approach: direct annealing over d-regular bipartite graphs.
#
# The C engine keeps a d-regular bipartite graph on n vertices (sides A and B)
# and minimises the number of vertex pairs at distance > D. Moves are
# degree- and bipartition-preserving 2-switches. When the cost reaches 0, the
# graph is saved and grown by 2 vertices (one per side) using a matching of d
# edges that is rerouted through the new pair, so it stays regular. The best
# valid graph is printed when time runs out. The start is K_{d,d}.
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

static int DEG, DIAM, CAP, NN, WCAP;
static int *nb, *bestnb, *stamp, *GA, *GB;
static char *isA;
static uint64_t *BA, *BB;
static int bestN;
static double TL, tstart;
static int gen_ctr = 0;

static double elapsed(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int slot(int v, int u) {
    for (int l = 0; l < DEG; l++)
        if (nb[v * DEG + l] == u) return l;
    return -1;
}

static int has_edge(int a, int b) {
    return slot(a, b) >= 0;
}

/* Precondition: nb[a][la] = b and nb[c][lc] = e, with a,c in A and b,e in B.
   Postcondition: nb[a][la] = e and nb[c][lc] = b, with reverse entries fixed. */
static void sw(int a, int la, int c, int lc, int b, int e) {
    nb[a * DEG + la] = e;
    nb[c * DEG + lc] = b;
    int s = slot(e, c);
    nb[e * DEG + s] = a;
    s = slot(b, a);
    nb[b * DEG + s] = c;
}

/* Number of unordered vertex pairs at distance > DIAM. */
static long long eval_cost(void) {
    int n = NN;
    int w = (n + 63) >> 6;
    uint64_t *cur = BA, *nxt = BB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)w);
    for (int v = 0; v < n; v++)
        cur[(size_t)v * w + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * w;
            const uint64_t *src = cur + (size_t)v * w;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)w);
            for (int l = 0; l < DEG; l++) {
                const uint64_t *s2 = cur + (size_t)nb[v * DEG + l] * w;
                for (int j = 0; j < w; j++) dst[j] |= s2[j];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long reached = 0;
    for (int v = 0; v < n; v++)
        for (int j = 0; j < w; j++)
            reached += pc64(cur[(size_t)v * w + j]);
    long long total = (long long)n * n - reached;
    return total / 2;
}

static void save_best(void) {
    memcpy(bestnb, nb, sizeof(int) * (size_t)NN * DEG);
    bestN = NN;
}

/* Add two vertices x (side A, label NN) and y (side B, label NN+1). */
static int grow(void) {
    if (NN + 2 > CAP) return 0;
    gen_ctr++;
    int cnt = 0;
    for (long tries = 0; cnt < DEG && tries < 200000; tries++) {
        int a = rndint(NN);
        if (!isA[a]) continue;
        int b = nb[a * DEG + rndint(DEG)];
        if (stamp[a] == gen_ctr || stamp[b] == gen_ctr) continue;
        stamp[a] = gen_ctr;
        stamp[b] = gen_ctr;
        GA[cnt] = a;
        GB[cnt] = b;
        cnt++;
    }
    if (cnt < DEG) return 0;
    int x = NN, y = NN + 1;
    for (int i = 0; i < DEG; i++) {
        int a = GA[i], b = GB[i];
        nb[a * DEG + slot(a, b)] = y;
        nb[b * DEG + slot(b, a)] = x;
        nb[x * DEG + i] = b;
        nb[y * DEG + i] = a;
    }
    isA[x] = 1;
    isA[y] = 0;
    NN += 2;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: d D cap seed time\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    CAP = atoi(argv[3]);
    unsigned long long seed = strtoull(argv[4], NULL, 10);
    TL = atof(argv[5]);
    tstart = (double)clock() / CLOCKS_PER_SEC;

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (DEG < 2 || DIAM < 2 || CAP < 2 * DEG + 2) {
        printf("0 0\n");
        return 0;
    }

    WCAP = (CAP + 63) / 64;
    nb = malloc(sizeof(int) * (size_t)CAP * DEG);
    bestnb = malloc(sizeof(int) * (size_t)CAP * DEG);
    stamp = calloc((size_t)CAP, sizeof(int));
    GA = malloc(sizeof(int) * (size_t)DEG);
    GB = malloc(sizeof(int) * (size_t)DEG);
    isA = calloc((size_t)CAP, 1);
    BA = malloc(sizeof(uint64_t) * (size_t)CAP * WCAP);
    BB = malloc(sizeof(uint64_t) * (size_t)CAP * WCAP);
    if (!nb || !bestnb || !stamp || !GA || !GB || !isA || !BA || !BB) {
        printf("0 0\n");
        return 0;
    }

    /* Start: K_{DEG,DEG}. A = 0..DEG-1, B = DEG..2DEG-1. */
    for (int a = 0; a < DEG; a++) {
        isA[a] = 1;
        for (int l = 0; l < DEG; l++) nb[a * DEG + l] = DEG + l;
    }
    for (int b = DEG; b < 2 * DEG; b++) {
        isA[b] = 0;
        for (int l = 0; l < DEG; l++) nb[b * DEG + l] = l;
    }
    NN = 2 * DEG;
    save_best();

    long long cost = eval_cost();
    long long moves = 0;

    while (elapsed() < TL) {
        if (cost == 0) {
            save_best();
            if (!grow()) break;
            cost = eval_cost();
            continue;
        }
        moves++;
        double frac = (double)(moves % 3000) / 3000.0;
        double temp = 0.25 + 0.75 * (1.0 - frac);

        int a, c;
        do { a = rndint(NN); } while (!isA[a]);
        do { c = rndint(NN); } while (!isA[c]);
        int la = rndint(DEG), lc = rndint(DEG);
        int b = nb[a * DEG + la];
        int e = nb[c * DEG + lc];
        if (a == c || b == e) continue;
        if (has_edge(a, e) || has_edge(c, b)) continue;

        sw(a, la, c, lc, b, e);
        long long c2 = eval_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost == 0) save_best();
        } else {
            sw(a, la, c, lc, e, b);
        }
    }

    int n = bestN;
    long long m = (long long)n * DEG / 2;
    printf("%d %lld\n", n, m);
    for (int v = 0; v < n; v++)
        for (int l = 0; l < DEG; l++) {
            int u = bestnb[v * DEG + l];
            if (v < u) printf("%d %d\n", v, u);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions (used as fallbacks and for small calibration cases).
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
# Main build: exact constructions, then the C annealing search, with fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for any D >= 2.
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

    if D == 4 and time.monotonic() - start < 0.5 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if d >= 3 and D >= 3:
        budget = min(0.80 * time_limit, time_limit - 8.0)
        if budget >= 1.0:
            cap = min(lib.moore_bound(d, D), 9000)
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, cap, int(seed) & 0x7FFFFFFF, round(budget, 2)],
                                 timeout=budget + 4.0)
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
