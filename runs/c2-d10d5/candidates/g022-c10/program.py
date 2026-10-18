import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: unstructured repair search instead of bi-Cayley voltage lifts.
#
# The C engine keeps a d-regular bipartite graph on explicit vertex ids and
# grows it by inserting one (A, B) pair of new vertices at a time. Inserting a
# pair removes d edges that form a matching and reconnects them through the two
# new vertices, so every degree stays exactly d. The graph is then repaired by
# simulated annealing over degree-preserving double-edge swaps. The cost is the
# number of ordered vertex pairs at distance > D, computed with bitsets.
# If repair fails, the search reverts to the last valid graph and halves the
# insertion batch. Every returned graph is re-checked with lib.is_valid, and
# K_{d,d} (or the exact PG/GQ start) is always the fallback.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define ITERS 3000

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
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static int DEG, DIAM, CAP, WMAX;
static int NN, NA, NB;
static int *nb, *Al, *Bl;
static int *bnb, *bAl, *bBl;
static int bNN, bNA, bNB;
static uint64_t *R1, *R2;
static double T_END;

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of ordered pairs (v, u) with dist(v, u) > DIAM. Zero iff valid. */
static int64_t evaluate(void) {
    int n = NN, w = (n + 63) >> 6;
    uint64_t *cur = R1, *nxt = R2;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)w);
    for (int v = 0; v < n; v++)
        cur[(size_t)v * w + (v >> 6)] = 1ULL << (v & 63);
    for (int t = 0; t < DIAM; t++) {
        int changed = 0;
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * w;
            const uint64_t *src = cur + (size_t)v * w;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)w);
            for (int j = 0; j < DEG; j++) {
                const uint64_t *s = cur + (size_t)nb[v * DEG + j] * w;
                for (int k = 0; k < w; k++) dst[k] |= s[k];
            }
            for (int k = 0; k < w; k++)
                if (dst[k] != src[k]) changed = 1;
        }
        uint64_t *tp = cur;
        cur = nxt;
        nxt = tp;
        if (!changed) break;
    }
    int64_t miss = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *s = cur + (size_t)v * w;
        int c = 0;
        for (int k = 0; k < w; k++) c += pc64(s[k]);
        miss += n - c;
    }
    return miss;
}

static int has_edge(int a, int b) {
    for (int j = 0; j < DEG; j++)
        if (nb[a * DEG + j] == b) return 1;
    return 0;
}

static int slot_of(int v, int u) {
    for (int j = 0; j < DEG; j++)
        if (nb[v * DEG + j] == u) return j;
    return -1;
}

/* Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Self-inverse with the same arguments. */
static void swap2(int a1, int j1, int a2, int j2) {
    int b1 = nb[a1 * DEG + j1], b2 = nb[a2 * DEG + j2];
    nb[a1 * DEG + j1] = b2;
    nb[a2 * DEG + j2] = b1;
    nb[b1 * DEG + slot_of(b1, a1)] = a2;
    nb[b2 * DEG + slot_of(b2, a2)] = a1;
}

/* Insert a new A vertex x and a new B vertex y, each of degree DEG, by removing a matching of DEG edges. */
static int insert_pair(void) {
    if (NN + 2 > CAP) return 0;
    int ea[64], eb[64], ej[64];
    int cnt = 0;
    for (long tries = 0; cnt < DEG && tries < 200000L; tries++) {
        int a = Al[rndint(NA)], j = rndint(DEG);
        int b = nb[a * DEG + j];
        int ok = 1;
        for (int i = 0; i < cnt; i++)
            if (ea[i] == a || eb[i] == b) {
                ok = 0;
                break;
            }
        if (!ok) continue;
        ea[cnt] = a;
        eb[cnt] = b;
        ej[cnt] = j;
        cnt++;
    }
    if (cnt < DEG) return 0;
    int x = NN, y = NN + 1;
    NN += 2;
    for (int i = 0; i < DEG; i++) {
        int a = ea[i], b = eb[i], j = ej[i];
        nb[a * DEG + j] = y;
        nb[b * DEG + slot_of(b, a)] = x;
        nb[y * DEG + i] = a;
        nb[x * DEG + i] = b;
    }
    Al[NA++] = x;
    Bl[NB++] = y;
    return 1;
}

/* Simulated annealing over double-edge swaps. Returns 1 if the graph becomes valid. */
static int anneal(void) {
    int64_t c = evaluate();
    if (c == 0) return 1;
    double T0 = 0.02 * (double)c + 1.0;
    for (int t = 0; t < ITERS; t++) {
        if (now_s() > T_END) break;
        double T = T0 * (1.0 - (double)t / ITERS) + 0.05;
        int a1 = Al[rndint(NA)], j1 = rndint(DEG);
        int a2 = Al[rndint(NA)], j2 = rndint(DEG);
        if (a1 == a2) continue;
        int b1 = nb[a1 * DEG + j1], b2 = nb[a2 * DEG + j2];
        if (b1 == b2) continue;
        if (has_edge(a1, b2) || has_edge(a2, b1)) continue;
        swap2(a1, j1, a2, j2);
        int64_t c2 = evaluate();
        if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) {
            c = c2;
            if (c == 0) return 1;
        } else {
            swap2(a1, j1, a2, j2);
        }
    }
    return c == 0;
}

static void save_backup(void) {
    bNN = NN;
    bNA = NA;
    bNB = NB;
    memcpy(bnb, nb, sizeof(int) * (size_t)NN * DEG);
    memcpy(bAl, Al, sizeof(int) * (size_t)NA);
    memcpy(bBl, Bl, sizeof(int) * (size_t)NB);
}

static void restore_backup(void) {
    NN = bNN;
    NA = bNA;
    NB = bNB;
    memcpy(nb, bnb, sizeof(int) * (size_t)NN * DEG);
    memcpy(Al, bAl, sizeof(int) * (size_t)NA);
    memcpy(Bl, bBl, sizeof(int) * (size_t)NB);
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
    double budget = atof(argv[5]);
    T_END = now_s() + budget;

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (DEG < 3 || DEG > 64 || DIAM < 2 || CAP < 2 * DEG) {
        printf("0 0\n");
        return 0;
    }

    WMAX = (CAP + 63) / 64;
    nb = malloc(sizeof(int) * (size_t)CAP * DEG);
    bnb = malloc(sizeof(int) * (size_t)CAP * DEG);
    Al = malloc(sizeof(int) * (size_t)CAP);
    Bl = malloc(sizeof(int) * (size_t)CAP);
    bAl = malloc(sizeof(int) * (size_t)CAP);
    bBl = malloc(sizeof(int) * (size_t)CAP);
    R1 = malloc(sizeof(uint64_t) * (size_t)CAP * WMAX);
    R2 = malloc(sizeof(uint64_t) * (size_t)CAP * WMAX);
    if (!nb || !bnb || !Al || !Bl || !bAl || !bBl || !R1 || !R2) {
        printf("0 0\n");
        return 0;
    }

    /* Start: K_{d,d}, valid for diameter >= 2. A = 0..d-1, B = d..2d-1. */
    NA = NB = 0;
    NN = 2 * DEG;
    for (int i = 0; i < DEG; i++) {
        Al[NA++] = i;
        Bl[NB++] = DEG + i;
        for (int j = 0; j < DEG; j++) {
            nb[i * DEG + j] = DEG + j;
            nb[(DEG + j) * DEG + i] = i;
        }
    }
    save_backup();

    int inc = 1;
    while (now_s() < T_END) {
        if (NN + 2 > CAP) break;
        int ok = 1;
        for (int k = 0; k < inc; k++) {
            if (!insert_pair()) {
                ok = 0;
                break;
            }
        }
        if (ok) ok = anneal();
        if (ok) {
            save_backup();
            inc *= 2;
            int cap_inc = NA / 16;
            if (cap_inc < 1) cap_inc = 1;
            if (inc > cap_inc) inc = cap_inc;
        } else {
            restore_backup();
            if (inc > 1) inc /= 2;
        }
    }

    /* The backup is always a valid graph. Vertex ids are 0..bNN-1. */
    printf("%d %ld\n", bNN, (long)bNA * DEG);
    for (int i = 0; i < bNA; i++) {
        int a = bAl[i];
        for (int j = 0; j < DEG; j++)
            printf("%d %d\n", a, bnb[a * DEG + j]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions used as start graphs and fallbacks.
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
# Main build: exact starts, then the C repair-growth search, then validation.
# ----------------------------------------------------------------------------

_MAX_CAP = 5000  # bitset cost per evaluation grows with n; keep it bounded


def build(d, D, seed, time_limit):
    start = time.monotonic()

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

    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() - start < budget:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search in C: repair-growth of a d-regular bipartite graph.
    if d >= 3 and D >= 3:
        remaining = budget - (time.monotonic() - start)
        if remaining > 2.0:
            cap = min(lib.moore_bound(d, D), _MAX_CAP)
            if cap >= 2 * d:
                try:
                    text = lib.run_c(C_SOURCE,
                                     [d, D, cap, int(seed) & 0x7FFFFFFF, round(remaining, 2)],
                                     timeout=remaining + 15.0)
                    n2, e2 = lib.parse_graph_text(text)
                    consider(n2, e2)
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
