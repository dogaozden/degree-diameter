import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: edge-switch annealing on bipartite d-regular graphs.
#
# A graph with sides A and B of size SIDE is kept d-regular. Each move picks
# two edges (a1,b1), (a2,b2) and rewires them to (a1,b2), (a2,b1). This keeps
# every degree equal to DEG and keeps the graph simple. The cost is the number
# of unordered vertex pairs at distance > DIAM, computed by bitset BFS from all
# vertices. Annealing runs in cycles with reheating; each cycle restarts from
# the best state found so far. A zero-cost state is a valid graph of order
# 2*SIDE. The search starts from a circulant (Haar) graph with random shifts.
#
# Vertices: A_a = a (0..SIDE-1), B_b = SIDE + b.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define CYC 3000
#define T_HI 2.0
#define T_LO 0.2
#define SIDE_MAX 3000

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int DEG, DIAM, SIDE, NV, NE, W;
static int *ea, *eb, *bea, *beb, *nbr, *ncnt;
static unsigned char *adjM;
static uint64_t *rA, *rB;

/* Unordered pairs at distance > DIAM. */
static long long eval_cost(void) {
    for (int v = 0; v < NV; v++) ncnt[v] = 0;
    for (int e = 0; e < NE; e++) {
        int a = ea[e], b = SIDE + eb[e];
        nbr[a * DEG + ncnt[a]++] = b;
        nbr[b * DEG + ncnt[b]++] = a;
    }
    uint64_t *cur = rA, *nxt = rB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)NV * W);
    for (int v = 0; v < NV; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int s = 0; s < DIAM; s++) {
        for (int v = 0; v < NV; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < DEG; k++) {
                const uint64_t *cu = cur + (size_t)nbr[v * DEG + k] * W;
                for (int w = 0; w < W; w++) o[w] |= cu[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < NV; v++) {
        int pc = 0;
        const uint64_t *c = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) pc += popc(c[w]);
        bad += NV - pc;
    }
    return bad / 2;
}

/* Pick two edges whose switch is legal (no shared endpoint, no duplicate edge). */
static int propose(int *pe1, int *pe2) {
    for (int tries = 0; tries < 60; tries++) {
        int e1 = rnd_int(NE), e2 = rnd_int(NE);
        if (e1 == e2) continue;
        int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
        if (a1 == a2 || b1 == b2) continue;
        if (adjM[a1 * SIDE + b2] || adjM[a2 * SIDE + b1]) continue;
        *pe1 = e1; *pe2 = e2;
        return 1;
    }
    return 0;
}

/* Apply the switch. Applying it again to the same pair undoes it. */
static void apply_sw(int e1, int e2) {
    int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
    eb[e1] = b2;
    eb[e2] = b1;
    adjM[a1 * SIDE + b1] = 0;
    adjM[a2 * SIDE + b2] = 0;
    adjM[a1 * SIDE + b2] = 1;
    adjM[a2 * SIDE + b1] = 1;
}

static void save_best(void) {
    memcpy(bea, ea, sizeof(int) * (size_t)NE);
    memcpy(beb, eb, sizeof(int) * (size_t)NE);
}

static void restore_best(void) {
    memcpy(ea, bea, sizeof(int) * (size_t)NE);
    memcpy(eb, beb, sizeof(int) * (size_t)NE);
    memset(adjM, 0, (size_t)SIDE * SIDE);
    for (int e = 0; e < NE; e++) adjM[ea[e] * SIDE + eb[e]] = 1;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed time_limit side\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    SIDE = atoi(argv[5]);
    if (DEG < 1 || DIAM < 1 || SIDE < DEG || SIDE > SIDE_MAX) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    NV = 2 * SIDE;
    NE = SIDE * DEG;
    W = (NV + 63) / 64;
    ea = malloc(sizeof(int) * (size_t)NE);
    eb = malloc(sizeof(int) * (size_t)NE);
    bea = malloc(sizeof(int) * (size_t)NE);
    beb = malloc(sizeof(int) * (size_t)NE);
    nbr = malloc(sizeof(int) * (size_t)NV * DEG);
    ncnt = malloc(sizeof(int) * (size_t)NV);
    adjM = calloc((size_t)SIDE * SIDE, 1);
    rA = malloc(sizeof(uint64_t) * (size_t)NV * W);
    rB = malloc(sizeof(uint64_t) * (size_t)NV * W);
    int *sh = malloc(sizeof(int) * (size_t)DEG);

    /* Start: circulant (Haar-type) graph with DEG distinct random shifts. */
    for (int k = 0; k < DEG; k++) {
        int s, dup;
        do {
            s = rnd_int(SIDE);
            dup = 0;
            for (int j = 0; j < k; j++) if (sh[j] == s) dup = 1;
        } while (dup);
        sh[k] = s;
    }
    for (int a = 0; a < SIDE; a++)
        for (int k = 0; k < DEG; k++) {
            int e = a * DEG + k;
            ea[e] = a;
            eb[e] = (a + sh[k]) % SIDE;
            adjM[a * SIDE + eb[e]] = 1;
        }
    for (int i = 0; i < 10 * NE; i++) {
        int e1, e2;
        if (propose(&e1, &e2)) apply_sw(e1, e2);
    }

    long long cur = eval_cost();
    long long best = cur;
    save_best();

    while (best > 0 && elapsed() < DEADLINE) {
        restore_best();
        cur = best;
        for (int it = 0; it < CYC && best > 0; it++) {
            if ((it & 15) == 0 && elapsed() > DEADLINE) break;
            double temp = T_HI * pow(T_LO / T_HI, (double)it / CYC);
            int e1, e2;
            if (!propose(&e1, &e2)) continue;
            apply_sw(e1, e2);
            long long c2 = eval_cost();
            long long dl = c2 - cur;
            if (dl <= 0 || rnd_unit() < exp(-(double)dl / temp)) {
                cur = c2;
                if (cur < best) {
                    best = cur;
                    save_best();
                }
            } else {
                apply_sw(e1, e2);
            }
        }
    }

    if (best == 0) {
        restore_best();
        printf("%d %d\n", NV, NE);
        for (int e = 0; e < NE; e++)
            printf("%d %d\n", ea[e], SIDE + eb[e]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
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
# Driver: baselines, then chained edge-switch annealing for sides one above
# the current best. Every returned graph is checked with lib.is_valid.
# ----------------------------------------------------------------------------

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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    # Edge-switch annealing: a d-regular bipartite graph with side s has order 2s.
    # Try s = (current best)/2 + 1 first; each success moves the target up by one side.
    deadline = start + 0.92 * time_limit - 1.5
    side = best_n // 2 + 1
    run_seed = seed
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 3.0 or 2 * side > moore or side > 3000:
            break
        try:
            out = lib.run_c(C_SOURCE, [d, D, run_seed, f"{remaining:.2f}", side],
                            timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
        except Exception:
            break
        if n == 0 or not e:
            break
        if not lib.is_valid(n, e, d, D):
            break
        if n > best_n:
            best = (n, e)
            best_n = n
        side = n // 2 + 1
        run_seed += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
