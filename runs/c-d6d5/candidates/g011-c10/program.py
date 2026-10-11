import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: direct graph-level search over bipartite DEG-regular graphs.
#
# Unlike the voltage-lift search, this engine works on the graph itself. It
# starts from a random DEG-regular bipartite graph on N vertices (A side 0..H-1,
# B side 0..H-1). The moves are degree-preserving double-edge swaps that keep the
# graph simple. The cost is the number of ordered vertex pairs at distance more
# than DIAM, computed by bitset BFS (reach sets, DIAM rounds of OR over
# neighbours). Simulated annealing runs in cycles. Each cycle restarts from the
# best state of the previous cycle.
#
# When cost reaches 0 the graph is valid and is saved. The engine then grows it
# by two vertices (one new A and one new B vertex). Growth removes DEG-1 edges
# with distinct endpoints, reattaches them to the new vertices, and adds the
# remaining edges, so the graph stays DEG-regular and simple. Search continues
# at the larger order. If no valid graph has appeared after several cycles at a
# start order, the engine restarts at a slightly smaller order.
#
# Output: the largest valid graph saved, as "n m" plus edges. Vertex labels are
# A = 0..H-1 and B = H..2H-1, so the graph is bipartite by construction.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 1400
#define HM 700
#define WM 22
#define CYC 3000
#define FAILCYC 12
#define MAXDEG 64

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;
static int DEG, DIAM, H, E;
static int *ea, *eb, *sa, *sb, *bestA, *bestB;
static int *M;
static int *nb, *ndeg;
static uint64_t *R0, *R1;
static int bestN = 0, bestE = 0, bestH = 0;
static int *tmpperm;

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

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void alloc_all(void) {
    int emax = HM * DEG;
    ea = malloc(sizeof(int) * emax);
    eb = malloc(sizeof(int) * emax);
    sa = malloc(sizeof(int) * emax);
    sb = malloc(sizeof(int) * emax);
    bestA = malloc(sizeof(int) * emax);
    bestB = malloc(sizeof(int) * emax);
    M = calloc((size_t)HM * HM, sizeof(int));
    nb = malloc(sizeof(int) * NMAX * DEG);
    ndeg = malloc(sizeof(int) * NMAX);
    R0 = malloc(sizeof(uint64_t) * NMAX * WM);
    R1 = malloc(sizeof(uint64_t) * NMAX * WM);
    tmpperm = malloc(sizeof(int) * HM);
}

static void rebuild_M(void) {
    memset(M, 0, sizeof(int) * (size_t)HM * HM);
    for (int e = 0; e < E; e++) M[ea[e] * HM + eb[e]]++;
}

static int count_dups(void) {
    int c = 0;
    for (int e = 0; e < E; e++)
        if (M[ea[e] * HM + eb[e]] > 1) c++;
    return c;
}

/* Change the B endpoint of edge e, keeping M consistent. */
static inline void setb(int e, int nbv) {
    int a = ea[e];
    M[a * HM + eb[e]]--;
    M[a * HM + nbv]++;
    eb[e] = nbv;
}

/* Cost = number of ordered pairs at distance > DIAM (0 iff valid). */
static long long evalcost(void) {
    int n = 2 * H;
    int W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) ndeg[v] = 0;
    for (int e = 0; e < E; e++) {
        int a = ea[e], b = H + eb[e];
        nb[a * DEG + ndeg[a]++] = b;
        nb[b * DEG + ndeg[b]++] = a;
    }
    uint64_t *cur = R0, *nxt = R1;
    for (int v = 0; v < n; v++)
        for (int w = 0; w < W; w++) cur[v * WM + w] = 0;
    for (int v = 0; v < n; v++) cur[v * WM + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *out = nxt + v * WM;
            const uint64_t *in = cur + v * WM;
            for (int w = 0; w < W; w++) out[w] = in[w];
            for (int k = 0; k < DEG; k++) {
                const uint64_t *src = cur + (size_t)nb[v * DEG + k] * WM;
                for (int w = 0; w < W; w++) out[w] |= src[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long cnt = 0;
    for (int v = 0; v < n; v++)
        for (int w = 0; w < W; w++) cnt += pc64(cur[v * WM + w]);
    return (long long)n * n - cnt;
}

/* Random DEG-regular simple bipartite graph on H + H vertices. Returns 1 on success. */
static int random_init(void) {
    int h = H;
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < h; i++) tmpperm[i] = i;
        for (int i = h - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int tmp = tmpperm[i]; tmpperm[i] = tmpperm[j]; tmpperm[j] = tmp;
        }
        for (int i = 0; i < h; i++) {
            int e = l * h + i;
            ea[e] = i;
            eb[e] = tmpperm[i];
        }
    }
    rebuild_M();
    for (long long tries = 0; tries < 4000000LL; tries++) {
        if (tries % 2000 == 0 && count_dups() == 0) break;
        int e1 = rnd_int(E);
        if (M[ea[e1] * HM + eb[e1]] <= 1) continue;
        int e2 = rnd_int(E);
        int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
        if (a1 == a2 || b1 == b2) continue;
        if (M[a1 * HM + b2] || M[a2 * HM + b1]) continue;
        setb(e1, b2);
        setb(e2, b1);
    }
    return count_dups() == 0;
}

/* Add one A vertex and one B vertex (order +2), keeping the graph DEG-regular and simple. */
static int grow(void) {
    int h0 = H;
    if (2 * (h0 + 1) > NMAX || h0 + 1 >= HM) return 0;
    int need = DEG - 1;
    int chosen[MAXDEG];
    int nc = 0;
    static int usedA[HM], usedB[HM];
    static int stamp = 0;
    stamp++;
    for (int tries = 0; tries < 100000 && nc < need; tries++) {
        int e = rnd_int(E);
        int a = ea[e], b = eb[e];
        if (usedA[a] == stamp || usedB[b] == stamp) continue;
        usedA[a] = stamp;
        usedB[b] = stamp;
        chosen[nc++] = e;
    }
    if (nc < need) return 0;
    for (int i = 0; i < nc; i++) {
        int e = chosen[i];
        int a = ea[e], b = eb[e];
        /* (a,b) becomes (new A, b); add (a, new B) */
        M[a * HM + b]--;
        ea[e] = h0;
        M[h0 * HM + b]++;
        ea[E + i] = a;
        eb[E + i] = h0;
        M[a * HM + h0]++;
    }
    ea[E + nc] = h0;
    eb[E + nc] = h0;
    M[h0 * HM + h0]++;
    E += nc + 1;
    H = h0 + 1;
    return 1;
}

static void save_best(void) {
    if (2 * H <= bestN) return;
    if (count_dups() != 0) return;
    bestN = 2 * H;
    bestH = H;
    bestE = E;
    memcpy(bestA, ea, sizeof(int) * (size_t)E);
    memcpy(bestB, eb, sizeof(int) * (size_t)E);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int n0 = argc > 5 ? atoi(argv[5]) : 0;
    if (DEG < 2 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    alloc_all();
    uint64_t sm = sd * 2654435761ULL + 99991ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    if (n0 > NMAX - 2) n0 = NMAX - 2;
    int h = n0 / 2;
    if (h < DEG + 1) h = DEG + 1;
    int ok = 0;
    while (h >= DEG && !ok) {
        H = h;
        E = h * DEG;
        ok = random_init();
        if (!ok) h--;
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    long long cost = evalcost();
    int done = 0, fails = 0;

    while (!done && elapsed() < DEADLINE) {
        if (cost == 0) {
            save_best();
            if (!grow()) { done = 1; break; }
            cost = evalcost();
            fails = 0;
            continue;
        }
        double T0c = 2.0 + 0.02 * (double)cost;
        double ratio = 0.3 / T0c;
        long long cbest = cost;
        memcpy(sa, ea, sizeof(int) * (size_t)E);
        memcpy(sb, eb, sizeof(int) * (size_t)E);
        for (int it = 0; it < CYC; it++) {
            if ((it & 15) == 0 && elapsed() > DEADLINE) break;
            double Tt = T0c * pow(ratio, (double)it / CYC);
            int e1 = rnd_int(E), e2 = rnd_int(E);
            if (e1 == e2) continue;
            int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
            if (a1 == a2 || b1 == b2) continue;
            if (M[a1 * HM + b2] || M[a2 * HM + b1]) continue;
            setb(e1, b2);
            setb(e2, b1);
            long long c2 = evalcost();
            long long dl = c2 - cost;
            if (dl <= 0 || rnd_unit() < exp(-(double)dl / Tt)) {
                cost = c2;
                if (cost == 0) break;
                if (cost < cbest) {
                    cbest = cost;
                    memcpy(sa, ea, sizeof(int) * (size_t)E);
                    memcpy(sb, eb, sizeof(int) * (size_t)E);
                }
            } else {
                setb(e1, b1);
                setb(e2, b2);
            }
        }
        if (cost != 0 && cost > cbest) {
            memcpy(ea, sa, sizeof(int) * (size_t)E);
            memcpy(eb, sb, sizeof(int) * (size_t)E);
            rebuild_M();
            cost = cbest;
        }
        if (bestN == 0) {
            if (++fails >= FAILCYC) {
                int nh = (int)(H * 0.93);
                if (nh < DEG + 1) nh = DEG + 1;
                int ok2 = 0;
                while (nh >= DEG && !ok2) {
                    H = nh;
                    E = nh * DEG;
                    ok2 = random_init();
                    if (!ok2) nh--;
                }
                if (!ok2) done = 1;
                else cost = evalcost();
                fails = 0;
            }
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
    } else {
        printf("%d %d\n", bestN, bestE);
        for (int e = 0; e < bestE; e++)
            printf("%d %d\n", bestA[e], bestH + bestB[e]);
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
# Driver: baselines in Python, then the C graph-level annealer that grows a valid graph.
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

    # Already at the Moore bound: nothing larger is possible.
    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    # Give the C search nearly all of the budget.
    remaining = 0.92 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0 and 2 <= d <= 64:
        # Start the growth chain well below the Moore bound; C grows it while valid.
        n0 = 2 * int(0.36 * moore / 2)
        n0 = max(n0, 2 * d + 2)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", n0],
                            timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
