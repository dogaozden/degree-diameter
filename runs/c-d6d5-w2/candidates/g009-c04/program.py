import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New search family: unstructured bipartite graphs, no group symmetry.
#
# State: a bipartite graph with sides A = {0..S-1} and B = {0..S-1}, every
# vertex of degree DEG (edges stored as parallel arrays ea[], eb[]).
#
# Moves: edge switches. Pick edges (a1,b1), (a2,b2) with a1 != a2, b1 != b2,
# replace them by (a1,b2), (a2,b1). Degrees are preserved and bipartiteness
# is automatic. Cost = number of unordered vertex pairs at distance > DIAM,
# computed exactly with bitset ball expansion.
#
# Growth: when cost reaches 0 the graph is valid. It is saved and grown by
# two vertices (one new A vertex, one new B vertex): pick DEG disjoint edges
# x_i-y_i, reroute them to x_i-b' and a'-y_i. Degrees stay DEG everywhere.
# Annealing then repairs the cost.
#
# Start: the circulant (K_{DEG,DEG} at S = DEG), which is valid for DIAM >= 2.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXS 1200
#define MAXN (2 * MAXS)
#define LEN 30000

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;
static int DEG, DIAM, S, W;
static int *ea, *eb, *nb, *ncnt;
static uint64_t *bufA, *bufB;
static unsigned char adjm[MAXS * MAXS];
static int *bestA, *bestB, bestS = 0;

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

/* Rebuild neighbour lists from the edge arrays. Vertex a in A is a, vertex b in B is S + b. */
static void build_nb(void) {
    int N = 2 * S, E = S * DEG;
    memset(ncnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < E; e++) {
        int a = ea[e], b = S + eb[e];
        nb[(size_t)a * DEG + ncnt[a]++] = b;
        nb[(size_t)b * DEG + ncnt[b]++] = a;
    }
}

/* Number of unordered vertex pairs at distance > DIAM (0 means valid). */
static long long eval_cost(void) {
    int N = 2 * S;
    W = (N + 63) >> 6;
    build_nb();
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++)
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < DEG; k++) {
                const uint64_t *cu = cur + (size_t)nb[(size_t)v * DEG + k] * W;
                for (int w = 0; w < W; w++) o[w] |= cu[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *c = cur + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += __builtin_popcountll(c[w]);
        tot += N - cnt;
    }
    return tot / 2;
}

/* Circulant start: a_i adjacent to b_{(i+k) mod S}, k < DEG. Valid for DIAM >= 2. */
static void init_circulant(void) {
    S = DEG;
    for (int i = 0; i < S; i++) {
        for (int k = 0; k < DEG; k++) {
            int e = i * DEG + k;
            int j = (i + k) % S;
            ea[e] = i;
            eb[e] = j;
            adjm[i * MAXS + j] = 1;
        }
    }
}

/* Add one A vertex and one B vertex, each of degree DEG, by rerouting a matching of DEG edges.
   Returns 0 if no suitable matching was found (state unchanged). */
static int grow(void) {
    int E = S * DEG;
    if (S + 2 >= MAXS) return 0;
    int *perm = malloc(sizeof(int) * (size_t)E);
    int *chosen = malloc(sizeof(int) * (size_t)DEG);
    unsigned char *ua = malloc((size_t)S);
    unsigned char *ub = malloc((size_t)S);
    int ok = 0;
    for (int att = 0; att < 300 && !ok; att++) {
        for (int e = 0; e < E; e++) perm[e] = e;
        for (int i = E - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        memset(ua, 0, (size_t)S);
        memset(ub, 0, (size_t)S);
        int c = 0;
        for (int i = 0; i < E && c < DEG; i++) {
            int e = perm[i];
            if (!ua[ea[e]] && !ub[eb[e]]) {
                ua[ea[e]] = 1;
                ub[eb[e]] = 1;
                chosen[c++] = e;
            }
        }
        if (c == DEG) ok = 1;
    }
    if (ok) {
        int newA = S;  /* new A vertex index and new B vertex index are both S */
        for (int i = 0; i < DEG; i++) {
            int e = chosen[i];
            int x = ea[e], y = eb[e];
            adjm[x * MAXS + y] = 0;
            ea[e] = x;
            eb[e] = newA;               /* x - b' */
            adjm[x * MAXS + newA] = 1;
            int ne = E + i;
            ea[ne] = newA;
            eb[ne] = y;                 /* a' - y */
            adjm[newA * MAXS + y] = 1;
        }
        S = S + 1;
    }
    free(perm);
    free(chosen);
    free(ua);
    free(ub);
    return ok;
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
    if (DEG < 2 || DEG > 64 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    ea = malloc(sizeof(int) * (size_t)MAXS * DEG);
    eb = malloc(sizeof(int) * (size_t)MAXS * DEG);
    nb = malloc(sizeof(int) * (size_t)MAXN * DEG);
    ncnt = malloc(sizeof(int) * (size_t)MAXN);
    bufA = malloc(sizeof(uint64_t) * (size_t)MAXN * (size_t)((MAXN + 63) / 64));
    bufB = malloc(sizeof(uint64_t) * (size_t)MAXN * (size_t)((MAXN + 63) / 64));
    bestA = malloc(sizeof(int) * (size_t)MAXS * DEG);
    bestB = malloc(sizeof(int) * (size_t)MAXS * DEG);

    init_circulant();
    long long cost = eval_cost();
    long long iter = 0;

    while (1) {
        if (cost == 0) {
            int E = S * DEG;
            memcpy(bestA, ea, sizeof(int) * (size_t)E);
            memcpy(bestB, eb, sizeof(int) * (size_t)E);
            bestS = S;
            if (!grow()) break;
            cost = eval_cost();
            continue;
        }
        iter++;
        if ((iter & 255) == 0 && elapsed() > DEADLINE) break;

        int E = S * DEG;
        int e1 = rnd_int(E), e2 = rnd_int(E);
        int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
        if (e1 == e2 || a1 == a2 || b1 == b2) continue;
        if (adjm[a1 * MAXS + b2] || adjm[a2 * MAXS + b1]) continue;

        adjm[a1 * MAXS + b1] = 0;
        adjm[a2 * MAXS + b2] = 0;
        adjm[a1 * MAXS + b2] = 1;
        adjm[a2 * MAXS + b1] = 1;
        eb[e1] = b2;
        eb[e2] = b1;

        long long c2 = eval_cost();
        double frac = (double)(iter % LEN) / (double)LEN;
        double T = 2.0 * pow(0.05, frac);
        if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            adjm[a1 * MAXS + b2] = 0;
            adjm[a2 * MAXS + b1] = 0;
            adjm[a1 * MAXS + b1] = 1;
            adjm[a2 * MAXS + b2] = 1;
            eb[e1] = b1;
            eb[e2] = b2;
        }
    }

    if (bestS > 0) {
        int m = bestS * DEG;
        printf("%d %d\n", 2 * bestS, m);
        for (int e = 0; e < m; e++)
            printf("%d %d\n", bestA[e], bestS + bestB[e]);
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
# Driver: baselines in Python, then the C edge-switch annealer with growth.
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
    if best_n >= lib.moore_bound(d, D):
        return best

    # Unstructured edge-switch annealing with growth, using nearly all the budget.
    remaining = 0.9 * time_limit - (time.monotonic() - start) - 1.5
    if d >= 3 and remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                            timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
