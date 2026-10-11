import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction for the target cases: Cayley-bipartite (bi-Cayley with a
# single base vertex per side) lifts over a group G = Z_m x|_r Z_k2.
#
# Vertices: A_g and B_g for g in G. Each A_g is joined to B_{g*s} for the d
# DISTINCT elements s of a connection set S. Left multiplication is an
# automorphism that is transitive on each side, so the diameter is decided
# by two BFS runs, from A_e and from B_e. The cost is the number of
# unreached (rep, vertex) pairs. Moves replace one element of S by a new
# element. This is a different search space from the multi-vertex voltage
# annealer: no base permutations, no duplicate penalty, and the cost is
# evaluated with a table-driven BFS on 2|G| vertices.
#
# The Python driver climbs the group order G by a ladder: expand while
# successful, then bisect between the last success and the first failure.
# Every success is checked with lib.is_valid, and the best valid graph is
# kept, so the output never gets worse than the exact fallbacks.
#
# Usage: prog d D m k2 r seed slice_seconds
# Prints a graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGCOST (1 << 30)
#define STAG 6000
#define RL 40000

static int DEG, DIAM, G, MM, K2;
static int *POWR, *MT, *INV;
static int *S, *bestS;
static uint32_t *vis;
static uint32_t stamp = 0;
static int *fr, *fr2;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int gmul_formula(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, dd = y % K2;
    long long t = (a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + dd) % K2);
}

/* Unreached (rep, vertex) pairs, reps = A_e (id 0) and B_e (id G). */
static int cost_fn(const int *s) {
    int N = 2 * G;
    int total = 0;
    for (int rep = 0; rep < 2; rep++) {
        int src = (rep == 0) ? 0 : G;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)N);
            stamp = 0;
        }
        stamp++;
        int *cur = fr, *nxt = fr2;
        int fn = 1, reached = 1;
        cur[0] = src;
        vis[src] = stamp;
        for (int lv = 0; lv < DIAM && fn > 0; lv++) {
            int nn = 0;
            for (int q = 0; q < fn; q++) {
                int u = cur[q];
                if (u < G) {
                    const int *row = MT + (size_t)u * G;
                    for (int j = 0; j < DEG; j++) {
                        int v = G + row[s[j]];
                        if (vis[v] != stamp) { vis[v] = stamp; nxt[nn++] = v; }
                    }
                } else {
                    const int *row = MT + (size_t)(u - G) * G;
                    for (int j = 0; j < DEG; j++) {
                        int v = row[INV[s[j]]];
                        if (vis[v] != stamp) { vis[v] = stamp; nxt[nn++] = v; }
                    }
                }
            }
            reached += nn;
            int *t = cur; cur = nxt; nxt = t;
            fn = nn;
        }
        total += N - reached;
    }
    return total;
}

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    MM = atoi(argv[3]);
    K2 = atoi(argv[4]);
    int r = atoi(argv[5]);
    uint64_t seed = strtoull(argv[6], NULL, 10);
    double slice = atof(argv[7]);

    if (DEG < 1 || DIAM < 1 || MM < 1 || K2 < 1) { printf("0 0\n"); return 0; }
    G = MM * K2;
    if (G <= DEG || G > 3000) { printf("0 0\n"); return 0; }
    r = ((r % MM) + MM) % MM;
    if (gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }

    POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    MT = malloc(sizeof(int) * (size_t)G * (size_t)G);
    INV = malloc(sizeof(int) * (size_t)G);
    if (!MT || !INV) { printf("0 0\n"); return 0; }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            MT[(size_t)x * G + y] = gmul_formula(x, y);
    for (int x = 0; x < G; x++) {
        INV[x] = -1;
        for (int y = 0; y < G; y++)
            if (MT[(size_t)x * G + y] == 0) { INV[x] = y; break; }
        if (INV[x] < 0) { printf("0 0\n"); return 0; }
    }

    int N = 2 * G;
    S = malloc(sizeof(int) * DEG);
    bestS = malloc(sizeof(int) * DEG);
    vis = calloc((size_t)N, sizeof(uint32_t));
    fr = malloc(sizeof(int) * (size_t)N);
    fr2 = malloc(sizeof(int) * (size_t)N);
    if (!S || !bestS || !vis || !fr || !fr2) { printf("0 0\n"); return 0; }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x7654321ULL;
    if (rs == 0) rs = 1;

    clock_t t0 = clock();
    int bestCost = BIGCOST;
    int found = 0;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestCost < BIGCOST && rnd01() < 0.5) {
            /* Reheat from the best connection set with 1-2 random replacements. */
            memcpy(S, bestS, sizeof(int) * (size_t)DEG);
            int kick = 1 + rndint(2);
            for (int q = 0; q < kick; q++) {
                int j = rndint(DEG);
                int g;
                for (;;) {
                    g = rndint(G);
                    int ok = 1;
                    for (int k = 0; k < DEG; k++) if (S[k] == g) { ok = 0; break; }
                    if (ok) break;
                }
                S[j] = g;
            }
            T0 = 0.8;
        } else {
            /* Fresh random connection set of DEG distinct elements. */
            for (int j = 0; j < DEG; j++) {
                int g;
                for (;;) {
                    g = rndint(G);
                    int ok = 1;
                    for (int k = 0; k < j; k++) if (S[k] == g) { ok = 0; break; }
                    if (ok) break;
                }
                S[j] = g;
            }
            T0 = 2.0;
        }

        int cur = cost_fn(S);
        if (cur < bestCost) { bestCost = cur; memcpy(bestS, S, sizeof(int) * (size_t)DEG); }
        if (cur == 0) { found = 1; break; }

        int runBest = cur, since = 0;
        for (int it = 0; it < RL; it++) {
            if ((it & 255) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.05;
            int j = rndint(DEG);
            int g = rndint(G);
            int dup = 0;
            for (int k = 0; k < DEG; k++) if (S[k] == g) { dup = 1; break; }
            if (dup) continue;
            int old = S[j];
            S[j] = g;
            int nc = cost_fn(S);
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                S[j] = old;
            }
            if (cur < bestCost) { bestCost = cur; memcpy(bestS, S, sizeof(int) * (size_t)DEG); }
            if (cur == 0) { found = 1; break; }
            if (cur < runBest) { runBest = cur; since = 0; }
            else if (++since > STAG) break;
        }
    }

    if (bestCost == 0) {
        printf("%d %d\n", N, G * DEG);
        for (int g = 0; g < G; g++)
            for (int j = 0; j < DEG; j++)
                printf("%d %d\n", g, G + MT[(size_t)g * G + bestS[j]]);
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact / safe constructions (fallbacks for every case).
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
# Group enumeration: all Z_m x|_r Z_k2 with m * k2 = order.
# ----------------------------------------------------------------------------

def _groups(order):
    """Return a list of (m, k2, r) with m * k2 = order and r^k2 = 1 mod m, gcd(r, m) = 1."""
    out = []
    for k2 in range(1, order + 1):
        if order % k2:
            continue
        m = order // k2
        if m == 1:
            out.append((1, k2, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                out.append((m, k2, r))
    return out


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

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
            return True
        return False

    # Exact constructions.
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

    if time.monotonic() >= deadline - 2.0:
        return best

    def attempt(G_, slice_s):
        """Try to find a bi-Cayley graph with group order G_. Returns 'ok', 'fail' or 'abort'."""
        groups = _groups(G_)
        if not groups:
            return 'fail'
        for _ in range(2):
            rem = deadline - time.monotonic()
            if rem < 2.0:
                return 'fail'
            s = min(slice_s, rem - 1.0)
            m, k2, r = rng.choice(groups)
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, m, k2, r, rng.randrange(1, 10 ** 9), f"{s:.2f}"],
                    timeout=s + 8.0,
                )
            except RuntimeError:
                return 'abort'
            try:
                n, e = lib.parse_graph_text(out)
            except ValueError:
                continue
            if n > 0 and lib.is_valid(n, e, d, D):
                consider(n, e)
                return 'ok'
        return 'fail'

    # Ladder over the group order G: the bi-Cayley graph has 2G vertices.
    G = max(d + 1, min(best[0] // 2, lib.moore_bound(d, D) // (2 * d)))
    lo = None
    hi = None
    while True:
        if lo is None and hi is None:
            cur = G
        elif hi is None:
            cur = lo + max(2, lo // 40)
        else:
            if hi - lo <= 1:
                break
            cur = (lo + hi) // 2
        if cur <= d:
            break
        rem = deadline - time.monotonic()
        if rem < 2.0:
            break
        slice_s = min(max(1.0, 0.15 * budget), rem - 1.0)
        res = attempt(cur, slice_s)
        if res == 'abort':
            break
        if res == 'ok':
            lo = cur
        elif lo is None:
            G = cur // 2
            if G <= d:
                break
        else:
            hi = cur

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
