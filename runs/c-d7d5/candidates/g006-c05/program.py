import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: general bi-regular base multigraph with K vertices per side
# and DEG darts per vertex, lifted over an arbitrary finite group given by its
# multiplication table (read from stdin). Element 0 must be the identity.
#
# Dart e joins A_{dA[e]} to B_{dB[e]} with voltage dS[e]:
#   A_{i,g} ~ B_{j, g*s} for all g in G.
# Left multiplication by h is an automorphism of the lift, so one BFS from each
# of the 2K fibre representatives (A_{i,0}, B_{j,0}) decides the diameter.
#
# Unlike a layered-permutation model, moves are: change a voltage, swap the
# B-endpoints of two darts, or swap the A-endpoints of two darts. Each swap
# keeps every base vertex at degree DEG. Cost = unreached (rep, vertex) pairs
# + a duplicate-dart penalty. Simulated annealing with reheating from the best
# state found so far.
#
# Input (stdin): "G*G G*G" then G*G lines "x*G+y  x*y" (the group table).
# Usage: prog DEG DIAM K seed slice_seconds
# Output: a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define BIGCOST (1 << 30)

static int DEG, DIAM, K, G, N, NE;
static int *tbl;
static int *dA, *dB, *dS, *perm, *adj, *cnt, *fr, *nx;
static int *bestA, *bestB, *bestS;
static uint32_t *vis;
static uint32_t stamp = 0;
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

static void set_perm(int e) {
    int s = dS[e];
    int *pm = perm + (size_t)e * G;
    for (int g = 0; g < G; g++) pm[g] = tbl[(size_t)g * G + s];
}

static int cost_fn(void) {
    int dup = 0;
    for (int e1 = 0; e1 < NE; e1++)
        for (int e2 = e1 + 1; e2 < NE; e2++)
            if (dA[e1] == dA[e2] && dB[e1] == dB[e2] && dS[e1] == dS[e2]) dup++;

    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < NE; e++) {
        int ba = dA[e] * G, bb = (K + dB[e]) * G;
        const int *pm = perm + (size_t)e * G;
        for (int g = 0; g < G; g++) {
            int a = ba + g, b = bb + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }

    int total = 0;
    for (int ri = 0; ri < 2 * K; ri++) {
        int src = ri * G;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)N);
            stamp = 0;
        }
        stamp++;
        vis[src] = stamp;
        int *cur = fr, *nxt = nx;
        int fn = 1, reached = 1;
        cur[0] = src;
        for (int lv = 0; lv < DIAM && fn > 0; lv++) {
            int nn = 0;
            for (int q = 0; q < fn; q++) {
                int u = cur[q];
                const int *au = adj + (size_t)u * DEG;
                for (int t = 0; t < DEG; t++) {
                    int v = au[t];
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
        total += N - reached;
    }
    return total + PEN * dup;
}

static void save_best(void) {
    memcpy(bestA, dA, sizeof(int) * (size_t)NE);
    memcpy(bestB, dB, sizeof(int) * (size_t)NE);
    memcpy(bestS, dS, sizeof(int) * (size_t)NE);
}

static void random_lift(void) {
    for (int e = 0; e < NE; e++) dA[e] = e / DEG;
    for (int e = 0; e < NE; e++) dB[e] = e / DEG;
    for (int i = NE - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = dB[i]; dB[i] = dB[j]; dB[j] = t;
    }
    for (int e = 0; e < NE; e++) dS[e] = rndint(G);
    for (int e = 0; e < NE; e++) set_perm(e);
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double slice = atof(argv[5]);

    long long tn = 0, tm = 0;
    if (DEG < 1 || DIAM < 1 || K < 1) { printf("0 0\n"); return 0; }
    if (scanf("%lld %lld", &tn, &tm) != 2) { printf("0 0\n"); return 0; }
    int g0 = (int)llround(sqrt((double)tn));
    if (g0 < 1 || (long long)g0 * g0 != tn || tm != tn) { printf("0 0\n"); return 0; }
    G = g0;
    tbl = malloc(sizeof(int) * (size_t)tn);
    if (!tbl) { printf("0 0\n"); return 0; }
    for (long long q = 0; q < tm; q++) {
        long long u, v;
        if (scanf("%lld %lld", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || u >= tn || v < 0 || v >= G) { printf("0 0\n"); return 0; }
        tbl[u] = (int)v;
    }
    /* Element 0 must be the identity (needed for vertex-transitivity). */
    for (int y = 0; y < G; y++)
        if (tbl[y] != y) { printf("0 0\n"); return 0; }

    NE = DEG * K;
    N = 2 * K * G;
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    dA = malloc(sizeof(int) * NE);
    dB = malloc(sizeof(int) * NE);
    dS = malloc(sizeof(int) * NE);
    bestA = malloc(sizeof(int) * NE);
    bestB = malloc(sizeof(int) * NE);
    bestS = malloc(sizeof(int) * NE);
    perm = malloc(sizeof(int) * (size_t)NE * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * N);
    fr = malloc(sizeof(int) * N);
    nx = malloc(sizeof(int) * N);
    vis = calloc(N, sizeof(uint32_t));
    if (!dA || !dB || !dS || !bestA || !bestB || !bestS || !perm || !adj ||
        !cnt || !fr || !nx || !vis) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    int found = 0;
    int bestCost = BIGCOST;
    const int RL = 60000;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestCost >= BIGCOST || rnd01() < 0.25) {
            random_lift();
            T0 = 2.0;
        } else {
            memcpy(dA, bestA, sizeof(int) * (size_t)NE);
            memcpy(dB, bestB, sizeof(int) * (size_t)NE);
            memcpy(dS, bestS, sizeof(int) * (size_t)NE);
            int kick = NE / 8 + 1;
            for (int q = 0; q < kick; q++) {
                if (rnd01() < 0.5) {
                    dS[rndint(NE)] = rndint(G);
                } else {
                    int e1 = rndint(NE), e2 = rndint(NE);
                    int t = dB[e1]; dB[e1] = dB[e2]; dB[e2] = t;
                }
            }
            for (int e = 0; e < NE; e++) set_perm(e);
            T0 = 0.8;
        }
        int cur = cost_fn();
        if (cur < bestCost) { bestCost = cur; save_best(); }
        if (cur == 0) { found = 1; break; }

        for (int it = 0; it < RL; it++) {
            if ((it & 255) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.05;
            double u = rnd01();
            if (u < 0.2) {
                /* voltage change */
                int e = rndint(NE);
                int old = dS[e];
                int ns = rndint(G);
                if (ns == old) continue;
                dS[e] = ns;
                set_perm(e);
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    dS[e] = old;
                    set_perm(e);
                }
            } else {
                /* endpoint swap on the B side (u < 0.6) or the A side */
                int *arr = (u < 0.6) ? dB : dA;
                int e1 = rndint(NE), e2 = rndint(NE);
                if (e1 == e2 || arr[e1] == arr[e2]) continue;
                int t = arr[e1]; arr[e1] = arr[e2]; arr[e2] = t;
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    t = arr[e1]; arr[e1] = arr[e2]; arr[e2] = t;
                }
            }
            if (cur < bestCost) { bestCost = cur; save_best(); }
            if (cur == 0) { found = 1; break; }
        }
    }

    if (found) {
        printf("%d %d\n", N, NE * G);
        for (int e = 0; e < NE; e++) {
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", dA[e] * G + g, (K + dB[e]) * G + perm[(size_t)e * G + g]);
            }
        }
    } else {
        printf("0 0\n");
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
# Group choice and group tables (passed to C through stdin).
# ----------------------------------------------------------------------------

_TABLE_CACHE = {}


def _table(m, k, r):
    """Multiplication table of Z_m x|_r Z_k as (order, pairs); pair (x*order+y, x*y)."""
    key = (m, k, r)
    if key not in _TABLE_CACHE:
        if len(_TABLE_CACHE) > 3:
            _TABLE_CACHE.clear()
        order, mul, _ = lib.semidirect_group(m, k, r)
        pairs = [(x * order + y, mul(x, y)) for x in range(order) for y in range(order)]
        _TABLE_CACHE[key] = (order, pairs)
    return _TABLE_CACHE[key]


def _pick_group(G, rng):
    """Return (m, k, r) with m * k == G. Small k are favoured; r = 1 is the direct product."""
    divs = [k for k in range(1, min(G, 48) + 1) if G % k == 0 and G // k >= 2]
    k = rng.choice(divs)
    m = G // k
    r = 1
    if k > 1 and rng.random() < 0.7:
        cands = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k, m) == 1 % m]
        if cands:
            r = rng.choice(cands)
    return m, k, r


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
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

    # Main search: general bi-regular base over a group given by its table.
    # Each attempt targets a total group order G with 2*K*G > current best.
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 3.0:
            break
        K = rng.choice([1, 1, 2, 2, 3])
        while best[0] // (2 * K) > 900 and K < 8:
            K += 1
        base = best[0] // (2 * K)
        G = max(2, base + 1 + rng.randrange(0, base // 12 + 2))
        if G > 1000:
            break
        m, k, r = _pick_group(G, rng)
        Gt, pairs = _table(m, k, r)

        remaining = deadline - time.monotonic()
        slice_s = min(remaining - 1.5, 12.0)
        if slice_s < 1.0:
            break
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, K, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                stdin_graph=(Gt * Gt, pairs),
                timeout=slice_s + 10.0,
            )
        except RuntimeError:
            break
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
