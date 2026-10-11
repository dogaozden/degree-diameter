import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction family: Haar-type bi-Cayley graphs with a SET-valued
# connection set.
#
# Group G = Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b; r = 1 gives the
# direct product). For a d-subset S of G (distinct elements, identity allowed)
# the graph H(G, S) has vertices A_g and B_h (g, h in G) and edges
# A_g ~ B_{g*s} for s in S. Every vertex has degree exactly d and the graph is
# simple and bipartite. Left multiplication is an automorphism, so the
# diameter is decided by BFS from A_e and B_e only.
#
# Search: simulated annealing over the set S (replace one element by a
# non-member). Cost = number of (rep, vertex) pairs at distance > D.
# Group orders are targeted at G > best_n / 2, so every success is a strict
# improvement of the order 2G.
#
# Usage: prog d D m k2 r seed slice_seconds
# Prints a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000

static int DEG, DIAM, MM, K2, RR, G, NV;
static int POWR[128];
static int *S, *Sinv, *bestS, *inS, *mulS, *mulI, *fr, *nx;
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

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, d2 = y % K2;
    long long t = (a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + d2) % K2);
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long long t = ((long long)(MM - a % MM) % MM) * POWR[nb] % MM;
    return (int)(t * K2 + nb);
}

/* mulS[x*DEG+k] = x*S[k];  mulI[x*DEG+k] = x*S[k]^{-1}. */
static void update_col(int k) {
    for (int x = 0; x < G; x++) {
        mulS[(size_t)x * DEG + k] = gmul(x, S[k]);
        mulI[(size_t)x * DEG + k] = gmul(x, Sinv[k]);
    }
}

/* Vertices: A_g = g, B_h = G + h. Returns total unreached (rep, vertex) pairs. */
static int cost(void) {
    int total = 0;
    for (int side = 0; side < 2; side++) {
        int src = side ? G : 0;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)NV);
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
                if (u < G) {
                    const int *row = mulS + (size_t)u * DEG;
                    for (int k = 0; k < DEG; k++) {
                        int v = G + row[k];
                        if (vis[v] != stamp) { vis[v] = stamp; nxt[nn++] = v; }
                    }
                } else {
                    const int *row = mulI + (size_t)(u - G) * DEG;
                    for (int k = 0; k < DEG; k++) {
                        int v = row[k];
                        if (vis[v] != stamp) { vis[v] = stamp; nxt[nn++] = v; }
                    }
                }
            }
            reached += nn;
            int *tmp = cur; cur = nxt; nxt = tmp;
            fn = nn;
        }
        total += NV - reached;
    }
    return total;
}

int main(int argc, char **argv) {
    if (argc < 8) {
        fprintf(stderr, "usage: prog d D m k2 r seed slice\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    MM = atoi(argv[3]);
    K2 = atoi(argv[4]);
    RR = atoi(argv[5]);
    uint64_t seed = strtoull(argv[6], NULL, 10);
    double slice = atof(argv[7]);

    if (DEG < 1 || DIAM < 1 || MM < 2 || K2 < 1 || K2 > 120 || RR < 1) {
        printf("0 0\n");
        return 0;
    }
    if (gcd_int(RR, MM) != 1) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * RR % MM);
    if ((long long)POWR[K2 - 1] * RR % MM != 1 % MM) { printf("0 0\n"); return 0; }

    G = MM * K2;
    NV = 2 * G;
    if (G <= DEG) { printf("0 0\n"); return 0; }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    S = malloc(sizeof(int) * DEG);
    Sinv = malloc(sizeof(int) * DEG);
    bestS = malloc(sizeof(int) * DEG);
    inS = calloc((size_t)G, sizeof(int));
    mulS = malloc(sizeof(int) * (size_t)G * DEG);
    mulI = malloc(sizeof(int) * (size_t)G * DEG);
    vis = calloc((size_t)NV, sizeof(uint32_t));
    fr = malloc(sizeof(int) * NV);
    nx = malloc(sizeof(int) * NV);
    if (!S || !Sinv || !bestS || !inS || !mulS || !mulI || !vis || !fr || !nx) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    int found = 0;
    int bestCost = BIGC;
    const int RL = 40000;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestCost >= BIGC || rnd01() < 0.2) {
            /* Fresh random d-subset of G. */
            memset(inS, 0, sizeof(int) * (size_t)G);
            for (int k = 0; k < DEG; k++) {
                int v;
                do { v = rndint(G); } while (inS[v]);
                S[k] = v;
                inS[v] = 1;
            }
            T0 = 2.0;
        } else {
            /* Reheat from the best subset found so far, with a small kick. */
            memcpy(S, bestS, sizeof(int) * DEG);
            memset(inS, 0, sizeof(int) * (size_t)G);
            for (int k = 0; k < DEG; k++) inS[S[k]] = 1;
            int kick = 1 + rndint(2);
            for (int q = 0; q < kick; q++) {
                int k = rndint(DEG);
                int v;
                do { v = rndint(G); } while (inS[v]);
                inS[S[k]] = 0;
                S[k] = v;
                inS[v] = 1;
            }
            T0 = 0.8;
        }
        for (int k = 0; k < DEG; k++) {
            Sinv[k] = ginv(S[k]);
            update_col(k);
        }
        int cur = cost();
        if (cur < bestCost) { bestCost = cur; memcpy(bestS, S, sizeof(int) * DEG); }
        if (cur == 0) { found = 1; break; }

        for (int it = 0; it < RL; it++) {
            if ((it & 127) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.05;
            int k = rndint(DEG);
            int v = rndint(G);
            if (inS[v]) continue;
            int old = S[k];
            S[k] = v;
            inS[old] = 0;
            inS[v] = 1;
            Sinv[k] = ginv(v);
            update_col(k);
            int nc = cost();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
                if (cur < bestCost) { bestCost = cur; memcpy(bestS, S, sizeof(int) * DEG); }
                if (cur == 0) { found = 1; break; }
            } else {
                S[k] = old;
                inS[v] = 0;
                inS[old] = 1;
                Sinv[k] = ginv(old);
                update_col(k);
            }
        }
    }

    if (found) {
        printf("%d %d\n", NV, G * DEG);
        for (int g = 0; g < G; g++) {
            for (int k = 0; k < DEG; k++) {
                printf("%d %d\n", g, G + mulS[(size_t)g * DEG + k]);
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
# Group candidates and the search driver.
# ----------------------------------------------------------------------------

def _group_candidates(order):
    """All (m, k2, r) with m * k2 == order describing Z_m x|_r Z_k2 (r = 1 is the direct product)."""
    out = []
    for k2 in (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21, 24, 27, 28, 30, 36):
        if order % k2:
            continue
        m = order // k2
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                out.append((m, k2, r))
    return out


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

        # Araujo-Pardo & Lopez record for D = 3, d = q + 2 with q a prime power.
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

    # Main search: anneal the connection set of a Haar-type bi-Cayley graph
    # over a group of order G, giving 2G vertices. Target G > best_n / 2.
    failures = 0
    while failures < 3:
        remaining = deadline - time.monotonic()
        if remaining < 1.5:
            break
        slice_s = min(remaining - 0.5, 8.0)
        lo = best[0] // 2 + 1
        g = lo + rng.choice([0, 0, 1, 2, 3])
        cands = []
        for _ in range(300):
            cands = _group_candidates(g)
            if cands:
                break
            g += 1
        if not cands:
            break
        m, k2, r = rng.choice(cands)
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                timeout=slice_s + 10.0,
            )
        except RuntimeError:
            failures += 1
            continue
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
