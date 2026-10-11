import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction: Haar graphs over groups (K = 1 bi-Cayley lifts).
#
# Group G of order n = m * k2 (element (a, b) coded as a*k2 + b, product
# (a, b)(c, d) = (a + r^b c, b + d)). Connection set S with |S| = d.
# Vertices A_x = x and B_y = n + y. Edge A_x ~ B_{x s} for s in S.
#
# Left multiplication by g is an automorphism (A_x -> A_gx, B_y -> B_gy), so
# the graph is vertex-transitive on each side. Hence diameter <= D holds iff
# the BFS balls of radius D around A_e and B_e cover everything. Only two BFS
# runs per evaluation, which is very fast, so the C engine can test many
# connection sets and many groups quickly.
#
# Search: simulated annealing over the elements of S (replace one element by
# a fresh group element), cost = unreached vertices from the two roots.
# Restarts perturb the best set found so far.
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

#define MAXG 2000
#define BIGCOST (1 << 30)

static int DEG, DIAM, MM, K2, G, N;
static int POWR[MAXG + 1];
static int *mt;
static int *invt;
static int S[64], Sinv[64], bestS[64];
static uint32_t *vis;
static uint32_t stamp = 0;
static int *fr, *nx;
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
    int a = x / K2, b = x % K2, c = y / K2, dd = y % K2;
    long long t = (a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + dd) % K2);
}

static void build_tables(void) {
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            mt[(size_t)x * G + y] = gmul(x, y);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (mt[(size_t)x * G + y] == 0) { invt[x] = y; break; }
}

/* Number of vertices not reached within DIAM steps from root. */
static int bfs_unreached(int root) {
    stamp++;
    if (stamp == 0) {
        memset(vis, 0, sizeof(uint32_t) * (size_t)N);
        stamp = 1;
    }
    int *cur = fr, *nxt = nx;
    int fn = 1, reached = 1;
    cur[0] = root;
    vis[root] = stamp;
    for (int lv = 0; lv < DIAM && fn > 0; lv++) {
        int nn = 0;
        for (int q = 0; q < fn; q++) {
            int u = cur[q];
            if (u < G) {
                const int *row = mt + (size_t)u * G;
                for (int s = 0; s < DEG; s++) {
                    int v = G + row[S[s]];
                    if (vis[v] != stamp) { vis[v] = stamp; nxt[nn++] = v; }
                }
            } else {
                const int *row = mt + (size_t)(u - G) * G;
                for (int s = 0; s < DEG; s++) {
                    int v = row[Sinv[s]];
                    if (vis[v] != stamp) { vis[v] = stamp; nxt[nn++] = v; }
                }
            }
        }
        reached += nn;
        int *tmp = cur; cur = nxt; nxt = tmp;
        fn = nn;
    }
    return N - reached;
}

static int cost_fn(void) {
    return bfs_unreached(0) + bfs_unreached(G);
}

static int in_set(int g, int upto) {
    for (int t = 0; t < upto; t++) if (S[t] == g) return 1;
    return 0;
}

static void random_set(void) {
    for (int s = 0; s < DEG; s++) {
        int g;
        do { g = rndint(G); } while (in_set(g, s));
        S[s] = g;
    }
    for (int s = 0; s < DEG; s++) Sinv[s] = invt[S[s]];
}

static void load_best(void) {
    memcpy(S, bestS, sizeof(int) * (size_t)DEG);
    for (int s = 0; s < DEG; s++) Sinv[s] = invt[S[s]];
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
    int r = atoi(argv[5]);
    uint64_t seed = strtoull(argv[6], NULL, 10);
    double slice = atof(argv[7]);

    if (DEG < 1 || DEG > 64 || DIAM < 1 || MM < 1 || K2 < 1) {
        printf("0 0\n");
        return 0;
    }
    G = MM * K2;
    if (G > MAXG || G < DEG) {
        printf("0 0\n");
        return 0;
    }
    N = 2 * G;

    r %= MM;
    if (r < 0) r += MM;
    if (gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    mt = malloc(sizeof(int) * (size_t)G * G);
    invt = malloc(sizeof(int) * G);
    vis = calloc(N, sizeof(uint32_t));
    fr = malloc(sizeof(int) * N);
    nx = malloc(sizeof(int) * N);
    if (!mt || !invt || !vis || !fr || !nx) {
        printf("0 0\n");
        return 0;
    }
    build_tables();

    clock_t t0 = clock();
    int found = 0;
    int bestCost = BIGCOST;
    int restarts = 0;
    const int RL = 30000;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (restarts == 0 || bestCost >= BIGCOST || rnd01() < 0.4) {
            random_set();
            T0 = 1.2;
        } else {
            load_best();
            int pos = rndint(DEG);
            int g;
            do { g = rndint(G); } while (in_set(g, DEG));
            S[pos] = g;
            Sinv[pos] = invt[g];
            T0 = 0.6;
        }
        restarts++;

        int cur = cost_fn();
        if (cur < bestCost) {
            bestCost = cur;
            memcpy(bestS, S, sizeof(int) * (size_t)DEG);
        }
        if (cur == 0) { found = 1; break; }

        for (int it = 0; it < RL; it++) {
            if ((it & 127) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.02;
            int i = rndint(DEG);
            int g = rndint(G);
            if (in_set(g, DEG)) continue;
            int old = S[i], oldinv = Sinv[i];
            S[i] = g;
            Sinv[i] = invt[g];
            int nc = cost_fn();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
                if (cur < bestCost) {
                    bestCost = cur;
                    memcpy(bestS, S, sizeof(int) * (size_t)DEG);
                }
                if (cur == 0) { found = 1; break; }
            } else {
                S[i] = old;
                Sinv[i] = oldinv;
            }
        }
    }

    if (found) {
        printf("%d %d\n", N, DEG * G);
        for (int x = 0; x < G; x++)
            for (int s = 0; s < DEG; s++)
                printf("%d %d\n", x, G + mt[(size_t)x * G + S[s]]);
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions (safe fallbacks).
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
# Group choice for the Haar search.
# ----------------------------------------------------------------------------

def _group_choice(n, rng):
    """Return (m, k2, r) with Z_m x|_r Z_k2 of order n = m * k2 (r = 1 is the direct product)."""
    divs = [k for k in range(1, n + 1) if n % k == 0]
    k2 = rng.choice(divs)
    m = n // k2
    r = 1
    if k2 > 1 and m > 2 and rng.random() < 0.7:
        cands = [c for c in range(2, m)
                 if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
        if cands:
            r = rng.choice(cands)
    return m, k2, r


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

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
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

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Haar-graph search: adaptive ladder over the group order n.
    # Success at n gives a valid graph on 2n vertices; then the ladder moves up.
    if D >= 2:
        moore_half = max(2, lib.moore_bound(d, D) // 2)
        lo = max(d, best[0] // 2 + 1)
        cap = min(moore_half, max(lo + 2, int(lo * 1.6) + 4))
        while True:
            remaining = deadline - time.monotonic()
            if remaining < 1.5 or lo > moore_half:
                break
            span = max(1, cap - lo)
            n = lo + min(span - 1, int((rng.random() ** 2) * span))
            m, k2, r = _group_choice(n, rng)
            slice_s = min(remaining - 0.5, 3.0)
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                    timeout=slice_s + 10.0,
                )
            except RuntimeError:
                break
            try:
                gn, ge = lib.parse_graph_text(out)
            except ValueError:
                gn, ge = 0, []
            if gn == 2 * n and ge:
                consider(gn, ge)
                lo = n + 1
                cap = max(cap, min(moore_half, lo + lo // 10 + 2))
            else:
                cap = max(lo + 2, lo + int((cap - lo) * 0.85))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
