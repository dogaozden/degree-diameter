import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: bi-Cayley lifts with ONE vertex per side over a group G of
# order m*k2 (semidirect Z_m x|_r Z_k2, element (a, b) coded as a*k2 + b).
#
# Graph: vertices A_g and B_g for g in G. Connection set S = {s_1..s_DEG}
# (distinct group elements). Edges A_g ~ B_{g s} for all g and s in S.
# Left multiplication is an automorphism, so the diameter is exact once every
# vertex is reached within DIAM steps from A_0 and from B_0.
#
# Cost = number of vertices NOT reached within DIAM steps from A_0 plus from
# B_0. Zero iff the graph is valid. Simulated annealing over S: a move swaps
# one connection element for a fresh one (degree and simplicity are preserved).
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

#define GMAX 3000

static int DEG, DIAM, MM, K2, RR, G;
static int *POWR, *MUL, *INV;
static int *S, *adj, *vis, *fr, *nx, *inS;
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int gmul_raw(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, dd = y % K2;
    long long t = ((long long)a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + dd) % K2);
}

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

/* Number of vertices reached from src within DIAM steps (src included). */
static int reach_from(int src) {
    int *cur = fr, *nxt = nx;
    stamp++;
    if (stamp == 0x7fffffff) {
        memset(vis, 0, sizeof(int) * (size_t)(2 * G));
        stamp = 1;
    }
    vis[src] = stamp;
    cur[0] = src;
    int fn = 1, reached = 1;
    for (int lv = 0; lv < DIAM && fn > 0; lv++) {
        int nn = 0;
        for (int q = 0; q < fn; q++) {
            const int *au = adj + (size_t)cur[q] * DEG;
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
    return reached;
}

static int cost_of(const int *Sx) {
    for (int g = 0; g < G; g++) {
        int *ag = adj + (size_t)g * DEG;
        int *bg = adj + (size_t)(G + g) * DEG;
        for (int t = 0; t < DEG; t++) {
            int s = Sx[t];
            ag[t] = G + MUL[(size_t)g * G + s];
            bg[t] = MUL[(size_t)g * G + INV[s]];
        }
    }
    int r0 = reach_from(0);
    int r1 = reach_from(G);
    return (2 * G - r0) + (2 * G - r1);
}

int main(int argc, char **argv) {
    if (argc < 8) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    MM = atoi(argv[3]);
    K2 = atoi(argv[4]);
    RR = atoi(argv[5]);
    uint64_t seed = strtoull(argv[6], NULL, 10);
    double slice = atof(argv[7]);

    if (DEG < 1 || DIAM < 1 || MM < 1 || K2 < 1 || MM > GMAX || K2 > GMAX) {
        printf("0 0\n");
        return 0;
    }
    G = MM * K2;
    if (G > GMAX || G < DEG + 1) { printf("0 0\n"); return 0; }
    if (RR < 1 || gcd_int(RR, MM) != 1) { printf("0 0\n"); return 0; }

    POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++)
        POWR[b] = (int)((long long)POWR[b - 1] * RR % MM);
    if (((long long)POWR[K2 - 1] * RR) % MM != 1 % MM) {
        printf("0 0\n");
        return 0;
    }

    MUL = malloc(sizeof(int) * (size_t)G * G);
    INV = malloc(sizeof(int) * (size_t)G);
    S = malloc(sizeof(int) * (size_t)DEG);
    adj = malloc(sizeof(int) * (size_t)2 * G * DEG);
    vis = calloc((size_t)2 * G, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)2 * G);
    nx = malloc(sizeof(int) * (size_t)2 * G);
    inS = calloc((size_t)G, sizeof(int));
    if (!MUL || !INV || !S || !adj || !vis || !fr || !nx || !inS) {
        printf("0 0\n");
        return 0;
    }

    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            MUL[(size_t)x * G + y] = gmul_raw(x, y);
    for (int x = 0; x < G; x++) {
        INV[x] = -1;
        for (int y = 0; y < G; y++)
            if (MUL[(size_t)x * G + y] == 0) { INV[x] = y; break; }
        if (INV[x] < 0) { printf("0 0\n"); return 0; }
    }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    clock_t t0 = clock();
    int found = 0;
    const int RL = 30000;
    int *bestS = malloc(sizeof(int) * (size_t)DEG);

    while (!found && elapsed(t0) < slice) {
        memset(inS, 0, sizeof(int) * (size_t)G);
        for (int t = 0; t < DEG; t++) {
            int x;
            do { x = rndint(G); } while (inS[x]);
            inS[x] = 1;
            S[t] = x;
        }
        int cur = cost_of(S);
        int bestRun = cur;
        if (cur == 0) { found = 1; break; }
        memcpy(bestS, S, sizeof(int) * (size_t)DEG);
        const double T0 = 2.0;

        for (int it = 0; it < RL; it++) {
            if ((it & 255) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.05;
            int t = rndint(DEG);
            int old = S[t];
            int x;
            do { x = rndint(G); } while (inS[x]);
            S[t] = x;
            int nc = cost_of(S);
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                inS[old] = 0;
                inS[x] = 1;
                cur = nc;
                if (cur < bestRun) {
                    bestRun = cur;
                    memcpy(bestS, S, sizeof(int) * (size_t)DEG);
                }
                if (cur == 0) { found = 1; break; }
            } else {
                S[t] = old;
            }
        }
    }

    if (found) {
        memcpy(S, bestS, sizeof(int) * (size_t)DEG);
        printf("%d %d\n", 2 * G, G * DEG);
        for (int g = 0; g < G; g++) {
            for (int t = 0; t < DEG; t++) {
                printf("%d %d\n", g, G + MUL[(size_t)g * G + S[t]]);
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
# Exact / safe constructions (valid fallbacks).
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
# Greedy spare-degree extension (no-op for regular graphs).
# ----------------------------------------------------------------------------

def _two_colour(n, edges):
    """Return a 0/1 side label per vertex (bipartition), or None if not bipartite."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
                elif col[v] == col[u]:
                    return None
    return col


def _extend_spare(n, edges, d, D, deadline):
    """Greedily add fresh vertex pairs while the graph stays valid. Returns (n, edges)."""
    if d < 2:
        return n, edges
    col = _two_colour(n, edges)
    if col is None:
        return n, edges
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    edges = list(edges)
    while time.monotonic() < deadline:
        A_sp = [v for v in range(n) if col[v] == 0 and deg[v] < d]
        B_sp = [v for v in range(n) if col[v] == 1 and deg[v] < d]
        if not A_sp or not B_sp:
            break
        grown = False
        for k in range(d - 1, 0, -1):
            if k > len(A_sp) or k > len(B_sp):
                continue
            a, b = n, n + 1
            cand_new = [(a, b)] + [(a, x) for x in B_sp[:k]] + [(b, y) for y in A_sp[:k]]
            cand = edges + cand_new
            if lib.is_valid(n + 2, cand, d, D):
                edges = cand
                n += 2
                col += [0, 1]
                deg += [0, 0]
                deg[a] = k + 1
                deg[b] = k + 1
                for x in B_sp[:k]:
                    deg[x] += 1
                for y in A_sp[:k]:
                    deg[y] += 1
                grown = True
                break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Group sampling and driver.
# ----------------------------------------------------------------------------

K2_CHOICES = [1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21, 24,
              27, 28, 30, 36, 40, 42, 48, 49, 54, 56, 63, 72, 81]


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x|_r Z_k2 with order m*k2 >= target, or None."""
    for _ in range(300):
        k2 = rng.choice(K2_CHOICES)
        m0 = max(2, -(-target // k2))
        m = m0 + rng.randrange(0, 3)
        twists = [c for c in range(1, m)
                  if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
        if not twists:
            continue
        nontrivial = [c for c in twists if c != 1]
        if nontrivial and rng.random() < 0.7:
            r = rng.choice(nontrivial)
        else:
            r = 1
        return m, k2, r
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = start + budget
    search_deadline = start + 0.92 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is larger and valid."""
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

    # Main search: single-orbit bi-Cayley lifts searched by annealing over the
    # connection set, across many groups near the target order.
    step = 0.15
    while True:
        remaining = search_deadline - time.monotonic()
        if remaining < 1.5:
            break
        slice_s = min(remaining, 8.0)
        want = best[0] * (1.0 + step)
        target = max(d + 1, math.ceil(want / 2))
        if target > 1500:
            break
        grp = _sample_group(target, rng)
        if grp is None:
            step = max(0.005, step * 0.7)
            continue
        m, k2, r = grp
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                timeout=slice_s + 10.0,
            )
        except RuntimeError:
            break
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            step = max(0.005, step * 0.8)
            continue
        if consider(n, e):
            step = min(0.3, step * 1.3)
        else:
            step = max(0.005, step * 0.8)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Spare-degree extension with the remaining time.
    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, deadline)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
