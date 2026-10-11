import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: K = 1 bi-Cayley lifts over the semidirect product
# Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b).
#
# Graph: vertices A_g = g and B_h = G + h (G = m*k2). Connection set
# S = {s_0, ..., s_{DEG-1}} of distinct group elements, with s_0 = identity
# (WLOG, by relabelling B). Edges A_g ~ B_{g*s} for all g and all s in S.
# This is DEG-regular, bipartite, and simple.
#
# Left multiplication is an automorphism, so the diameter is decided by BFS
# from A_0 and B_0 alone. The search is simulated annealing over the
# non-identity elements of S (replace one element by a fresh one), with
# reheats from the best state and occasional fresh restarts.
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

#define BIGCOST (1 << 30)
#define MAXDEG 64

static int DEG, DIAM, MM, K2, G, N;
static int POWR[64];
static int *mt, *inv_el, *vst, *qb;
static int S[MAXDEG], bestS[MAXDEG];
static int stampv = 0;
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

/* Number of vertices within DIAM of src (BFS on the bi-Cayley graph). */
static int reach_count(int src) {
    stampv++;
    if (stampv == 0x7fffffff) {
        memset(vst, 0, sizeof(int) * (size_t)N);
        stampv = 1;
    }
    int head = 0, tail = 0;
    qb[tail++] = src;
    vst[src] = stampv;
    for (int lv = 0; lv < DIAM && head < tail; lv++) {
        int end = tail;
        while (head < end) {
            int u = qb[head++];
            if (u < G) {
                const int *row = mt + (size_t)u * G;
                for (int j = 0; j < DEG; j++) {
                    int v = G + row[S[j]];
                    if (vst[v] != stampv) { vst[v] = stampv; qb[tail++] = v; }
                }
            } else {
                int h = u - G;
                const int *row = mt + (size_t)h * G;
                for (int j = 0; j < DEG; j++) {
                    int v = row[inv_el[S[j]]];
                    if (vst[v] != stampv) { vst[v] = stampv; qb[tail++] = v; }
                }
            }
        }
    }
    return tail;
}

static int cost_fn(void) {
    int a = reach_count(0);
    int b = reach_count(G);
    return (N - a) + (N - b);
}

static int in_set(int x, int k) {
    for (int i = 0; i < k; i++) if (S[i] == x) return 1;
    return 0;
}

static void random_init(void) {
    S[0] = 0;
    for (int i = 1; i < DEG; i++) {
        int x;
        do { x = rndint(G); } while (in_set(x, i));
        S[i] = x;
    }
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

    if (DEG < 2 || DEG > MAXDEG || DIAM < 1 || MM < 2 || K2 < 1 || K2 > 60 || r < 1) {
        printf("0 0\n");
        return 0;
    }
    G = MM * K2;
    if (DEG >= G || (long long)G * G > 16000000LL) {
        printf("0 0\n");
        return 0;
    }
    if (gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    N = 2 * G;
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    mt = malloc(sizeof(int) * (size_t)G * G);
    inv_el = malloc(sizeof(int) * G);
    vst = calloc(N, sizeof(int));
    qb = malloc(sizeof(int) * N);
    if (!mt || !inv_el || !vst || !qb) { printf("0 0\n"); return 0; }

    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            mt[(size_t)x * G + y] = gmul(x, y);
    for (int x = 0; x < G; x++) {
        inv_el[x] = 0;
        for (int y = 0; y < G; y++) {
            if (mt[(size_t)x * G + y] == 0) { inv_el[x] = y; break; }
        }
    }

    clock_t t0 = clock();
    int bestCost = BIGCOST;
    int found = 0;
    const int RL = 40000;

    while (!found && elapsed(t0) < slice) {
        double T0;
        int fresh = (bestCost >= BIGCOST) || rnd01() < 0.3;
        if (fresh) {
            random_init();
            T0 = 1.5;
        } else {
            memcpy(S, bestS, sizeof(int) * (size_t)DEG);
            int kick = 1 + rndint(2);
            for (int q = 0; q < kick; q++) {
                int i = 1 + rndint(DEG - 1);
                int x;
                do { x = rndint(G); } while (in_set(x, DEG));
                S[i] = x;
            }
            T0 = 0.6;
        }
        int cur = cost_fn();
        if (cur < bestCost) { bestCost = cur; memcpy(bestS, S, sizeof(int) * (size_t)DEG); }
        if (cur == 0) { found = 1; break; }

        for (int it = 0; it < RL; it++) {
            if ((it & 255) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.02;
            int i = 1 + rndint(DEG - 1);
            int x;
            do { x = rndint(G); } while (in_set(x, DEG));
            int old = S[i];
            S[i] = x;
            int nc = cost_fn();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                S[i] = old;
            }
            if (cur < bestCost) { bestCost = cur; memcpy(bestS, S, sizeof(int) * (size_t)DEG); }
            if (cur == 0) { found = 1; break; }
        }
    }

    if (found) {
        printf("%d %d\n", N, G * DEG);
        for (int g = 0; g < G; g++) {
            for (int j = 0; j < DEG; j++) {
                printf("%d %d\n", g, G + mt[(size_t)g * G + bestS[j]]);
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
# Spare-degree extension (no-op for regular graphs).
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
# Group candidates: Z_m x|_r Z_k2 with order m*k2 in [lo, hi].
# ----------------------------------------------------------------------------

def _group_candidates(lo, hi):
    """Return (m, k2, r) triples with lo <= m*k2 <= hi and r^k2 = 1 mod m, gcd(r, m) = 1."""
    out = []
    for k2 in range(1, 41):
        for order in range(max(lo, 4), hi + 1):
            if order % k2:
                continue
            m = order // k2
            if m < 2:
                continue
            if k2 == 1:
                out.append((m, 1, 1))
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
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    search_deadline = start + 0.9 * budget
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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Ladder search: for each group order just above the current half-order,
    # anneal a K = 1 bi-Cayley connection set. Each success raises the bar.
    if d >= 3 and D >= 3:
        fails = 0
        while fails < 4:
            remaining = search_deadline - time.monotonic()
            if remaining < 1.0:
                break
            slice_s = min(remaining, 12.0)
            cur_G = best[0] // 2
            lo = cur_G + 1 + rng.randrange(0, 3 + cur_G // 50)
            cands = _group_candidates(lo, lo + 6)
            if not cands:
                continue
            m, k2, r = rng.choice(cands)
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                    timeout=slice_s + 15.0,
                )
            except RuntimeError:
                fails += 1
                continue
            try:
                n, e = lib.parse_graph_text(out)
            except ValueError:
                continue
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Spare-degree extension with the remaining time (no-op for regular graphs).
    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, deadline)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
