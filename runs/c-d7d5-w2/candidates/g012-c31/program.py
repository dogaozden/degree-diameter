import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy (bold change): single-orbit bi-Cayley graphs over non-abelian groups.
#
# Instead of annealing voltages of a multi-vertex lift, this engine fixes ONE
# orbit per side: A_g ~ B_{g*s} for every g in G and every s in S, with |S| = d
# distinct group elements. Left multiplication is an automorphism, so the
# diameter is decided by two BFS runs, from A_e and from B_e.
#
# The C engine runs tabu search over the connection set S. Each move replaces
# one element of S by a sampled group element. The cost is the excess-distance
# total (sum over the two BFS of max(0, t - DIAM) and an unreached penalty), so
# cost 0 exactly when the graph has diameter <= DIAM. Groups are semidirect
# products Z_m x|_r Z_k, with the order chosen just above the current target.
#
# Safe fallbacks: K_{d,d}, the projective plane incidence graph and W(q). Every
# result is checked with lib.is_valid before it is adopted.
#
# Usage: prog d D m k2 r seed slice_seconds
# Prints a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <limits.h>
#include <time.h>

#define GMAX 2400
#define STALL 1500
#define MOVES 400
#define TENURE 10

static int DEG, DIAM, MM, K2, G;
static int *POWR, *MT, *INV, *fr, *nx;
static uint32_t *vis;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* Semidirect product Z_MM x| Z_K2: (a,b)*(c,d) = (a + r^b c, b + d); code a*K2+b. */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, dd = y % K2;
    long long t = (a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + dd) % K2);
}

/* Excess-distance cost of the bi-Cayley graph with connection set S.
   SI[k] = inverse of S[k]. Zero iff diameter <= DIAM. */
static int cost_of(const int *S, const int *SI) {
    const int LMAX = DIAM + 3;
    const int UNREACH_W = LMAX - DIAM + 2;
    int total = 0;
    for (int side = 0; side < 2; side++) {
        int src = (side == 0) ? 0 : G;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)(2 * G));
            stamp = 0;
        }
        stamp++;
        vis[src] = stamp;
        int *cur = fr, *nxt = nx;
        int fn = 1, reached = 1;
        cur[0] = src;
        for (int lv = 0; lv < LMAX && fn > 0; lv++) {
            int nn = 0;
            for (int q = 0; q < fn; q++) {
                int u = cur[q];
                if (u < G) {
                    const int *row = MT + (size_t)u * G;
                    for (int k = 0; k < DEG; k++) {
                        int v = G + row[S[k]];
                        if (vis[v] != stamp) { vis[v] = stamp; nxt[nn++] = v; }
                    }
                } else {
                    const int *row = MT + (size_t)(u - G) * G;
                    for (int k = 0; k < DEG; k++) {
                        int v = row[SI[k]];
                        if (vis[v] != stamp) { vis[v] = stamp; nxt[nn++] = v; }
                    }
                }
            }
            reached += nn;
            if (lv + 1 > DIAM) total += (lv + 1 - DIAM) * nn;
            int *tmp = cur; cur = nxt; nxt = tmp;
            fn = nn;
        }
        total += (2 * G - reached) * UNREACH_W;
    }
    return total;
}

int main(int argc, char **argv) {
    if (argc < 8) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    MM = atoi(argv[3]);
    K2 = atoi(argv[4]);
    int r = atoi(argv[5]);
    uint64_t seed = strtoull(argv[6], NULL, 10);
    double slice = atof(argv[7]);

    if (DEG < 1 || DIAM < 1 || MM < 1 || K2 < 1) { printf("0 0\n"); return 0; }
    if ((long long)MM * K2 > GMAX || (long long)MM * K2 < DEG) { printf("0 0\n"); return 0; }
    G = MM * K2;
    r %= MM; if (r < 0) r += MM;
    if (gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }

    POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x7654321ULL;
    if (rs == 0) rs = 1;

    MT = malloc(sizeof(int) * (size_t)G * G);
    INV = malloc(sizeof(int) * G);
    fr = malloc(sizeof(int) * (size_t)(2 * G));
    nx = malloc(sizeof(int) * (size_t)(2 * G));
    vis = calloc((size_t)(2 * G), sizeof(uint32_t));
    int *S = malloc(sizeof(int) * DEG), *SI = malloc(sizeof(int) * DEG);
    int *bestS = malloc(sizeof(int) * DEG);
    char *inS = calloc(G, 1);
    long long *tabu = calloc(G, sizeof(long long));
    if (!MT || !INV || !fr || !nx || !vis || !S || !SI || !bestS || !inS || !tabu) {
        printf("0 0\n");
        return 0;
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            MT[(size_t)x * G + y] = gmul(x, y);
    for (int x = 0; x < G; x++) {
        INV[x] = 0;
        for (int y = 0; y < G; y++)
            if (MT[(size_t)x * G + y] == 0) { INV[x] = y; break; }
    }

    clock_t t0 = clock();
    int found = 0;
    int bestCost = INT_MAX;
    long long gi = 0;

    while (!found && elapsed(t0) < slice) {
        /* Random restart: DEG distinct elements. */
        memset(inS, 0, G);
        for (int k = 0; k < DEG; k++) {
            int g;
            do { g = rndint(G); } while (inS[g]);
            inS[g] = 1;
            S[k] = g;
            SI[k] = INV[g];
        }
        int cur = cost_of(S, SI);
        if (cur < bestCost) { bestCost = cur; memcpy(bestS, S, sizeof(int) * DEG); }
        if (cur == 0) { found = 1; memcpy(bestS, S, sizeof(int) * DEG); break; }

        int runBest = cur, since = 0;
        while (1) {
            if (elapsed(t0) >= slice) break;
            gi++;
            int bc = INT_MAX, bi = -1, bg = -1, nties = 0;
            for (int mv = 0; mv < MOVES; mv++) {
                int i = rndint(DEG);
                int g = rndint(G);
                if (inS[g]) continue;
                int keep = S[i];
                S[i] = g; SI[i] = INV[g];
                int c = cost_of(S, SI);
                S[i] = keep; SI[i] = INV[keep];
                if (tabu[g] > gi && c >= bestCost) continue;   /* tabu unless aspiration */
                if (c < bc) {
                    bc = c; bi = i; bg = g; nties = 1;
                } else if (c == bc) {
                    nties++;
                    if (rndint(nties) == 0) { bi = i; bg = g; }
                }
            }
            if (bi < 0) continue;
            int out = S[bi];
            inS[out] = 0;
            inS[bg] = 1;
            S[bi] = bg; SI[bi] = INV[bg];
            tabu[out] = gi + TENURE;
            cur = bc;
            if (cur < bestCost) { bestCost = cur; memcpy(bestS, S, sizeof(int) * DEG); }
            if (cur == 0) { found = 1; memcpy(bestS, S, sizeof(int) * DEG); break; }
            if (cur < runBest) { runBest = cur; since = 0; }
            else if (++since > STALL) break;
        }
    }

    if (found) {
        printf("%d %d\n", 2 * G, DEG * G);
        for (int k = 0; k < DEG; k++)
            for (int g = 0; g < G; g++)
                printf("%d %d\n", g, G + MT[(size_t)g * G + bestS[k]]);
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
    pts = [v for v in __import__("itertools").product(range(q), repeat=4)
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
# Group sampling: semidirect products Z_m x| Z_k with order m*k >= T and
# small waste, non-abelian (r != 1) whenever possible.
# ----------------------------------------------------------------------------

def _group_for(T, rng):
    """Return (m, k2, r) for a group of order m*k2 in [T, T + waste]."""
    cands = []
    for k2 in range(2, 41):
        if k2 > T:
            break
        m = -(-T // k2)
        if m < 2:
            continue
        waste = m * k2 - T
        if waste <= max(1, 0.02 * T):
            cands.append((m, k2))
    rng.shuffle(cands)
    for m, k2 in cands[:40]:
        rs_ = [c for c in range(2, m)
               if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
        if rs_:
            return m, k2, rng.choice(rs_)
    m = max(2, -(-T // 2))
    return m, 2, 1  # direct product Z_m x Z_2


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    budget = max(1.0, min(0.88 * time_limit, time_limit - 4.5))
    deadline = t_start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is larger and valid."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

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

    # Main loop: tabu search over connection sets, with an adaptive size target.
    step = 0.03
    while True:
        remaining = deadline - time.monotonic() - 1.0
        if remaining < 2.0:
            break
        slice_s = min(remaining, max(4.0, min(10.0, budget / 5)))
        want_n = best[0] * (1.0 + step) + 2
        T = max(d, math.ceil(want_n / 2))
        m, k2, r = _group_for(T, rng)
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
            step = max(0.002, step * 0.7)
            continue
        if consider(n, e):
            step = min(0.3, step * 1.3)
        else:
            step = max(0.002, step * 0.75)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, deadline)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
