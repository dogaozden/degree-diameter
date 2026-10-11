import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley graphs.
#
# Group: Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b, product
# (a,b)(c,d) = (a + r^b c, b + d)). Vertices A_g = g and B_g = G + g, where
# G = m*k2. Connection set S (DEG distinct elements): A_g ~ B_{g s} for s in S.
# Left multiplication is an automorphism, so BFS from A_1 and B_1 decides the
# diameter exactly. The cost is the number of (source, vertex) pairs not within
# DIAM steps, plus a penalty per repeated element of S. Cost 0 gives a valid graph.
#
# Moves: replace one element of S by a random element outside S.
# Restarts: fresh random S, or a kick from the best S found so far.
#
# Usage: prog DEG DIAM m k2 r seed slice_seconds
# Prints "n m" plus edges, or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define RL 40000
#define STAG 6000
#define GMAX 5000

static int DEG, DIAM, MM, K2, G, NV;
static int *POWR, *inv_t, *S, *bestS, *invS, *qb;
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

static inline int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, d = y % K2;
    long long t = (a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + d) % K2);
}

static int cost_fn(void) {
    int dup = 0;
    for (int i = 0; i < DEG; i++) {
        invS[i] = inv_t[S[i]];
        for (int j = i + 1; j < DEG; j++) if (S[i] == S[j]) dup++;
    }
    int total = PEN * dup;
    for (int src = 0; src < 2; src++) {
        if (++stamp == 0) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)NV);
            stamp = 1;
        }
        int s0 = src ? G : 0;
        int head = 0, tail = 1;
        qb[0] = s0;
        vis[s0] = stamp;
        for (int lv = 0; lv < DIAM; lv++) {
            int end = tail;
            if (head == end) break;
            for (int q = head; q < end; q++) {
                int u = qb[q];
                if (u < G) {
                    for (int i = 0; i < DEG; i++) {
                        int v = G + gmul(u, S[i]);
                        if (vis[v] != stamp) { vis[v] = stamp; qb[tail++] = v; }
                    }
                } else {
                    int h = u - G;
                    for (int i = 0; i < DEG; i++) {
                        int v = gmul(h, invS[i]);
                        if (vis[v] != stamp) { vis[v] = stamp; qb[tail++] = v; }
                    }
                }
            }
            head = end;
        }
        total += NV - tail;
    }
    return total;
}

static void fresh_element(int i) {
    int x, ok;
    do {
        x = rndint(G);
        ok = 1;
        for (int j = 0; j < DEG; j++) if (j != i && S[j] == x) { ok = 0; break; }
    } while (!ok);
    S[i] = x;
}

int main(int argc, char **argv) {
    if (argc < 8) {
        fprintf(stderr, "usage: prog DEG DIAM m k2 r seed slice\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    MM = atoi(argv[3]);
    K2 = atoi(argv[4]);
    int r = atoi(argv[5]);
    uint64_t seed = strtoull(argv[6], NULL, 10);
    double slice = atof(argv[7]);

    if (DEG < 1 || DIAM < 1 || MM < 2 || K2 < 1) { printf("0 0\n"); return 0; }
    long long Gl = (long long)MM * K2;
    if (Gl > GMAX || DEG > Gl) { printf("0 0\n"); return 0; }
    if (r < 1 || gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }
    G = (int)Gl;
    NV = 2 * G;

    POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    S = malloc(sizeof(int) * DEG);
    bestS = malloc(sizeof(int) * DEG);
    invS = malloc(sizeof(int) * DEG);
    inv_t = malloc(sizeof(int) * G);
    qb = malloc(sizeof(int) * NV);
    vis = calloc((size_t)NV, sizeof(uint32_t));
    if (!S || !bestS || !invS || !inv_t || !qb || !vis) { printf("0 0\n"); return 0; }

    for (int x = 0; x < G; x++) {
        inv_t[x] = -1;
        for (int y = 0; y < G; y++) {
            if (gmul(x, y) == 0) { inv_t[x] = y; break; }
        }
        if (inv_t[x] < 0) { printf("0 0\n"); return 0; }
    }

    clock_t t0 = clock();
    int found = 0;
    int bestCost = 1 << 30;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestCost >= (1 << 30) || rnd01() < 0.3) {
            for (int i = 0; i < DEG; i++) fresh_element(i);
            T0 = 1.5;
        } else {
            memcpy(S, bestS, sizeof(int) * (size_t)DEG);
            int kick = 1 + rndint(2);
            for (int k = 0; k < kick; k++) fresh_element(rndint(DEG));
            T0 = 0.6;
        }
        int cur = cost_fn();
        if (cur < bestCost) { bestCost = cur; memcpy(bestS, S, sizeof(int) * (size_t)DEG); }
        if (cur == 0) { found = 1; break; }

        int runBest = cur;
        int since = 0;
        for (int it = 0; it < RL; it++) {
            if ((it & 255) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.03;
            int i = rndint(DEG);
            int x = rndint(G);
            int in = 0;
            for (int j = 0; j < DEG; j++) if (S[j] == x) { in = 1; break; }
            if (in) continue;
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
            if (cur < runBest) { runBest = cur; since = 0; }
            else if (++since > STAG) break;
        }
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", NV, DEG * G);
    for (int g = 0; g < G; g++) {
        for (int i = 0; i < DEG; i++) {
            printf("%d %d\n", g, G + gmul(g, S[i]));
        }
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions and helpers.
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
# Bi-Cayley search over a wide family of groups Z_m x|_r Z_k2.
# ----------------------------------------------------------------------------

def _groups(G):
    """All (m, k2, r) with m * k2 = G and r a valid twist (r^k2 = 1 mod m, gcd(r, m) = 1)."""
    out = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2 or k2 > 4096:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                out.append((m, k2, r))
    return out


def _bicayley(d, D, best, rng, deadline, slice_pref):
    """Search bi-Cayley graphs with 2G vertices, growing G while the search succeeds."""
    moore = lib.moore_bound(d, D)
    G = max(best[0] // 2 + 1, moore // 6, d + 1)
    fails = 0
    while G <= 5000:
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            break
        cands = _groups(G)
        if not cands:
            G += 1
            continue
        nontriv = [c for c in cands if c[2] > 1]
        m, k2, r = rng.choice(nontriv or cands)
        slice_s = min(remaining - 1.0, slice_pref)
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                timeout=slice_s + 10.0,
            )
            n, e = lib.parse_graph_text(out)
        except Exception:
            break
        if n > 0 and lib.is_valid(n, e, d, D) and n > best[0]:
            best = (n, e)
            G = n // 2 + 1
            fails = 0
            continue
        fails += 1
        if fails >= 3:
            break
    return best


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = (2, [(0, 1)])
    cand = lib.haar_graph(d, range(d))
    if lib.is_valid(cand[0], cand[1], d, D):
        best = cand

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        if D == 3 and pg is not None and lib.is_prime_power(d - 1):
            return best

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bold path: bi-Cayley search over nonabelian and abelian groups.
    if d >= 3 and time.monotonic() < deadline - 2.0:
        slice_pref = max(3.0, 0.2 * budget)
        best = _bicayley(d, D, best, rng, deadline, slice_pref)

    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, deadline)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        fb = lib.haar_graph(d, range(d))
        best = fb if lib.is_valid(fb[0], fb[1], d, D) else (2, [(0, 1)])
    return best
