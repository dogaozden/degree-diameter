import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over voltage lifts.
#
# Base graph: K "A" vertices and K "B" vertices, d layers. Layer j is a
# permutation pi_j: A-vertex u sends dart (u, j) to B-vertex pi_j(u), so every
# base vertex has degree d. Each dart carries a voltage g in a finite group H
# of order G (H = Z_m1 x| Z_m2 with multiplication (a,b)(c,e) = (a + r^b c, b + e)).
#
# Lift: (u, x) ~ (v, x*g) for every dart (u, v, g) and every x in H. This is
# bipartite, d-regular, and the left action of H is an automorphism group, so
# every vertex of a side looks the same as the identity of its base class. Hence
# diameter <= D iff the D-balls of the 2K representatives (u, e) and (v, e) are
# the whole vertex set. Cost = total unreached count over those 2K BFS runs,
# plus a large penalty for parallel darts with equal voltage (multi-edges).
#
# Search: random restarts over (K, G, group) with G climbing past the best
# valid lift found so far; each attempt is an annealing run over voltages and
# permutation swaps. Output is the largest valid lift found.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 8
#define MAXDEG 40
#define MAXPER 1100
#define MAXG 1200
#define MAXN (2 * MAXPER)
#define MAXE (MAXPER * MAXDEG)
#define BIGPEN 100000LL

static int d, D, K, G;
static uint64_t rs = 1;
static int dv[MAXK][MAXDEG], dg[MAXK][MAXDEG];
static int inU[MAXK][MAXDEG], inG[MAXK][MAXDEG];
static int mulT[MAXG * MAXG];
static int invT[MAXG];
static int vis[MAXN], qq[MAXN];
static int stampv = 0;
static int bu[MAXE], bv[MAXE];
static int bestN = 0, bestM = 0, bestPer = 0;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nextr() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/* Group Z_m1 x| Z_m2 with element (a,b) coded as a*m2+b; identity is 0. */
static void build_group(int m1, int m2, int r) {
    static int pw[MAXG];
    G = m1 * m2;
    long long p = 1 % m1;
    for (int b = 0; b < m2; b++) {
        pw[b] = (int)p;
        p = (p * r) % m1;
    }
    for (int x = 0; x < G; x++) {
        int a = x / m2, b = x % m2;
        for (int y = 0; y < G; y++) {
            int c = y / m2, e = y % m2;
            int na = (int)((a + (long long)pw[b] * c) % m1);
            int nb = (b + e) % m2;
            mulT[x * G + y] = na * m2 + nb;
        }
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (mulT[x * G + y] == 0) {
                invT[x] = y;
                break;
            }
}

static void choose_group(int k, int g) {
    K = k;
    int divs[MAXG], nd = 0;
    for (int t = 1; t <= g; t++)
        if (g % t == 0) divs[nd++] = t;
    int m2 = divs[rnd(nd)];
    int m1 = g / m2;
    int r = 1;
    if (m1 >= 3 && m2 >= 2 && rnd(3) != 0) {
        for (int t = 0; t < 80; t++) {
            int c = 2 + rnd(m1 - 2);
            if (gcd_i(c, m1) != 1) continue;
            long long p = 1 % m1;
            for (int i = 0; i < m2; i++) p = (p * c) % m1;
            if (p == 1 % m1) {
                r = c;
                break;
            }
        }
    }
    build_group(m1, m2, r);
}

static void random_init(void) {
    int perm[MAXK];
    for (int j = 0; j < d; j++) {
        for (int u = 0; u < K; u++) perm[u] = u;
        for (int i = K - 1; i > 0; i--) {
            int t = rnd(i + 1);
            int x = perm[i];
            perm[i] = perm[t];
            perm[t] = x;
        }
        for (int u = 0; u < K; u++) {
            dv[u][j] = perm[u];
            dg[u][j] = rnd(G);
        }
    }
}

/* For each B-vertex v, record the in-dart from each layer j. */
static void rebuild_in(void) {
    for (int u = 0; u < K; u++)
        for (int j = 0; j < d; j++) {
            int v = dv[u][j];
            inU[v][j] = u;
            inG[v][j] = invT[dg[u][j]];
        }
}

static int bfs_unreached(int src) {
    int KG = K * G;
    int N = 2 * KG;
    stampv++;
    int head = 0, tail = 0;
    qq[tail++] = src;
    vis[src] = stampv;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int lend = tail;
        while (head < lend) {
            int id = qq[head++];
            if (id < KG) {
                int u = id / G, x = id - u * G;
                for (int j = 0; j < d; j++) {
                    int nb = KG + dv[u][j] * G + mulT[x * G + dg[u][j]];
                    if (vis[nb] != stampv) {
                        vis[nb] = stampv;
                        qq[tail++] = nb;
                    }
                }
            } else {
                int v = (id - KG) / G;
                int y = id - KG - v * G;
                for (int j = 0; j < d; j++) {
                    int nb = inU[v][j] * G + mulT[y * G + inG[v][j]];
                    if (vis[nb] != stampv) {
                        vis[nb] = stampv;
                        qq[tail++] = nb;
                    }
                }
            }
        }
    }
    return N - tail;
}

static long long eval_cost(void) {
    long long c = 0;
    for (int u = 0; u < K; u++) c += bfs_unreached(u * G);
    for (int v = 0; v < K; v++) c += bfs_unreached(K * G + v * G);
    long long col = 0;
    for (int u = 0; u < K; u++)
        for (int j = 0; j < d; j++)
            for (int i = j + 1; i < d; i++)
                if (dv[u][i] == dv[u][j] && dg[u][i] == dg[u][j]) col++;
    return c + col * BIGPEN;
}

static void mutate(void) {
    if (K < 2 || rnd(2) == 0) {
        int u = rnd(K), j = rnd(d);
        dg[u][j] = rnd(G);
    } else {
        int j = rnd(d);
        int u1 = rnd(K), u2 = rnd(K - 1);
        if (u2 >= u1) u2++;
        int t = dv[u1][j];
        dv[u1][j] = dv[u2][j];
        dv[u2][j] = t;
    }
}

static int run_trial(double end_t, double slice) {
    static int svdv[MAXK][MAXDEG], svdg[MAXK][MAXDEG];
    random_init();
    rebuild_in();
    long long cur = eval_cost();
    double t0 = now();
    double T = 3.0;
    for (long it = 0; cur > 0; it++) {
        if ((it & 31) == 0) {
            double t = now();
            if (t >= end_t || t - t0 >= slice) break;
            T = 3.0 * (1.0 - (t - t0) / slice) + 0.1;
        }
        memcpy(svdv, dv, sizeof dv);
        memcpy(svdg, dg, sizeof dg);
        mutate();
        rebuild_in();
        long long nc = eval_cost();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            memcpy(dv, svdv, sizeof dv);
            memcpy(dg, svdg, sizeof dg);
            rebuild_in();
        }
    }
    return cur == 0;
}

static void save_best(void) {
    int m = 0;
    for (int u = 0; u < K; u++)
        for (int j = 0; j < d; j++)
            for (int x = 0; x < G; x++) {
                bu[m] = u * G + x;
                bv[m] = K * G + dv[u][j] * G + mulT[x * G + dg[u][j]];
                m++;
            }
    bestM = m;
    bestN = 2 * K * G;
    bestPer = K * G;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 99991ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();
    if (d < 2 || d > MAXDEG || D < 2 || tl < 1.5) {
        printf("0 0\n");
        return 0;
    }
    double tstart = now();
    double end_t = tstart + tl - 1.0;
    double slice = tl * 0.15;
    if (slice < 1.0) slice = 1.0;

    while (now() < end_t && bestPer < MAXPER) {
        int k = 1 + rnd(6);
        int g = bestPer / k + 1 + rnd(3);
        if (g < 2) g = 2;
        if (k * g > MAXPER) g = MAXPER / k;
        if (g < 2 || k * g <= bestPer) continue;
        choose_group(k, g);
        if (run_trial(end_t, slice)) save_best();
    }

    if (bestM == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bu[i], bv[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python fallbacks and glue.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
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
    """W(q) for the largest prime power q <= 9 with q + 1 <= d (kept small for speed)."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order (never lengthens distances)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = lib._bipartition(n, adj) if hasattr(lib, "_bipartition") else None
    if color is None:
        color = [-1] * n
        for s in range(n):
            if color[s] != -1:
                continue
            color[s] = 0
            stack = [s]
            while stack:
                u = stack.pop()
                for v in adj[u]:
                    if color[v] == -1:
                        color[v] = 1 - color[u]
                        stack.append(v)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

    # Trivial cases.
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Calibration: D = 3 with d - 1 a prime power is the Moore-optimal incidence graph.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, e0, d, D):
            return n0, e0

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Second fallback for D >= 4: W(q) incidence graph, saturated with spare degree.
    if D >= 4 and d >= 3:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
                consider(gq[0], _saturate_edges(gq[0], gq[1], d, rng))
        except Exception:
            pass

    # Main path: C voltage-lift search over small groups.
    elapsed = time.monotonic() - start
    budget = max(1.0, tl * 0.85 - elapsed)
    if D >= 2 and d >= 2:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=None, timeout=budget + 10.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
