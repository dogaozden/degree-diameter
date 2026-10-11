import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley (Haar-type) graphs.
#
# Group G = Z_GA x Z_GB of order M (a random factorisation of each candidate M).
# Vertices A_g and B_h (g, h in G). Connection set S = {s_0 = 0, s_1, ..., s_{d-1}},
# |S| = d, distinct. Edges A_g -- B_{g + s} for s in S. The graph is d-regular,
# bipartite, with 2M vertices.
#
# Translations act transitively on each side, so diameter <= D is equivalent to:
# every vertex is within distance D of A_0 and within distance D of B_0.
# So the cost is just the number of vertices not reached from A_0 plus from B_0,
# which is two small BFS runs per move. Annealing moves replace one non-zero
# element of S. Each candidate M is given a time slice. Every success is kept,
# and the search continues with M + 1. The output is the largest valid graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 2000
#define MAXD 32

static int DEG, DIAM;
static int M, GA, GB;
static int S[MAXD];
static char inS[MAXM];
static int NA[MAXM * MAXD];
static int NBT[MAXM * MAXD];
static int bestS[MAXD];
static int bestM, bestGA, bestGB, haveBest;
static int distv[2 * MAXM];
static int stampv[2 * MAXM];
static int stampc = 0;
static int qbuf[2 * MAXM];
static uint64_t rs = 1;

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

/* group Z_GA x Z_GB, element a = x*GB + y */
static int gadd(int a, int b) {
    int x = a / GB + b / GB;
    if (x >= GA) x -= GA;
    int y = a % GB + b % GB;
    if (y >= GB) y -= GB;
    return x * GB + y;
}

static int gneg(int a) {
    int x = (GA - a / GB) % GA;
    int y = (GB - a % GB) % GB;
    return x * GB + y;
}

static void set_col(int k, int val) {
    int ng = gneg(val);
    S[k] = val;
    for (int g = 0; g < M; g++) {
        NA[g * MAXD + k] = gadd(g, val);
        NBT[g * MAXD + k] = gadd(g, ng);
    }
}

/* number of vertices within distance DIAM of src (src < M: A side, else B side) */
static int reach_count(int src) {
    stampc++;
    int head = 0, tail = 0;
    qbuf[tail++] = src;
    stampv[src] = stampc;
    distv[src] = 0;
    while (head < tail) {
        int v = qbuf[head++];
        int dv = distv[v];
        if (dv >= DIAM) continue;
        const int *row;
        int base;
        if (v < M) {
            row = NA + v * MAXD;
            base = M;
        } else {
            row = NBT + (v - M) * MAXD;
            base = 0;
        }
        for (int k = 0; k < DEG; k++) {
            int w = base + row[k];
            if (stampv[w] != stampc) {
                stampv[w] = stampc;
                distv[w] = dv + 1;
                qbuf[tail++] = w;
            }
        }
    }
    return tail;
}

static int cost(void) {
    int ra = reach_count(0);
    int rb = reach_count(M);
    return (2 * M - ra) + (2 * M - rb);
}

static void random_S(void) {
    memset(inS, 0, sizeof(char) * (size_t)M);
    inS[0] = 1;
    set_col(0, 0);
    for (int k = 1; k < DEG; k++) {
        int x;
        do {
            x = 1 + rnd(M - 1);
        } while (inS[x]);
        inS[x] = 1;
        set_col(k, x);
    }
}

static int anneal_m(double until) {
    random_S();
    int c = cost();
    int bestc = c;
    long it = 0, lastImp = 0;
    while (c > 0) {
        if ((it & 127) == 0 && now() >= until) return 0;
        it++;
        int k = 1 + rnd(DEG - 1);
        int old = S[k];
        int x;
        do {
            x = 1 + rnd(M - 1);
        } while (inS[x]);
        inS[old] = 0;
        inS[x] = 1;
        set_col(k, x);
        int c2 = cost();
        if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / 1.5)) {
            c = c2;
        } else {
            inS[x] = 0;
            inS[old] = 1;
            set_col(k, old);
        }
        if (c < bestc) {
            bestc = c;
            lastImp = it;
        }
        if (it - lastImp > 20000) {
            random_S();
            c = cost();
            bestc = c;
            lastImp = it;
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int mstart = atoi(argv[5]);
    int mmax = atoi(argv[6]);
    if (mmax > MAXM) mmax = MAXM;
    if (DEG < 2 || DEG > MAXD || DIAM < 2 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    haveBest = 0;
    int m = mstart;
    if (m < DEG + 1) m = DEG + 1;
    double end = tl;
    while (m <= mmax && now() < end) {
        int divs[64];
        int nd = 0;
        for (int t = 1; t <= m; t++)
            if (m % t == 0 && nd < 64) divs[nd++] = t;
        int gb = divs[rnd(nd)];
        M = m;
        GB = gb;
        GA = m / gb;
        double until = now() + 1.5;
        if (until > end) until = end;
        if (anneal_m(until)) {
            haveBest = 1;
            bestM = M;
            bestGA = GA;
            bestGB = GB;
            for (int k = 0; k < DEG; k++) bestS[k] = S[k];
        }
        m++;
    }

    if (!haveBest) {
        printf("0 0\n");
        return 0;
    }
    M = bestM;
    GA = bestGA;
    GB = bestGB;
    for (int k = 0; k < DEG; k++) set_col(k, bestS[k]);
    printf("%d %d\n", 2 * M, M * DEG);
    for (int g = 0; g < M; g++)
        for (int k = 0; k < DEG; k++)
            printf("%d %d\n", g, M + NA[g * MAXD + k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
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
    """Generalized quadrangle incidence graph W(q), q <= 9 and q + 1 <= d (cheap to build)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order (keeps diameter, bipartiteness)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
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
    if d >= 1 and D == 1:
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

    # Cheap algebraic baseline for the targets: GQ incidence graph and its saturation.
    if D >= 4 and d >= 5:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            consider(gq[0], _saturate_edges(gq[0], gq[1], d, rng))

    # Bold change: bi-Cayley (Haar-type) search over abelian groups, in C.
    # Cost is evaluated by two BFS runs (vertex-transitive on each side).
    budget = 0.8 * tl - 3.0 - (time.monotonic() - start)
    if budget >= 3.0:
        mstart = max(d + 1, best_n // 2 + 1)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", mstart, 1990],
                            stdin_graph=None, timeout=budget + 10.0)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
