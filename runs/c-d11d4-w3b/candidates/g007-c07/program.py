import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: bi-Cayley graphs over metacyclic groups Z_m x|_r Z_k.
#
# Vertices (0, g) and (1, h) for g, h in G (|G| = m*k). Edges (0, g)-(1, g*s)
# for s in S, |S| = d. Left multiplication is an automorphism, so the diameter
# condition reduces to two BFS runs, from (0, e) and from (1, e), each reaching
# all 2|G| vertices within D steps. C runs simulated annealing over S, with
# cost = number of unreached (source, vertex) pairs.
#
# Python keeps the old quadrangle baseline (W(q) plus saturation) as a fallback.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define GMAX 2048
#define DMAX 32
#define NMAX (2 * GMAX)
#define STALL 2500
#define TEMP 1.0

static int M, K, G, R, DEG, DIAM;
static int pw[GMAX];
static int invT[GMAX];
static int S[DMAX], Sinv[DMAX];
static int Rt[GMAX * DMAX];
static int Lt[GMAX * DMAX];
static unsigned char mark[GMAX];
static int stampArr[NMAX], distArr[NMAX], qbuf[NMAX];
static int stampCur = 0;
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

static int gmul(int x, int y) {
    int a = x / K, b = x % K;
    int c = y / K, d = y % K;
    int aa = (a + pw[b] * c) % M;
    int bb = (b + d) % K;
    return aa * K + bb;
}

static int ginv(int x) {
    int a = x / K, b = x % K;
    int nb = (K - b) % K;
    int t = (pw[nb] * a) % M;
    int aa = (M - t) % M;
    return aa * K + nb;
}

static void set_slot(int i, int x) {
    S[i] = x;
    Sinv[i] = invT[x];
    for (int g = 0; g < G; g++) {
        Rt[g * DEG + i] = gmul(g, x);
        Lt[g * DEG + i] = gmul(g, Sinv[i]);
    }
}

static int bfs_reach(int src) {
    stampCur++;
    int qh = 0, qt = 0;
    qbuf[qt++] = src;
    stampArr[src] = stampCur;
    distArr[src] = 0;
    while (qh < qt) {
        int u = qbuf[qh++];
        int du = distArr[u];
        if (du >= DIAM) continue;
        if (u < G) {
            const int *row = Rt + u * DEG;
            for (int i = 0; i < DEG; i++) {
                int x = G + row[i];
                if (stampArr[x] != stampCur) {
                    stampArr[x] = stampCur;
                    distArr[x] = du + 1;
                    qbuf[qt++] = x;
                }
            }
        } else {
            const int *row = Lt + (u - G) * DEG;
            for (int i = 0; i < DEG; i++) {
                int x = row[i];
                if (stampArr[x] != stampCur) {
                    stampArr[x] = stampCur;
                    distArr[x] = du + 1;
                    qbuf[qt++] = x;
                }
            }
        }
    }
    return qt;
}

static int cost_now(void) {
    int N = 2 * G;
    int r0 = bfs_reach(0);
    int r1 = bfs_reach(G);
    return (N - r0) + (N - r1);
}

static void emit(void) {
    printf("%d %d\n", 2 * G, G * DEG);
    for (int g = 0; g < G; g++)
        for (int i = 0; i < DEG; i++)
            printf("%d %d\n", g, G + Rt[g * DEG + i]);
}

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    M = atoi(argv[5]);
    K = atoi(argv[6]);
    R = atoi(argv[7]);
    if (DEG < 1 || DEG > DMAX || DIAM < 1 || tl <= 0 || M < 2 || K < 1 ||
        (long)M * K > GMAX) {
        printf("0 0\n");
        return 0;
    }
    G = M * K;
    if (G < DEG) {
        printf("0 0\n");
        return 0;
    }
    R %= M;
    if (R < 0) R += M;
    pw[0] = 1 % M;
    for (int b = 1; b < K; b++) pw[b] = (pw[b - 1] * R) % M;
    if ((pw[K - 1] * R) % M != 1 % M) {
        printf("0 0\n");
        return 0;
    }
    {
        int a = R, b = M;
        while (b) {
            int t = a % b;
            a = b;
            b = t;
        }
        if (a != 1) {
            printf("0 0\n");
            return 0;
        }
    }
    for (int x = 0; x < G; x++) invT[x] = ginv(x);

    rs = seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    double t0 = (double)clock() / CLOCKS_PER_SEC;
    long long iter = 0;
    while (1) {
        if ((double)clock() / CLOCKS_PER_SEC - t0 >= tl) break;
        memset(mark, 0, (size_t)G);
        for (int i = 0; i < DEG; i++) {
            int x;
            do {
                x = rnd(G);
            } while (mark[x]);
            mark[x] = 1;
            set_slot(i, x);
        }
        int cur = cost_now();
        if (cur == 0) {
            emit();
            return 0;
        }
        if (G == DEG) break;
        int best = cur;
        long stall = 0;
        while (cur > 0) {
            iter++;
            if ((iter & 63) == 0 &&
                (double)clock() / CLOCKS_PER_SEC - t0 >= tl)
                break;
            int i = rnd(DEG);
            int old = S[i];
            int x;
            do {
                x = rnd(G);
            } while (mark[x]);
            mark[old] = 0;
            mark[x] = 1;
            set_slot(i, x);
            int c2 = cost_now();
            double dl = (double)(c2 - cur);
            if (dl <= 0 || rnd01() < exp(-dl / TEMP)) {
                cur = c2;
            } else {
                mark[x] = 0;
                mark[old] = 1;
                set_slot(i, old);
            }
            if (cur < best) {
                best = cur;
                stall = 0;
            } else if (++stall > STALL) {
                break;
            }
        }
        if (cur == 0) {
            emit();
            return 0;
        }
    }
    printf("0 0\n");
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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
    return color


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
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


_GROUP_CACHE = {}


def _groups_for(G):
    """Metacyclic groups Z_m x|_r Z_k of order G (k <= 12), as (m, k, list of valid r)."""
    if G in _GROUP_CACHE:
        return _GROUP_CACHE[G]
    opts = []
    for k in range(1, 13):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        rl = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if rl:
            opts.append((m, k, rl))
    _GROUP_CACHE[G] = opts
    return opts


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

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

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    # Baseline: quadrangle incidence graph plus saturation (valid for D >= 4).
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            consider(gq[0], _saturate_edges(gq[0], gq[1], d, rng))

    search_end = start + 0.88 * tl - 1.5
    if 2 <= d <= 32 and time.monotonic() < search_end - 0.5:
        lo = max(d, best[0] // 2 + 1)
        state = {"call": 0, "found": None}

        def attempt(m, k, rl, budget):
            state["call"] += 1
            r = rng.choice(rl)
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, seed * 7919 + state["call"], f"{budget:.3f}", m, k, r],
                    stdin_graph=None,
                    timeout=budget + 3.0,
                )
                n2, e2 = lib.parse_graph_text(out)
            except Exception:
                return False
            if n2 > 0 and consider(n2, e2):
                state["found"] = n2 // 2
                return True
            return False

        # Pass 1: sweep group orders upward from the first size that beats the baseline.
        sweep_end = time.monotonic() + 0.5 * (search_end - time.monotonic())
        G = lo
        while time.monotonic() < sweep_end and G < lo + 200:
            rem = sweep_end - time.monotonic()
            if rem < 0.05:
                break
            opts = _groups_for(G)
            if opts:
                m, k, rl = rng.choice(opts)
                attempt(m, k, rl, min(0.25, rem))
            G += 1

        # Pass 2: push just above the best success, or retry near the threshold.
        while True:
            rem = search_end - time.monotonic()
            if rem < 0.2:
                break
            if state["found"]:
                G = state["found"] + 1 + rng.randrange(8)
            else:
                G = lo + rng.randrange(60)
            opts = _groups_for(G)
            if not opts:
                continue
            m, k, rl = rng.choice(opts)
            attempt(m, k, rl, min(0.9, rem))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
