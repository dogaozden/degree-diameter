import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction for D >= 4: bipartite Cayley (Haar) graphs over Z_m.
# Vertices a_x, b_y (x, y in Z_m); a_x ~ b_{x+s} for s in S, |S| = d, 0 in S.
# C simulated annealing moves one element of S at a time and minimises the
# number of vertex pairs at distance > D. A zero-cost S gives a d-regular
# bipartite graph on 2m vertices.
# ----------------------------------------------------------------------------

HAAR_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 2000
#define MAXV (2 * MAXM)
#define WMAX ((MAXV + 63) / 64)
#define DMAX 32

static int d, D, m, nv;
static int S[DMAX];
static char in[MAXM];
static int adj[MAXV][DMAX];
static uint64_t RA[MAXV * WMAX], RB[MAXV * WMAX];
static uint64_t rs = 1;

static uint64_t nx(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nx() % (uint64_t)k); }

static double r01(void) { return (double)(nx() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void build(void) {
    nv = 2 * m;
    for (int x = 0; x < m; x++) {
        for (int i = 0; i < d; i++) {
            adj[x][i] = m + (x + S[i]) % m;
            adj[m + x][i] = ((x - S[i]) % m + m) % m;
        }
    }
}

static long long cost(void) {
    int Wn = (nv + 63) >> 6;
    uint64_t *cur = RA, *nxt = RB, *t;
    memset(RA, 0, sizeof(uint64_t) * (size_t)nv * (size_t)Wn);
    for (int v = 0; v < nv; v++)
        cur[(size_t)v * Wn + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < nv; v++) {
            uint64_t *o = nxt + (size_t)v * Wn;
            memcpy(o, cur + (size_t)v * Wn, sizeof(uint64_t) * (size_t)Wn);
            for (int i = 0; i < d; i++) {
                uint64_t *s = cur + (size_t)adj[v][i] * Wn;
                for (int w = 0; w < Wn; w++) o[w] |= s[w];
            }
        }
        t = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < nv; v++) {
        int c = 0;
        for (int w = 0; w < Wn; w++) c += pc64(cur[(size_t)v * Wn + w]);
        bad += nv - c;
    }
    return bad / 2;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    m = atoi(argv[5]);
    if (d < 2 || d > DMAX || D < 1 || m < d + 1 || m > MAXM || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nx();

    memset(in, 0, sizeof in);
    S[0] = 0;
    in[0] = 1;
    for (int i = 1; i < d; i++) {
        int x;
        do x = 1 + rnd(m - 1); while (in[x]);
        in[x] = 1;
        S[i] = x;
    }
    build();
    long long c = cost();
    clock_t t0 = clock();
    while (c > 0) {
        double frac = ((double)(clock() - t0) / CLOCKS_PER_SEC) / tl;
        if (frac >= 1.0) break;
        double T = 0.5 + 3.0 * (1.0 - frac);
        int i = 1 + rnd(d - 1);
        int x;
        do x = 1 + rnd(m - 1); while (in[x]);
        int old = S[i];
        in[old] = 0;
        in[x] = 1;
        S[i] = x;
        build();
        long long c2 = cost();
        if (c2 <= c || r01() < exp(-(double)(c2 - c) / T)) {
            c = c2;
        } else {
            in[x] = 0;
            in[old] = 1;
            S[i] = old;
            build();
        }
    }
    if (c != 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", 2 * m, m * d);
    for (int v = 0; v < m; v++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", v, adj[v][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q + 1, diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        inv = F.inv(next(x for x in v if x))
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    edges = []
    nl = 0
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
            for p in L:
                edges.append((p, P + nl))
                for r in L:
                    if p < r:
                        covered.add((p, r))
            nl += 1
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q <= min(d - 1, 9)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _colour(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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
    return col


def _balls(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _cover(cands, ball, full, d, rng):
    """Greedy cover of `full` by at most d candidates; randomised retries."""
    for t in range(4):
        pool = list(cands)
        if t:
            rng.shuffle(pool)
        covered, chosen = 0, []
        while covered != full and len(chosen) < d and pool:
            bg, bi = 0, -1
            for i, s in enumerate(pool):
                g = (ball[s] & ~covered).bit_count()
                if g > bg or (t and g == bg and g > 0 and rng.random() < 0.3):
                    bg, bi = g, i
            if bi < 0:
                break
            s = pool.pop(bi)
            chosen.append(s)
            covered |= ball[s]
        if covered == full:
            return chosen
    return None


def _extend(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover all vertices within radius D - 1."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    while time.monotonic() < deadline:
        col = _colour(n, adj)
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if col[s] == c and len(adj[s]) < d]
            chosen = _cover(cands, ball, full, d, rng)
            if chosen is None:
                continue
            v = n
            n += 1
            adj.append(list(chosen))
            for s in chosen:
                adj[s].append(v)
            added = True
            break
        if not added:
            break
    return n, [(u, v) for u in range(n) for v in adj[u] if u < v]


def _saturate(n, edges, d, rng):
    """Join deficient opposite-side vertices in random order."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    nb = [set(a) for a in adj]
    col = _colour(n, adj)
    left = [v for v in range(n) if col[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if col[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in nb[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d:
            adj[a].append(b)
            adj[b].append(a)
            edges.append((a, b))
    return n, edges


def _haar(d, D, m, seed, budget):
    """Run the C Haar-graph annealer on Z_m; return (n, edges) or None."""
    out = lib.run_c(HAAR_C, [d, D, seed, f"{budget:.2f}", m], timeout=budget + 5.0)
    n, e = lib.parse_graph_text(out)
    return (n, e) if e else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

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

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    p1 = start + (0.5 if D == 3 else 0.35) * tl
    if D == 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        if qs:
            n0, e0 = lib.projective_plane_incidence(qs[0])
            consider(n0, e0)
            n1, e1 = _extend(n0, e0, d, D, p1, rng)
            n1, e1 = _saturate(n1, e1, d, rng)
            consider(n1, e1)
    elif D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n1, e1 = _extend(gq[0], gq[1], d, D, p1, rng)
            n1, e1 = _saturate(n1, e1, d, rng)
            consider(n1, e1)

    # Bold branch for the target regime: search Haar graphs of growing order.
    if D >= 4 and d >= 5:
        end = start + 0.9 * tl - 1.0
        m = best[0] // 2 + 1
        fails = 0
        while fails < 3:
            remaining = end - time.monotonic()
            if remaining < 2.5:
                break
            budget = max(2.5, 0.35 * remaining)
            try:
                res = _haar(d, D, m, rng.randrange(1 << 30), budget)
            except Exception:
                res = None
            if res is not None:
                consider(res[0], res[1])
                fails = 0
                m = max(m + 1, res[0] // 2 + 1)
            else:
                fails += 1
                m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
