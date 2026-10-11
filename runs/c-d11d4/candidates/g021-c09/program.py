import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over Z_m x| Z_k2 voltage lifts of a random
# d-regular bipartite base with KB + KB vertices. Each layer p joins A-vertex u
# to B-vertex Vt[p][u] with voltage Gv[p][u]. The lift has order 2*KB*GO, where
# GO = m*k2. Moves: change one voltage, or re-draw one layer's permutation.
# Cost = unordered pairs at distance > DIAM, via bitset ball propagation.
# Stops as soon as cost is 0 and prints that graph; otherwise prints "0 0".
# argv: d D seed time KB m k2 r
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXV 4096
#define WMAX (MAXV / 64)
#define DMAX 16
#define MAXK 64
#define MAXD 16

static int DEGV, DIAM, KB, MM, K2, RR, GO, NV;
static int adj[MAXV][DMAX];
static int dg[MAXV];
static int Vt[MAXD][MAXK];
static int Gv[MAXD][MAXK];
static int gpow[16];
static uint64_t RA[MAXV * WMAX];
static uint64_t RB[MAXV * WMAX];
static uint64_t rs = 1;

static uint64_t nxt64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int k) { return (int)(nxt64() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(nxt64() >> 11) * (1.0 / 9007199254740992.0);
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Group product in Z_MM x| Z_K2: (a,b)*(c,d) = (a + r^b c, b + d). */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, d = y % K2;
    long long t = ((long long)a + (long long)gpow[b] * c) % MM;
    return (int)(t * K2 + (b + d) % K2);
}

static void add_edge(int a, int b) {
    for (int i = 0; i < dg[a]; i++)
        if (adj[a][i] == b) return;
    if (dg[a] >= DMAX || dg[b] >= DMAX) return;
    adj[a][dg[a]++] = b;
    adj[b][dg[b]++] = a;
}

static void build(void) {
    NV = 2 * KB * GO;
    for (int v = 0; v < NV; v++) dg[v] = 0;
    for (int p = 0; p < DEGV; p++)
        for (int u = 0; u < KB; u++) {
            int v = Vt[p][u], g = Gv[p][u];
            for (int x = 0; x < GO; x++)
                add_edge(u * GO + x, (KB + v) * GO + gmul(x, g));
        }
}

static long long eval_cost(void) {
    int W = (NV + 63) >> 6;
    uint64_t *cur = RA, *nx = RB, *tmp;
    memset(RA, 0, sizeof(uint64_t) * (size_t)NV * (size_t)W);
    for (int v = 0; v < NV; v++)
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < NV; v++) {
            uint64_t *o = nx + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < dg[v]; i++) {
                uint64_t *t = cur + (size_t)adj[v][i] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        tmp = cur;
        cur = nx;
        nx = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < NV; v++) {
        uint64_t *s = cur + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += popc64(s[w]);
        bad += NV - cnt;
    }
    return bad / 2;
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    DEGV = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    KB = atoi(argv[5]);
    MM = atoi(argv[6]);
    K2 = atoi(argv[7]);
    RR = atoi(argv[8]);
    if (DEGV < 1 || DEGV > MAXD || DIAM < 1 || KB < 1 || KB > MAXK ||
        MM < 1 || K2 < 1 || K2 > 16 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    GO = MM * K2;
    if (GO < 2 || 2 * KB * GO > MAXV) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL + 4242ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nxt64();

    gpow[0] = 1 % MM;
    for (int b = 1; b < K2; b++)
        gpow[b] = (int)((long long)gpow[b - 1] * RR % MM);

    for (int p = 0; p < DEGV; p++) {
        for (int i = 0; i < KB; i++) Vt[p][i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = Vt[p][i];
            Vt[p][i] = Vt[p][j];
            Vt[p][j] = t;
        }
        for (int i = 0; i < KB; i++) Gv[p][i] = rndi(GO);
    }

    build();
    long long cur = eval_cost();
    double t0 = (double)clock() / CLOCKS_PER_SEC;

    while (cur != 0) {
        double frac = ((double)clock() / CLOCKS_PER_SEC - t0) / tl;
        if (frac >= 1.0) break;
        double T = 2.0 * pow(0.05, frac) + 0.02;

        if (KB > 1 && rnd01() < 0.12) {
            int p = rndi(DEGV);
            int old[MAXK];
            memcpy(old, Vt[p], sizeof(int) * (size_t)KB);
            for (int i = 0; i < KB; i++) Vt[p][i] = i;
            for (int i = KB - 1; i > 0; i--) {
                int j = rndi(i + 1);
                int t = Vt[p][i];
                Vt[p][i] = Vt[p][j];
                Vt[p][j] = t;
            }
            build();
            long long c2 = eval_cost();
            double dl = (double)(c2 - cur);
            if (dl <= 0 || rnd01() < exp(-dl / T)) {
                cur = c2;
            } else {
                memcpy(Vt[p], old, sizeof(int) * (size_t)KB);
                build();
            }
        } else {
            int p = rndi(DEGV);
            int u = rndi(KB);
            int old = Gv[p][u];
            int ng = rndi(GO - 1);
            if (ng >= old) ng++;
            Gv[p][u] = ng;
            build();
            long long c2 = eval_cost();
            double dl = (double)(c2 - cur);
            if (dl <= 0 || rnd01() < exp(-dl / T)) {
                cur = c2;
            } else {
                Gv[p][u] = old;
                build();
            }
        }
    }

    if (cur != 0) {
        printf("0 0\n");
        return 0;
    }
    long long em = 0;
    for (int v = 0; v < NV; v++) em += dg[v];
    printf("%d %lld\n", NV, em / 2);
    for (int v = 0; v < NV; v++)
        for (int i = 0; i < dg[v]; i++)
            if (v < adj[v][i]) printf("%d %d\n", v, adj[v][i]);
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 16)."""
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
    """Greedily join deficient opposite-side vertices in random order (diameter never grows)."""
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


def _twin_grow(n, edges, d, rng, deadline):
    """Add twin vertices (same side, same neighbourhood) while neighbours have spare degree."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
        order = list(range(n))
        rng.shuffle(order)
        for x in order:
            if time.monotonic() >= deadline:
                break
            nb = adj[x]
            if not nb or any(deg[y] >= d for y in nb):
                continue
            v = n
            n += 1
            adj.append(list(nb))
            deg.append(len(nb))
            for y in nb:
                adj[y].append(v)
                deg[y] += 1
                edges.append((y, v))
            changed = True
    return n, edges


def _group_options(G, rng):
    """Semidirect products Z_m x| Z_k2 of order G (k2 <= 16), as (m, k2, r) triples."""
    opts = []
    for k2 in range(1, 17):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            opts.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                opts.append((m, k2, r))
    rng.shuffle(opts)
    return opts[:12]


def _run_lift(d, D, seed, K, m, k2, r, budget):
    """Run the C voltage annealer for `budget` seconds; return parsed (n, edges), or (0, []) on failure."""
    out = lib.run_c(C_LIFT, [d, D, seed, f"{budget:.2f}", K, m, k2, r],
                    stdin_graph=None, timeout=budget + 5.0)
    return lib.parse_graph_text(out)


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
    end = start + 0.85 * tl - 1.5

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # D = 3 (non-calibration): projective plane, twin growth, then saturation.
    if D == 3 and d >= 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:1]
        for q in qs:
            pn, pe = lib.projective_plane_incidence(q)
            consider(pn, pe)
            tn, te = _twin_grow(pn, pe, d, rng, end)
            consider(tn, te)
            consider(tn, _saturate_edges(tn, te, d, rng))

    # D >= 4: generalized quadrangle W(q), then a voltage-lift search over
    # non-cyclic groups that aims just above the current best order.
    if D >= 4 and d >= 3:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            consider(gq[0], _saturate_edges(gq[0], gq[1], d, rng))

            Ks = [1, 2, 3, 4, 5, 6]
            failed = set()
            jump = 24
            while True:
                remaining = end - time.monotonic()
                if remaining < 4.0:
                    break
                goal = best_n + jump
                cands = []
                for K in Ks:
                    g0 = max(2, round(goal / (2 * K)))
                    for G in (g0 - 1, g0, g0 + 1):
                        if G < 2:
                            continue
                        n = 2 * K * G
                        if n <= best_n or n > 4000 or (K, G) in failed:
                            continue
                        cands.append((abs(n - goal), K, G))
                if not cands:
                    break
                cands.sort()
                _, K, G = cands[0]
                opts = _group_options(G, rng)
                if not opts:
                    failed.add((K, G))
                    continue
                m, k2, r = opts[rng.randrange(len(opts))]
                budget = min(remaining - 2.0, max(5.0, remaining / 5.0))
                try:
                    n2, e2 = _run_lift(d, D, rng.randrange(1 << 30), K, m, k2, r, budget)
                except Exception:
                    n2, e2 = 0, []
                if n2 > best_n:
                    before = best_n
                    consider(n2, e2)
                    if best_n > before:
                        jump = min(jump * 2, 400)
                    else:
                        failed.add((K, G))
                        jump = max(2, jump // 2)
                else:
                    failed.add((K, G))
                    jump = max(2, jump // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
