import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over VOLTAGE LIFTS of a small base graph.
#
# A lift has 2*KB base vertices (A side 0..KB-1, B side KB..2KB-1) and a group
# G = MM*K2 with elements a*K2+b, multiplication (a,b)*(c,d) = (a + R^b c, b + d).
# Darts (A-vertex, B-vertex, voltage) form a d-regular bipartite base multigraph.
# Dart (i, j, g) joins u*G+x to v*G+mul(x,g) for every x in the group.
#
# State: the darts. Moves: change one voltage, swap B-endpoints of two darts,
# swap A-endpoints of two darts (these keep the base degrees fixed).
# Cost: number of unordered vertex pairs at distance > DIAM in the lift, computed
# with bitset BFS. The first zero-cost lift is printed (bipartite, degree <= d,
# diameter <= D, all edges distinct). Failure prints "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXV 4096
#define WMAX 64
#define MAXK 16
#define MAXD 16
#define MAXDARTS (MAXK * MAXD)
#define MAXK2 4096
#define STALL_LIM 4000

static int DEGC, DIAM, KB, MM, K2, GG, NV, NDARTS;
static int DA[MAXDARTS], DB[MAXDARTS], DG[MAXDARTS];
static int BDA[MAXDARTS], BDB[MAXDARTS], BDG[MAXDARTS];
static int powr[MAXK2];
static int adjv[MAXV][MAXD];
static int dgv[MAXV];
static uint64_t SA[MAXV * WMAX], SB[MAXV * WMAX];
static uint64_t rs = 1;

static uint64_t nxt64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int n) { return (int)(nxt64() % (uint64_t)n); }

static double rnd01(void) {
    return (double)(nxt64() >> 11) * (1.0 / 9007199254740992.0);
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int gmul(int x, int g) {
    int a = x / K2, b = x % K2;
    int c = g / K2, d = g % K2;
    long long t = ((long long)powr[b] * c + a) % MM;
    return (int)t * K2 + (b + d) % K2;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < dgv[u]; i++)
        if (adjv[u][i] == v) return 1;
    return 0;
}

static void build_lift(void) {
    NV = 2 * KB * GG;
    for (int v = 0; v < NV; v++) dgv[v] = 0;
    for (int t = 0; t < NDARTS; t++) {
        int ua = DA[t];
        int vb = KB + DB[t];
        for (int x = 0; x < GG; x++) {
            int u = ua * GG + x;
            int v = vb * GG + gmul(x, DG[t]);
            if (dgv[u] < DEGC && dgv[v] < DEGC && !has_edge(u, v)) {
                adjv[u][dgv[u]++] = v;
                adjv[v][dgv[v]++] = u;
            }
        }
    }
}

static long long eval_bad(void) {
    build_lift();
    int W = (NV + 63) >> 6;
    uint64_t *cur = SA, *nx = SB, *tmp;
    memset(cur, 0, sizeof(uint64_t) * (size_t)NV * (size_t)W);
    for (int v = 0; v < NV; v++)
        cur[(size_t)v * W + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < NV; v++) {
            uint64_t *o = nx + (size_t)v * W;
            const uint64_t *s = cur + (size_t)v * W;
            memcpy(o, s, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < dgv[v]; i++) {
                const uint64_t *t = cur + (size_t)adjv[v][i] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        tmp = cur;
        cur = nx;
        nx = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < NV; v++) {
        const uint64_t *s = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(s[w]);
        bad += NV - c;
    }
    return bad / 2;
}

static int propose(int *oi, int *oj, int sv[2][3]) {
    int i = rndi(NDARTS), j = rndi(NDARTS);
    int type = rndi(10);
    *oi = i;
    *oj = j;
    sv[0][0] = DA[i]; sv[0][1] = DB[i]; sv[0][2] = DG[i];
    sv[1][0] = DA[j]; sv[1][1] = DB[j]; sv[1][2] = DG[j];
    if (type < 5) {
        DG[i] = (DG[i] + 1 + rndi(GG - 1)) % GG;
    } else if (type < 8) {
        if (i == j || DB[i] == DB[j]) return 0;
        int t = DB[i]; DB[i] = DB[j]; DB[j] = t;
    } else {
        if (i == j || DA[i] == DA[j]) return 0;
        int t = DA[i]; DA[i] = DA[j]; DA[j] = t;
    }
    return 1;
}

static void undo(int i, int j, int sv[2][3]) {
    DA[i] = sv[0][0]; DB[i] = sv[0][1]; DG[i] = sv[0][2];
    DA[j] = sv[1][0]; DB[j] = sv[1][1]; DG[j] = sv[1][2];
}

static void save_best(void) {
    memcpy(BDA, DA, sizeof(int) * NDARTS);
    memcpy(BDB, DB, sizeof(int) * NDARTS);
    memcpy(BDG, DG, sizeof(int) * NDARTS);
}

static void restore_best(void) {
    memcpy(DA, BDA, sizeof(int) * NDARTS);
    memcpy(DB, BDB, sizeof(int) * NDARTS);
    memcpy(DG, BDG, sizeof(int) * NDARTS);
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 1;
    }
    DEGC = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    KB = atoi(argv[5]);
    MM = atoi(argv[6]);
    K2 = atoi(argv[7]);
    long long rr = atoll(argv[8]);
    if (DEGC < 1 || DEGC > MAXD || DIAM < 1 || DIAM > 64 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    if (KB < 1 || KB > MAXK || MM < 1 || K2 < 1 || K2 > MAXK2) {
        printf("0 0\n");
        return 0;
    }
    GG = MM * K2;
    if (GG < 2 || 2 * KB * GG > MAXV) {
        printf("0 0\n");
        return 0;
    }

    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nxt64();

    long long R = ((rr % MM) + MM) % MM;
    powr[0] = 1 % MM;
    for (int b = 1; b < K2; b++)
        powr[b] = (int)((long long)powr[b - 1] * R % MM);

    NDARTS = KB * DEGC;
    int perm[MAXK];
    for (int p = 0; p < DEGC; p++) {
        for (int i = 0; i < KB; i++) perm[i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < KB; i++) {
            int t = p * KB + i;
            DA[t] = i;
            DB[t] = perm[i];
            DG[t] = rndi(GG);
        }
    }

    long long cur = eval_bad();
    long long best = cur;
    save_best();
    double c0 = (double)clock() / CLOCKS_PER_SEC;
    double T0 = 1.0 + 0.02 * (double)cur;
    long long stall = 0;

    while (best > 0) {
        double frac = ((double)clock() / CLOCKS_PER_SEC - c0) / tl;
        if (frac >= 1.0) break;
        int i, j;
        int sv[2][3];
        if (!propose(&i, &j, sv)) continue;
        long long c2 = eval_bad();
        double dl = (double)(c2 - cur);
        double T = T0 * (1.0 - frac) + 0.05;
        if (dl <= 0 || rnd01() < exp(-dl / T)) {
            cur = c2;
        } else {
            undo(i, j, sv);
        }
        if (cur < best) {
            best = cur;
            save_best();
            stall = 0;
        } else if (++stall > STALL_LIM) {
            restore_best();
            for (int q = 0; q < 3; q++) DG[rndi(NDARTS)] = rndi(GG);
            cur = eval_bad();
            stall = 0;
        }
    }

    if (best != 0) {
        printf("0 0\n");
        return 0;
    }
    restore_best();
    eval_bad();
    long long m = 0;
    for (int v = 0; v < NV; v++) m += dgv[v];
    printf("%d %lld\n", NV, m / 2);
    for (int v = 0; v < NV; v++)
        for (int i = 0; i < dgv[v]; i++)
            if (v < adjv[v][i]) printf("%d %d\n", v, adjv[v][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

RECORD_HINT = {(11, 4): 1734}
MAX_LIFT_N = 4096


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _best_gq(d):
    """W(q) incidence graph for the largest prime power q with q + 1 <= d."""
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
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
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
    """Add twins (same side, same neighbourhood) while neighbours have spare degree."""
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
    """Semidirect parameters (m, k2, r) with m * k2 = G, sampled per divisor."""
    opts = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if k2 == 1 or m == 1:
            opts.append((m, k2, 0))
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if rs:
            for r in rng.sample(rs, min(len(rs), 3)):
                opts.append((m, k2, r))
    return opts


def _lift_attempt(d, D, seed, budget, k, m, k2, r):
    """Run the C voltage annealer once; return (n, edges) or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", k, m, k2, r],
                        timeout=budget + 6.0)
        n, e = lib.parse_graph_text(out)
    except (RuntimeError, ValueError):
        return None
    if n < 1 or not e:
        return None
    return n, e


def _feasible(d, D, n, rng, deadline):
    """Try a few random group lifts of exactly n vertices; return a valid graph or None."""
    ks = [k for k in (1, 2, 3, 4, 6, 8)
          if n % (2 * k) == 0 and n // (2 * k) >= 2]
    if not ks:
        return None
    for _ in range(3):
        left = deadline - time.monotonic()
        if left < 1.2:
            return None
        budget = min(3.0, left - 0.3)
        k = rng.choice(ks)
        G = n // (2 * k)
        opts = _group_options(G, rng)
        if not opts:
            continue
        m, k2, r = rng.choice(opts)
        res = _lift_attempt(d, D, rng.randrange(1, 1 << 30), budget, k, m, k2, r)
        if res is not None:
            return res
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.9 * float(time_limit) - 0.5
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))          # K_{d,d}, Moore-optimal
    if d == 2:
        n = 2 * D                                   # even cycle C_{2D}
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Calibration: D = 3 with d - 1 a prime power is Moore-optimal.
    if D == 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, e0, d, D):
            return n0, e0

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Safe fallbacks.
    if D == 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        if qs and time.monotonic() < deadline:
            pn, pe = lib.projective_plane_incidence(qs[0])
            consider(pn, _saturate_edges(pn, pe, d, rng))
    elif D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            sat_e = _saturate_edges(gq[0], gq[1], d, rng)
            consider(gq[0], sat_e)
            if time.monotonic() < deadline:
                tn, te = _twin_grow(gq[0], sat_e, d, rng, deadline)
                consider(tn, te)

    # Main search: binary search on the order of voltage lifts above the fallback.
    moore = lib.moore_bound(d, D)
    if (d, D) in RECORD_HINT:
        top = RECORD_HINT[(d, D)] + 6
    else:
        top = int(0.8 * moore)
    top = min(top, MAX_LIFT_N)
    lo, hi = best_n // 2, top // 2
    while lo < hi and deadline - time.monotonic() > 1.5:
        mid = (lo + hi + 1) // 2
        res = _feasible(d, D, 2 * mid, rng, deadline)
        if res is not None:
            consider(res[0], res[1])
            lo = mid
        else:
            hi = mid - 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
