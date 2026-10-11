import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New engine: simulated annealing over Z_M x| Z_K2 voltage lifts.
#
# Base: K "A" vertices and K "B" vertices, DEG darts per A vertex, built from DEG
# random perfect matchings (so every base vertex has DEG darts). Lift: vertex
# (base u, x) for x in G, dart (u, v, g) joins (u, x) to (v, x*g).
#
# Left multiplication by h is an automorphism of the lift, so the lift has
# diameter <= DIAM iff every base vertex's representative (u, identity) reaches
# all 2*K*N vertices within DIAM steps. Cost = total unreached count over the
# 2K representatives. Cost 0 = valid graph.
# ----------------------------------------------------------------------------

LIFT_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <time.h>

#define MAXV 4400
#define DEGMAX 16
#define MAXD 256

static int DEG, DIAM, K, N, M, K2, R, NV, NDART;
static int du[MAXD], dv[MAXD], dg[MAXD];
static int adj[MAXV][DEGMAX], dgr[MAXV];
static int pw[64];
static int dist_[MAXV], qu[MAXV];
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

/* element x codes (a, b) as a*K2 + b; (a,b)*(c,d) = (a + r^b c, b + d) */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, d = y % K2;
    int t = (int)(((long long)a + (long long)pw[b] * c) % M);
    return t * K2 + (b + d) % K2;
}

static void add_edge(int a, int b) {
    for (int i = 0; i < dgr[a]; i++)
        if (adj[a][i] == b) return;
    if (dgr[a] >= DEG || dgr[b] >= DEG) return;
    adj[a][dgr[a]++] = b;
    adj[b][dgr[b]++] = a;
}

static void build_lift(void) {
    NV = 2 * K * N;
    memset(dgr, 0, sizeof(int) * (size_t)NV);
    for (int t = 0; t < NDART; t++) {
        int u = du[t], v = dv[t], g = dg[t];
        for (int x = 0; x < N; x++)
            add_edge(u * N + x, v * N + gmul(x, g));
    }
}

static long cost(void) {
    build_lift();
    long tot = 0;
    for (int s = 0; s < 2 * K; s++) {
        int src = s * N;
        for (int v = 0; v < NV; v++) dist_[v] = -1;
        int qh = 0, qt = 0;
        qu[qt++] = src;
        dist_[src] = 0;
        while (qh < qt) {
            int x = qu[qh++];
            if (dist_[x] >= DIAM) continue;
            for (int i = 0; i < dgr[x]; i++) {
                int y = adj[x][i];
                if (dist_[y] < 0) {
                    dist_[y] = dist_[x] + 1;
                    qu[qt++] = y;
                }
            }
        }
        tot += NV - qt;
    }
    return tot;
}

static void randomize_base(void) {
    int perm[64];
    int idx = 0;
    for (int t = 0; t < DEG; t++) {
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd(i + 1);
            int tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            du[idx] = i;
            dv[idx] = K + perm[i];
            dg[idx] = rnd(N);
            idx++;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    K = atoi(argv[5]);
    M = atoi(argv[6]);
    K2 = atoi(argv[7]);
    R = atoi(argv[8]);
    if (DEG < 1 || DEG > DEGMAX || DIAM < 1 || K < 1 || M < 2 || K2 < 1 || K2 > 32 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    N = M * K2;
    if (2 * K * N > MAXV || DEG * K > MAXD) {
        printf("0 0\n");
        return 0;
    }
    pw[0] = 1 % M;
    for (int b = 1; b < K2; b++) pw[b] = (int)((long long)pw[b - 1] * R % M);
    if ((long long)pw[K2 - 1] * R % M != 1 % M) {
        printf("0 0\n");
        return 0;
    }

    rs = seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    NDART = DEG * K;
    randomize_base();
    long cur = cost();
    double t0 = (double)clock() / CLOCKS_PER_SEC;
    long stall = 0;

    while (cur != 0) {
        double frac = ((double)clock() / CLOCKS_PER_SEC - t0) / tl;
        if (frac >= 1.0) break;

        int j = rnd(NDART);
        int oldj = dg[j];
        dg[j] = (oldj + 1 + rnd(N - 1)) % N;
        int j2 = -1, old2 = 0;
        if (rnd01() < 0.3) {
            j2 = rnd(NDART);
            old2 = dg[j2];
            dg[j2] = rnd(N);
        }

        long c2 = cost();
        double T = 0.3 + 2.0 * (1.0 - frac);
        double dl = (double)(c2 - cur);
        if (dl <= 0 || rnd01() < exp(-dl / T)) {
            if (c2 < cur) stall = 0;
            cur = c2;
        } else {
            if (j2 >= 0) dg[j2] = old2;
            dg[j] = oldj;
        }

        if (++stall > 4000) {
            for (int t = 0; t < NDART; t++) dg[t] = rnd(N);
            cur = cost();
            stall = 0;
        }
    }

    if (cur != 0) {
        printf("0 0\n");
        return 0;
    }
    build_lift();
    long me = 0;
    for (int v = 0; v < NV; v++)
        for (int i = 0; i < dgr[v]; i++)
            if (v < adj[v][i]) me++;
    printf("%d %ld\n", NV, me);
    for (int v = 0; v < NV; v++)
        for (int i = 0; i < dgr[v]; i++)
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


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


def _twin_grow(n, edges, d, rng, deadline):
    """Add twin vertices (same neighbourhood) while neighbours have spare degree."""
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


def _pick_group(N, rng):
    """Random semidirect product Z_m x| Z_k2 of order N: returns (m, k2, r) or None."""
    opts = []
    for k2 in range(1, 13):
        if N % k2:
            continue
        m = N // k2
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if rs:
            opts.append((m, k2, rng.choice(rs)))
    return rng.choice(opts) if opts else None


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

    search_end = start + 0.75 * tl
    twin_end = start + 0.88 * tl

    # D = 3 non-calibration: largest projective plane below the degree bound.
    if D == 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        if qs:
            pn, pe = lib.projective_plane_incidence(qs[0])
            consider(pn, pe)

    # D >= 4: start from the generalized quadrangle W(q), saturated with spare degree.
    if D >= 4 and d >= 3:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            consider(gq[0], _saturate_edges(gq[0], gq[1], d, rng))

    # Main new search: voltage lifts over non-cyclic groups, annealed in C.
    # Each successful run raises the target order for the next run.
    if D >= 4 and d >= 5:
        round_id = 0
        while time.monotonic() < search_end - 2.0:
            k = rng.choice([1, 2, 3, 4, 5, 6])
            N = best_n // (2 * k) + 1 + rng.randrange(0, 4)
            grp = _pick_group(N, rng)
            if grp is None:
                continue
            m, k2, r = grp
            budget = min(search_end - time.monotonic(), 6.0)
            if budget < 1.0:
                break
            try:
                out = lib.run_c(LIFT_C,
                                [d, D, seed * 1000 + round_id, f"{budget:.2f}", k, m, k2, r],
                                timeout=budget + 3.0)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass
            round_id += 1

    # Grow the best graph by twins and saturation (each step checked by consider).
    if best_n > 0:
        n2, e2 = _twin_grow(best_n, list(best[1]), d, rng, twin_end)
        consider(n2, e2)
        consider(best_n, _saturate_edges(best_n, best[1], d, rng))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
