import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over voltage lifts of small bipartite base
# multigraphs with voltages in a group G = Z_m x| Z_k (element a*k+b).
#
# Base: kb vertices per side, d darts per vertex (d random perfect matchings
# of K_{kb,kb} stacked). Dart (i, j, g) joins (A,i,x) to (B,j,x*g) for all x.
# Parallel darts get distinct voltages, so the lift is simple and d-regular.
#
# The left action of G is an automorphism group with 2*kb orbits, so the
# number of pairs at distance > D equals G times a sum over 2*kb representatives
# (A,i,e), (B,j,e). Cost = sum of far-counts over representatives; cost 0 means
# the lift is valid. The engine stops and prints the graph as soon as cost is 0.
# ----------------------------------------------------------------------------

LIFT_C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 12
#define MAXKB 8
#define MAXG 2600
#define MAXN (2 * MAXKB * MAXG)
#define MAXDART (MAXD * MAXKB)
#define MAXK 12

static int d, DIAM, kb, gm, gk, gr, G, N, nd;
static int rp[MAXK + 1];
static int *mulT;
static int invT[MAXG];
static int dI[MAXDART], dJ[MAXDART], dG[MAXDART];
static int outIdx[MAXKB][MAXD], inIdx[MAXKB][MAXD];
static int cntOut[MAXKB], cntIn[MAXKB];
static int distv[MAXN], stampv[MAXN], qv[MAXN];
static int stampc = 0;
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

static int gmul_calc(int x, int y) {
    int a = x / gk, b = x % gk;
    int c = y / gk, e = y % gk;
    int a2 = (a + rp[b] * c) % gm;
    int b2 = (b + e) % gk;
    return a2 * gk + b2;
}

/* BFS from vertex s in the lift; returns number of vertices at distance > DIAM. */
static int far_from(int s) {
    stampc++;
    int qh = 0, qt = 0;
    int reached = 1;
    int ALIM = kb * G;
    qv[qt++] = s;
    stampv[s] = stampc;
    distv[s] = 0;
    while (qh < qt) {
        int u = qv[qh++];
        int du = distv[u];
        if (du >= DIAM) continue;
        if (u < ALIM) {
            int i = u / G;
            int x = u - i * G;
            for (int t = 0; t < d; t++) {
                int dt = outIdx[i][t];
                int y = mulT[x * G + dG[dt]];
                int w = (kb + dJ[dt]) * G + y;
                if (stampv[w] != stampc) {
                    stampv[w] = stampc;
                    distv[w] = du + 1;
                    qv[qt++] = w;
                    reached++;
                }
            }
        } else {
            int jj = u - ALIM;
            int j = jj / G;
            int y = jj - j * G;
            for (int t = 0; t < d; t++) {
                int dt = inIdx[j][t];
                int x = mulT[y * G + invT[dG[dt]]];
                int w = dI[dt] * G + x;
                if (stampv[w] != stampc) {
                    stampv[w] = stampc;
                    distv[w] = du + 1;
                    qv[qt++] = w;
                    reached++;
                }
            }
        }
    }
    return N - reached;
}

static long long cost_eval(void) {
    long long c = 0;
    for (int i = 0; i < kb; i++) c += far_from(i * G);
    for (int j = 0; j < kb; j++) c += far_from((kb + j) * G);
    return c;
}

/* True if dart t with voltage g would parallel an earlier dart (t2 < lim) with the same g. */
static int conflict_n(int t, int g, int lim) {
    for (int t2 = 0; t2 < lim; t2++)
        if (t2 != t && dI[t2] == dI[t] && dJ[t2] == dJ[t] && dG[t2] == g) return 1;
    return 0;
}

static void build_base(void) {
    nd = d * kb;
    int perm[MAXKB];
    for (int p = 0; p < d; p++) {
        for (int i = 0; i < kb; i++) perm[i] = i;
        for (int i = kb - 1; i > 0; i--) {
            int j = rnd(i + 1);
            int tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < kb; i++) {
            int t = p * kb + i;
            dI[t] = i;
            dJ[t] = perm[i];
        }
    }
    for (int i = 0; i < kb; i++) { cntOut[i] = 0; cntIn[i] = 0; }
    for (int t = 0; t < nd; t++) {
        int i = dI[t], j = dJ[t];
        outIdx[i][cntOut[i]++] = t;
        inIdx[j][cntIn[j]++] = t;
    }
    for (int t = 0; t < nd; t++) {
        int g;
        do {
            g = rnd(G);
        } while (conflict_n(t, g, t));
        dG[t] = g;
    }
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    gm = atoi(argv[5]);
    gk = atoi(argv[6]);
    gr = atoi(argv[7]);
    kb = atoi(argv[8]);
    if (d < 1 || d > MAXD || DIAM < 1 || DIAM > 30 || kb < 1 || kb > MAXKB ||
        gm < 1 || gk < 1 || gk > MAXK || gr < 0 || gr >= gm || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    G = gm * gk;
    if (G > MAXG || G < d + 1) {
        printf("0 0\n");
        return 0;
    }
    N = 2 * kb * G;

    rs = seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    rp[0] = 1 % gm;
    for (int b = 1; b <= gk; b++) rp[b] = (int)((long long)rp[b - 1] * gr % gm);

    mulT = (int *)malloc(sizeof(int) * (size_t)G * (size_t)G);
    if (!mulT) {
        printf("0 0\n");
        return 0;
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            mulT[x * G + y] = gmul_calc(x, y);
    for (int x = 0; x < G; x++) {
        invT[x] = -1;
        for (int y = 0; y < G; y++)
            if (mulT[x * G + y] == 0) {
                invT[x] = y;
                break;
            }
        if (invT[x] < 0) {
            printf("0 0\n");
            return 0;
        }
    }

    build_base();

    long long cur = cost_eval();
    const double Tmax = 2.0, Tmin = 0.05;
    const long PER = 40000;
    double clk0 = (double)clock() / CLOCKS_PER_SEC;
    long it = 0;
    while (cur > 0) {
        if ((it & 127) == 0) {
            double el = (double)clock() / CLOCKS_PER_SEC - clk0;
            if (el >= tl) break;
        }
        long ph = it % PER;
        it++;
        double T = Tmax * pow(Tmin / Tmax, (double)ph / (double)PER);
        int t = rnd(nd);
        int g = rnd(G);
        if (g == dG[t] || conflict_n(t, g, nd)) continue;
        int old = dG[t];
        dG[t] = g;
        long long c2 = cost_eval();
        if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
            cur = c2;
        } else {
            dG[t] = old;
        }
    }

    if (cur == 0) {
        long long E = (long long)nd * G;
        printf("%d %lld\n", N, E);
        for (int t = 0; t < nd; t++) {
            for (int x = 0; x < G; x++) {
                int A = dI[t] * G + x;
                int B = (kb + dJ[t]) * G + mulT[x * G + dG[t]];
                printf("%d %d\n", A, B);
            }
        }
    } else {
        printf("0 0\n");
    }
    free(mulT);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

LIFT_SLICE = 3.0      # seconds per C lift attempt (returns early on success)
LIFT_MAX_FAIL = 3     # failures at one group order before that base size stops


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q): order 2(q+1)(q^2+1)."""
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
    """W(q) for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(min(d - 1, 16), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _pg_fallback(d):
    """Projective plane incidence PG(2, q) for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(min(d - 1, 16), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bipartition(n, adj):
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
    """Add edges between deficient opposite-side vertices. Keeps bipartiteness and diameter."""
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
    return n, edges


def _group_options(G, rng):
    """Candidate (m, k, r) with Z_m x|_r Z_k of order G: cyclic, direct and semidirect products."""
    opts = [(G, 1, 1)]
    for k in range(2, 13):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        opts.append((m, k, 1))
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if rs:
            for _ in range(2):
                opts.append((m, k, rng.choice(rs)))
    return opts


def _lift_ladder(d, D, seed, best_n, consider, deadline, rng):
    """Round-robin over base sizes kb; for each, climb the group order G while C finds valid lifts."""
    kbs = [1, 2, 3, 4]
    st = {kb: {"G": max(2, best_n // (2 * kb) + 1), "fail": 0, "dead": False} for kb in kbs}
    calls = 0
    turn = 0
    while True:
        left = deadline - time.monotonic()
        if left < 0.5:
            break
        alive = [kb for kb in kbs if not st[kb]["dead"]]
        if not alive:
            break
        kb = alive[turn % len(alive)]
        turn += 1
        s = st[kb]
        G = s["G"]
        if G > 2400:
            s["dead"] = True
            continue
        m, k, r = rng.choice(_group_options(G, rng))
        budget = min(LIFT_SLICE, left - 0.3)
        if budget < 0.5:
            break
        calls += 1
        n, e = 0, []
        try:
            out = lib.run_c(LIFT_C_SOURCE,
                            [d, D, seed * 1000 + calls, f"{budget:.2f}", m, k, r, kb],
                            timeout=budget + 5.0)
            n, e = lib.parse_graph_text(out)
        except Exception:
            n, e = 0, []
        if n > 0 and lib.is_valid(n, e, d, D):
            consider(n, e)
            s["G"] = G + 1
            s["fail"] = 0
        else:
            s["fail"] += 1
            if s["fail"] >= LIFT_MAX_FAIL:
                s["dead"] = True


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Calibration: D = 3 with d - 1 a prime power gives the Moore-optimal incidence graph.
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

    # Cheap structured fallbacks (both saturated, so degree is spent).
    try:
        if D == 3:
            pg = _pg_fallback(d)
            if pg is not None:
                consider(*_saturate_edges(pg[0], pg[1], d, rng))
        if D >= 4:
            gq = _best_gq(d)
            if gq is not None:
                consider(*_saturate_edges(gq[0], gq[1], d, rng))
    except Exception:
        pass

    # Main search: voltage lifts over small non-cyclic groups, annealed in C.
    if D >= 2 and d >= 3:
        deadline = start + 0.85 * tl - 1.0
        try:
            _lift_ladder(d, D, seed, best_n, consider, deadline, rng)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
