import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Start graphs: arc-extended projective plane incidence graphs (diameter 3),
# plus a generalized quadrangle baseline (diameter 4) and K_{d,d}.
#
# Points are 0..m-1 and lines m..2m-1 in PG(2, q). Each old vertex has spare
# s = d - q - 1. New A-vertices (joined to lines through a chosen point set SA)
# and new B-vertices (joined to points on a chosen line set SB) use that spare.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, nbr):
    """True if every target t is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements so that every target is hit by <= s chosen elements."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


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


def _start_graph(d, D, deadline, seed):
    """Best valid algebraic start graph that fits the deadline, or K_{d,d}."""
    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    if D >= 3:
        cands = _arc_extensions(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
                best = (n_c, e_c)
                break
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None and gq[0] > best[0] and lib.is_valid(gq[0], gq[1], d, D):
            best = gq
    return best


# ----------------------------------------------------------------------------
# New construction: fixed-size bipartite annealing with bitset ball evaluation.
#
# Given a valid start graph with a proper 2-colouring, add one isolated vertex
# on each side and search (simulated annealing) for a graph on the same vertex
# set with every pair at distance <= D. Cost = number of unordered pairs at
# distance > D. Moves keep the bipartition: degree-preserving edge swaps, and
# additions of edges between two deficient vertices (which never raise cost).
# Distances are computed exactly by bitset ball expansion, so each evaluation
# is cheap for n of a few hundred.
# ----------------------------------------------------------------------------

C_SA = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

typedef uint64_t u64;

static int N, NA, DEG, DIAM, W;
static int *adj, *dg, *badj, *bdg, *defA, *defB;
static u64 *bufX, *bufY;
static unsigned long long rs = 88172645463325252ULL;

static unsigned long long rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (unsigned long long)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    const int *p = adj + (size_t)a * DEG;
    for (int j = 0; j < dg[a]; j++) if (p[j] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj[(size_t)a * DEG + dg[a]++] = b;
    adj[(size_t)b * DEG + dg[b]++] = a;
}

static void drop_from(int a, int b) {
    int *p = adj + (size_t)a * DEG;
    for (int j = 0; j < dg[a]; j++) {
        if (p[j] == b) { p[j] = p[dg[a] - 1]; dg[a]--; return; }
    }
}

static void del_edge(int a, int b) { drop_from(a, b); drop_from(b, a); }

/* Number of unordered pairs at distance > DIAM. */
static long long evaluate(void) {
    u64 *cur = bufX, *nxt = bufY;
    memset(cur, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int k = 0; k < DIAM; k++) {
        for (int v = 0; v < N; v++) {
            u64 *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(u64) * (size_t)W);
            for (int j = 0; j < dg[v]; j++) {
                int u = adj[(size_t)v * DEG + j];
                const u64 *s = cur + (size_t)u * W;
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        u64 *t = cur; cur = nxt; nxt = t;
    }
    long long cnt = 0;
    size_t tot = (size_t)N * W;
    for (size_t i = 0; i < tot; i++) cnt += pc64(cur[i]);
    return ((long long)N * N - cnt) / 2;
}

static void save_best(void) {
    memcpy(badj, adj, sizeof(int) * (size_t)N * DEG);
    memcpy(bdg, dg, sizeof(int) * (size_t)N);
}

int main(int argc, char **argv) {
    if (argc < 6) return 1;
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long sd = (unsigned long long)atoll(argv[3]);
    double tl = atof(argv[4]);
    NA = atoi(argv[5]);
    DEG = d;
    rs ^= sd * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    int nin = 0, min_ = 0;
    if (scanf("%d %d", &nin, &min_) != 2) return 1;
    if (min_ < 0) min_ = 0;
    if (nin < 2 || NA < 1 || NA >= nin || DEG < 1 || DIAM < 1) return 1;
    N = nin;
    W = (N + 63) / 64;

    adj = calloc((size_t)N * DEG, sizeof(int));
    badj = calloc((size_t)N * DEG, sizeof(int));
    dg = calloc((size_t)N, sizeof(int));
    bdg = calloc((size_t)N, sizeof(int));
    defA = calloc((size_t)N, sizeof(int));
    defB = calloc((size_t)N, sizeof(int));
    bufX = calloc((size_t)N * W, sizeof(u64));
    bufY = calloc((size_t)N * W, sizeof(u64));
    if (!adj || !badj || !dg || !bdg || !defA || !defB || !bufX || !bufY) return 1;

    for (int i = 0; i < min_; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a < 0 || b < 0 || a >= N || b >= N || a == b) continue;
        if ((a < NA) == (b < NA)) continue;      /* must join A to B */
        if (a >= NA) { int t = a; a = b; b = t; }  /* a in A, b in B */
        if (dg[a] >= DEG || dg[b] >= DEG || has_edge(a, b)) continue;
        add_edge(a, b);
    }

    long long cur = evaluate();
    long long best = cur;
    save_best();

    double t0 = now();
    double T = 1.0;
    const double T0 = 1.0, T1 = 0.03;
    long long iter = 0;

    while (cur > 0) {
        if ((iter & 31) == 0) {
            double el = now() - t0;
            if (el >= tl) break;
            double f = tl > 0 ? el / tl : 1.0;
            if (f > 1.0) f = 1.0;
            T = T0 * pow(T1 / T0, f);
        }
        iter++;

        int nda = 0, ndb = 0;
        for (int v = 0; v < NA; v++) if (dg[v] < DEG) defA[nda++] = v;
        for (int v = NA; v < N; v++) if (dg[v] < DEG) defB[ndb++] = v;

        if (nda > 0 && ndb > 0 && rnd01() < 0.5) {
            int a = defA[rndint(nda)], b = defB[rndint(ndb)];
            if (!has_edge(a, b)) {
                add_edge(a, b);
                cur = evaluate();
                if (cur < best) { best = cur; save_best(); }
                continue;
            }
        }

        int a1 = rndint(NA);
        int a2 = rndint(NA);
        if (a1 == a2 || dg[a1] == 0 || dg[a2] == 0) continue;
        int b1 = adj[(size_t)a1 * DEG + rndint(dg[a1])];
        int b2 = adj[(size_t)a2 * DEG + rndint(dg[a2])];
        if (b1 == b2 || has_edge(a1, b2) || has_edge(a2, b1)) continue;

        del_edge(a1, b1);
        del_edge(a2, b2);
        add_edge(a1, b2);
        add_edge(a2, b1);
        long long nc = evaluate();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
            if (cur < best) { best = cur; save_best(); }
        } else {
            del_edge(a1, b2);
            del_edge(a2, b1);
            add_edge(a1, b1);
            add_edge(a2, b2);
        }
    }

    long m = 0;
    for (int v = 0; v < N; v++) m += bdg[v];
    m /= 2;
    printf("%d %ld\n", N, m);
    for (int v = 0; v < N; v++)
        for (int j = 0; j < bdg[v]; j++) {
            int u = badj[(size_t)v * DEG + j];
            if (v < u) printf("%d %d\n", v, u);
        }
    return 0;
}
"""


def _colours(n, edges):
    """Proper 2-colouring of the graph (isolated vertices get colour 0), or None if not bipartite."""
    adj = lib.adjacency(n, edges)
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


def _sa_extend(best, d, D, seed, budget):
    """Add one isolated vertex per side to best and run the annealer on the fixed vertex set.

    Returns a valid (n, edges) with n = best[0] + 2, or None.
    """
    n0, e0 = best
    col = _colours(n0, e0)
    if col is None:
        return None
    A = [v for v in range(n0) if col[v] == 0] + [n0]
    B = [v for v in range(n0) if col[v] == 1] + [n0 + 1]
    newid = {old: i for i, old in enumerate(A + B)}
    n = n0 + 2
    edges2 = [(newid[u], newid[v]) for u, v in e0]
    out = lib.run_c(C_SA, [d, D, seed, round(budget, 2), len(A)],
                    stdin_graph=(n, edges2), timeout=budget + 2.0)
    n2, e2 = lib.parse_graph_text(out)
    if n2 == n and lib.is_valid(n2, e2, d, D):
        return (n2, e2)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _start_graph(d, D, t0 + 0.15 * time_limit, seed)
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Annealing extension: only when the Moore bound allows one more pair of vertices.
    remaining = time_limit - (time.monotonic() - t0)
    if best[0] + 2 <= lib.moore_bound(d, D) and best[0] <= 1200 and remaining > 6:
        budget = max(0.5, min(0.85 * remaining - 1.0, remaining - 4.0))
        try:
            cand = _sa_extend(best, d, D, seed, budget)
            if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
                best = cand
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
