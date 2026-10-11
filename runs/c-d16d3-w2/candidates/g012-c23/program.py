import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine. It starts from a valid bipartite graph of max degree d and
# diameter <= D, adds one vertex at a time, and anneals over bipartite-preserving
# moves (double-edge swaps, edge add, edge remove) to drive the number of pairs
# at distance > D to zero. On failure it restores the last valid snapshot and
# retries with a fresh random vertex and fresh annealing.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define EXTRA 120
#define ROUND_ITERS 20000

static int DEG, DIAM, NCAP, N;
static int *dg, *sd, *nb;
static unsigned char *am;
static uint64_t *R0, *R1;
static int WCAP;
static uint64_t rs = 88172645463325252ull;
static double T_LIMIT;
static clock_t T_START;
static long long cur_cost;
static int *bu, *bv, *bs;
static int bestN, bm, have_best = 0;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - T_START) / CLOCKS_PER_SEC; }

static int has_edge(int u, int v) { return am[(size_t)u * NCAP + v]; }

static void add_edge(int u, int v) {
    am[(size_t)u * NCAP + v] = 1;
    am[(size_t)v * NCAP + u] = 1;
    nb[(size_t)u * DEG + dg[u]++] = v;
    nb[(size_t)v * DEG + dg[v]++] = u;
}

static void del_half(int u, int v) {
    int k;
    for (k = 0; k < dg[u]; k++) if (nb[(size_t)u * DEG + k] == v) break;
    nb[(size_t)u * DEG + k] = nb[(size_t)u * DEG + dg[u] - 1];
    dg[u]--;
}

static void del_edge(int u, int v) {
    am[(size_t)u * NCAP + v] = 0;
    am[(size_t)v * NCAP + u] = 0;
    del_half(u, v);
    del_half(v, u);
}

static int popc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

/* Number of unordered pairs at distance > DIAM (unreachable counts). */
static long long cost_bad(void) {
    int W = (N + 63) >> 6;
    uint64_t *cur = R0, *nxt = R1;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ull << (v & 63);
    for (int step = 0; step < DIAM; step++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            uint64_t *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(uint64_t) * W);
            for (int i = 0; i < dg[v]; i++) {
                const uint64_t *cu = cur + (size_t)nb[(size_t)v * DEG + i] * W;
                for (int w = 0; w < W; w++) o[w] |= cu[w];
            }
            for (int w = 0; w < W; w++) if (o[w] != c[w]) changed = 1;
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc(cur[(size_t)v * W + w]);
        tot += N - pc;
    }
    return tot / 2;
}

static int color_sides(int *q) {
    for (int v = 0; v < N; v++) sd[v] = -1;
    for (int s = 0; s < N; s++) {
        if (sd[s] >= 0) continue;
        sd[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int i = 0; i < dg[u]; i++) {
                int w = nb[(size_t)u * DEG + i];
                if (sd[w] < 0) { sd[w] = 1 - sd[u]; q[t++] = w; }
                else if (sd[w] == sd[u]) return 0;
            }
        }
    }
    return 1;
}

static int pick_side(int s) {
    for (int t = 0; t < 2000; t++) {
        int a = rndi(N);
        if (sd[a] == s && dg[a] > 0) return a;
    }
    return -1;
}

static int accept(long long delta, double T) {
    if (delta <= 0) return 1;
    return rndu() < exp(-(double)delta / T);
}

static void snapshot(void) {
    bm = 0;
    for (int u = 0; u < N; u++)
        for (int i = 0; i < dg[u]; i++) {
            int v = nb[(size_t)u * DEG + i];
            if (v > u) { bu[bm] = u; bv[bm] = v; bm++; }
        }
    for (int v = 0; v < N; v++) bs[v] = sd[v];
    bestN = N;
    have_best = 1;
}

static void restore(void) {
    for (int u = 0; u < N; u++) {
        dg[u] = 0;
        for (int v = 0; v < N; v++) am[(size_t)u * NCAP + v] = 0;
    }
    N = bestN;
    for (int v = 0; v < N; v++) sd[v] = bs[v];
    for (int i = 0; i < bm; i++) add_edge(bu[i], bv[i]);
    cur_cost = cost_bad();
}

static void anneal_round(long long iters, double T0, double T1) {
    for (long long it = 0; it < iters && cur_cost != 0; it++) {
        if ((it & 127) == 0 && elapsed() > T_LIMIT) return;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        double r = rndu();
        if (r < 0.6) {
            int a = pick_side(0), c = pick_side(0);
            if (a < 0 || c < 0 || a == c) continue;
            int b = nb[(size_t)a * DEG + rndi(dg[a])];
            int e = nb[(size_t)c * DEG + rndi(dg[c])];
            if (b == e || has_edge(a, e) || has_edge(c, b)) continue;
            del_edge(a, b); del_edge(c, e);
            add_edge(a, e); add_edge(c, b);
            long long nc = cost_bad();
            if (accept(nc - cur_cost, T)) cur_cost = nc;
            else {
                del_edge(a, e); del_edge(c, b);
                add_edge(a, b); add_edge(c, e);
            }
        } else if (r < 0.85) {
            int x = (rndu() < 0.5) ? N - 1 : rndi(N);
            if (dg[x] >= DEG) continue;
            int y = -1;
            for (int t = 0; t < 40; t++) {
                int z = rndi(N);
                if (sd[z] != sd[x] && dg[z] < DEG && !has_edge(x, z)) { y = z; break; }
            }
            if (y < 0) continue;
            add_edge(x, y);
            long long nc = cost_bad();
            if (accept(nc - cur_cost, T)) cur_cost = nc;
            else del_edge(x, y);
        } else {
            int a = pick_side(0);
            if (a < 0) continue;
            int b = nb[(size_t)a * DEG + rndi(dg[a])];
            del_edge(a, b);
            long long nc = cost_bad();
            if (accept(nc - cur_cost, T)) cur_cost = nc;
            else add_edge(a, b);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], 0, 10) * 0x9E3779B97F4A7C15ull + 1;
    if (!rs) rs = 1;
    T_LIMIT = atof(argv[4]);
    T_START = clock();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0) { printf("0 0\n"); return 0; }
    NCAP = n0 + EXTRA;
    WCAP = (NCAP + 63) >> 6;
    dg = calloc(NCAP, sizeof(int));
    sd = calloc(NCAP, sizeof(int));
    nb = calloc((size_t)NCAP * DEG + 1, sizeof(int));
    am = calloc((size_t)NCAP * NCAP, 1);
    R0 = calloc((size_t)NCAP * WCAP, sizeof(uint64_t));
    R1 = calloc((size_t)NCAP * WCAP, sizeof(uint64_t));
    bu = calloc((size_t)NCAP * DEG + 1, sizeof(int));
    bv = calloc((size_t)NCAP * DEG + 1, sizeof(int));
    bs = calloc(NCAP, sizeof(int));
    int *q = calloc(NCAP + 1, sizeof(int));

    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (has_edge(u, v) || dg[u] >= DEG || dg[v] >= DEG) continue;
        add_edge(u, v);
    }
    if (!color_sides(q)) { printf("0 0\n"); return 0; }

    cur_cost = cost_bad();
    if (cur_cost == 0) snapshot();

    while (elapsed() < T_LIMIT) {
        if (cur_cost == 0) {
            snapshot();
            if (N >= NCAP) break;
            sd[N] = rndi(2);
            dg[N] = 0;
            N++;
            cur_cost = cost_bad();
        }
        anneal_round(ROUND_ITERS, 1.0, 0.05);
        if (cur_cost != 0 && have_best && elapsed() < T_LIMIT) restore();
    }

    if (!have_best) snapshot();
    printf("%d %d\n", bestN, bm);
    for (int i = 0; i < bm; i++) printf("%d %d\n", bu[i], bv[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# A-side: a set SA of points. Each SA point P gets a new vertex joined to all
#         q+1 lines through P. Constraint: every line holds <= s points of SA.
# B-side: a set SB of lines. Each j in SB gets a new vertex joined to all
#         q+1 points on j. Constraint: every point lies on <= s lines of SB.
# ----------------------------------------------------------------------------

_LS_ITERS = 30000


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
    """Randomized greedy: choose elements x so that every target is hit by <= s chosen elements."""
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


def _local_search(m, s, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the same load-constrained set problem."""
    if s < 1:
        return list(S)
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= s:
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
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
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for q in qs:
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

        SA = _local_search(m, s, point_lines, SA, rng, deadline, _LS_ITERS)
        SB = _local_search(m, s, line_points, SB, rng, deadline, _LS_ITERS)

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
# ----------------------------------------------------------------------------

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


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (Python fallback).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    arc_deadline = start + 0.15 * time_limit
    deadline = start + 0.9 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Arc-extended projective plane graphs (diameter 3, valid for all D >= 3).
    if D >= 3:
        cands = _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: the C engine extends the best valid graph found so far.
    # It gets most of the budget; the remaining time goes to Python voltage lifts.
    if D >= 3 and d >= 2:
        elapsed = time.monotonic() - start
        c_budget = 0.8 * time_limit - elapsed
        if c_budget > 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                stdin_graph=best, timeout=c_budget + 5.0)
                n_c, e_c = lib.parse_graph_text(out)
                if n_c >= 1:
                    consider(n_c, e_c)
            except (RuntimeError, ValueError):
                pass

    # Voltage-lift annealing with the remaining time.
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
