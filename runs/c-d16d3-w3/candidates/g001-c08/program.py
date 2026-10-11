import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: insertion annealing for bipartite graphs with max degree d and
# diameter D. It starts from a valid graph, adds one vertex with degree 0, and
# runs simulated annealing over degree-preserving edge switches, edge additions
# and edge removals. Cost = ordered pairs at distance > D. Each time cost reaches
# 0 it saves the graph and adds another vertex. It prints the largest valid
# graph found before its CPU-time budget runs out.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXDEG 40

static int N, DEGMAX, DIAM;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int col[MAXN];
static int side[2][MAXN];
static int nside[2];
static int seenv[MAXN];
static int qbuf[MAXN];
static uint64_t rs = 88172645463325252ULL;

static int bestN = 0;
static int bdeg[MAXN];
static int badj[MAXN][MAXDEG];

typedef struct { int type, u, v; } Op;   /* type 0 = add edge, 1 = delete edge */
static Op ops[8];
static int nops = 0;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}
static void arc_del(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) { adj[u][i] = adj[u][--deg[u]]; return; }
    }
}
static void edge_add(int u, int v) { adj[u][deg[u]++] = v; adj[v][deg[v]++] = u; }
static void edge_del(int u, int v) { arc_del(u, v); arc_del(v, u); }

static void do_add(int u, int v) { edge_add(u, v); ops[nops].type = 0; ops[nops].u = u; ops[nops].v = v; nops++; }
static void do_del(int u, int v) { edge_del(u, v); ops[nops].type = 1; ops[nops].u = u; ops[nops].v = v; nops++; }
static void undo(void) {
    while (nops > 0) {
        Op o = ops[--nops];
        if (o.type == 0) edge_del(o.u, o.v);
        else edge_add(o.u, o.v);
    }
}

static void rebuild_sides(void) {
    nside[0] = nside[1] = 0;
    for (int u = 0; u < N; u++) side[col[u]][nside[col[u]]++] = u;
}

static void add_vertex(void) {
    int c = (nside[0] <= nside[1]) ? 0 : 1;
    col[N] = c;
    deg[N] = 0;
    N++;
    rebuild_sides();
}

/* Number of ordered pairs (s, t) with dist(s, t) > DIAM (unreachable counts). */
static long long cost_fn(void) {
    long long bad = 0;
    for (int s = 0; s < N; s++) {
        memset(seenv, 0, sizeof(int) * (size_t)N);
        int head = 0, tail = 0;
        qbuf[tail++] = s;
        seenv[s] = 1;
        int fend = tail;
        for (int lev = 0; lev < DIAM && head < tail; lev++) {
            while (head < fend) {
                int u = qbuf[head++];
                for (int i = 0; i < deg[u]; i++) {
                    int v = adj[u][i];
                    if (!seenv[v]) { seenv[v] = 1; qbuf[tail++] = v; }
                }
            }
            fend = tail;
        }
        bad += N - tail;
    }
    return bad;
}

/* Random move: switch (degree preserving), add, or remove. Returns 0 if no move was made. */
static int propose(void) {
    nops = 0;
    if (nside[0] < 1 || nside[1] < 1) return 0;
    double r = rndu();
    if (r < 0.6) {
        int u = side[0][rndint(nside[0])];
        int w = side[0][rndint(nside[0])];
        if (u == w || deg[u] == 0 || deg[w] == 0) return 0;
        int v = adj[u][rndint(deg[u])];
        int z = adj[w][rndint(deg[w])];
        if (v == z || has_edge(u, z) || has_edge(w, v)) return 0;
        do_del(u, v);
        do_del(w, z);
        do_add(u, z);
        do_add(w, v);
        return 1;
    } else if (r < 0.85) {
        int u = side[0][rndint(nside[0])];
        int v = side[1][rndint(nside[1])];
        if (deg[u] >= DEGMAX || deg[v] >= DEGMAX || has_edge(u, v)) return 0;
        do_add(u, v);
        return 1;
    } else {
        int u = side[0][rndint(nside[0])];
        if (deg[u] == 0) return 0;
        int v = adj[u][rndint(deg[u])];
        do_del(u, v);
        return 1;
    }
}

static void save_best(void) {
    bestN = N;
    for (int u = 0; u < N; u++) {
        bdeg[u] = deg[u];
        memcpy(badj[u], adj[u], sizeof(int) * (size_t)deg[u]);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    DEGMAX = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    if (DEGMAX < 1 || DEGMAX > MAXDEG || DIAM < 1) { printf("0 0\n"); return 0; }

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n >= MAXN - 64 || m < 0) { printf("0 0\n"); return 0; }
    N = n;
    for (int u = 0; u < N; u++) deg[u] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) { printf("0 0\n"); return 0; }
        if (deg[u] >= DEGMAX || deg[v] >= DEGMAX || has_edge(u, v)) { printf("0 0\n"); return 0; }
        edge_add(u, v);
    }

    /* Bipartition by BFS; the input must be bipartite. */
    for (int u = 0; u < N; u++) col[u] = -1;
    int okb = 1;
    for (int s = 0; s < N && okb; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        qbuf[t++] = s;
        while (h < t && okb) {
            int u = qbuf[h++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) { col[v] = 1 - col[u]; qbuf[t++] = v; }
                else if (col[v] == col[u]) okb = 0;
            }
        }
    }
    if (!okb) { printf("0 0\n"); return 0; }
    rebuild_sides();
    if (nside[0] == 0 || nside[1] == 0) { printf("0 0\n"); return 0; }

    long long cost = cost_fn();
    if (cost != 0) { printf("0 0\n"); return 0; }

    clock_t t0 = clock();
    double frac = 0.0, T = 1.0;
    long long it = 0;
    for (;;) {
        if (cost == 0) {
            save_best();
            if (N + 1 >= MAXN) break;
            add_vertex();
            cost = cost_fn();
            continue;
        }
        if ((it & 63) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= budget) break;
            frac = el / budget;
        }
        it++;
        T = 1.5 * (1.0 - frac) + 0.15;
        if (!propose()) continue;
        long long c2 = cost_fn();
        long long delta = c2 - cost;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) cost = c2;
        else undo();
    }

    int M = 0;
    for (int u = 0; u < bestN; u++)
        for (int i = 0; i < bdeg[u]; i++)
            if (badj[u][i] > u) M++;
    printf("%d %d\n", bestN, M);
    for (int u = 0; u < bestN; u++)
        for (int i = 0; i < bdeg[u]; i++)
            if (badj[u][i] > u) printf("%d %d\n", u, badj[u][i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# A-side: a multiset SA of points. Each entry P gets a new vertex joined to all
#         q+1 lines through P. Every line holds <= s entries of SA.
# B-side: a multiset SB of lines, symmetric.
#
# Any diameter-3 check passes for any such multisets. For s = 2 (d = 16, q = 13)
# a repeated point blocks every other point on its lines, so the multiset family
# reduces to arcs with at most q+1 = 14 entries per side. That is why 394 is the
# family's ceiling for d = 16. The C insertion search below is the step meant to
# go past it.
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
    """True if every target t is hit by <= s entries of S (repeats counted), where entry x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _multi_side(m, s, nbr, rng, deadline):
    """Iterated greedy over multisets: choose entries (repeats allowed) so every target is hit <= s times."""
    order = list(range(m))

    def fill(S, load):
        rng.shuffle(order)
        for x in order:
            nb = nbr[x]
            while all(load[t] < s for t in nb):
                S.append(x)
                for t in nb:
                    load[t] += 1
        return S

    cur = fill([], [0] * m)
    best = list(cur)
    while time.monotonic() < deadline:
        S = list(cur)
        load = [0] * m
        for x in S:
            for t in nbr[x]:
                load[t] += 1
        for _ in range(min(rng.randint(1, 3), len(S))):
            i = rng.randrange(len(S))
            x = S.pop(i)
            for t in nbr[x]:
                load[t] -= 1
        S = fill(S, load)
        if len(S) >= len(cur):
            cur = S
            if len(cur) > len(best):
                best = list(cur)
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA entry and one new B-vertex per SB entry."""
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
    qs = sorted((q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)), reverse=True)
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        per_side = (deadline - now) / (2 * (len(qs) - idx))
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _multi_side(m, s, point_lines, rng, time.monotonic() + per_side)
        SB = _multi_side(m, s, line_points, rng, time.monotonic() + per_side)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

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
# Simulated annealing over bi-Cayley voltage lifts (unchanged from parent).
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


# ----------------------------------------------------------------------------
# C insertion search: start from a valid graph and try to add vertices.
# ----------------------------------------------------------------------------

def _c_extend(best, d, D, seed, budget):
    """Run the C insertion annealer from `best`; return (n, edges) of its best valid graph."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"], stdin_graph=best,
                    timeout=budget + 15.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    # Phase 1: constructions (arc-extended PG graphs for D >= 3, W(q) for D >= 4).
    arc_deadline = start + 0.15 * time_limit
    if D >= 3:
        cands = _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    if D >= 4 and time.monotonic() < arc_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Phase 2: C insertion search from the best graph, unless it already meets the Moore bound.
    # For D >= 5 this phase gets less time, leaving room for the voltage annealing below.
    c_end = start + (0.45 if D >= 5 else 0.85) * time_limit
    if best_n < lib.moore_bound(d, D) and d <= 40 and time.monotonic() < c_end - 3.0:
        budget = c_end - time.monotonic() - 2.0
        try:
            n_c, e_c = _c_extend(best, d, D, seed, budget)
            consider(n_c, e_c)
        except Exception:
            pass

    # Phase 3: annealed group voltage lifts (remaining time).
    deadline = start + 0.85 * time_limit
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
