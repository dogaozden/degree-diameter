import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: twin-cloning blow-up.
#
# A clone x of a vertex v (same neighbourhood, same side) keeps the diameter
# exactly: d(x, w) = d(v, w) for w != x, and d(x, v) = 2. It only raises the
# degree of each neighbour of v by one. The engine greedily clones random
# vertices whose neighbours all have spare degree, restarting until the CPU
# budget runs out, and prints the largest blow-up it found.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define DMAX 128

static int badj[MAXN][DMAX];
static int bdeg[MAXN];
static int bn;
static int adj[MAXN][DMAX];
static int deg[MAXN];
static int N;
static int DEG;
static int bestadj[MAXN][DMAX];
static int bestdeg[MAXN];
static int bestN = -1;
static int cand[MAXN];

static void restore(void) {
    N = bn;
    for (int v = 0; v < bn; v++) {
        deg[v] = bdeg[v];
        memcpy(adj[v], badj[v], sizeof(int) * (size_t)bdeg[v]);
    }
}

static int can_clone(int v) {
    if (deg[v] == 0) return 0;
    for (int i = 0; i < deg[v]; i++)
        if (deg[adj[v][i]] >= DEG) return 0;
    return 1;
}

static void clone_vertex(int v) {
    int x = N++;
    deg[x] = deg[v];
    for (int i = 0; i < deg[v]; i++) {
        int u = adj[v][i];
        adj[x][i] = u;
        adj[u][deg[u]++] = x;
    }
}

static void greedy(void) {
    restore();
    while (N < MAXN - 1) {
        int cnt = 0;
        for (int v = 0; v < N; v++)
            if (can_clone(v)) cand[cnt++] = v;
        if (cnt == 0) break;
        clone_vertex(cand[rand() % cnt]);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    unsigned seed = (unsigned)strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (d < 1 || d > DMAX - 1) { printf("0 0\n"); return 0; }
    DEG = d;
    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXN / 4 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    memset(bdeg, 0, sizeof bdeg);
    for (int k = 0; k < m; k++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || u >= n || v < 0 || v >= n || u == v || bdeg[u] >= d || bdeg[v] >= d) {
            printf("0 0\n");
            return 0;
        }
        badj[u][bdeg[u]++] = v;
        badj[v][bdeg[v]++] = u;
    }
    bn = n;

    clock_t t0 = clock();
    int runs = 0;
    for (;;) {
        srand((unsigned)(seed * 2654435761u + (unsigned)runs * 40503u + 12345u));
        greedy();
        runs++;
        if (N > bestN) {
            bestN = N;
            for (int v = 0; v < N; v++) {
                bestdeg[v] = deg[v];
                memcpy(bestadj[v], adj[v], sizeof(int) * (size_t)deg[v]);
            }
        }
        if ((double)(clock() - t0) / CLOCKS_PER_SEC >= budget) break;
    }

    int me = 0;
    for (int v = 0; v < bestN; v++)
        for (int i = 0; i < bestdeg[v]; i++)
            if (bestadj[v][i] > v) me++;
    printf("%d %d\n", bestN, me);
    for (int v = 0; v < bestN; v++)
        for (int i = 0; i < bestdeg[v]; i++)
            if (bestadj[v][i] > v) printf("%d %d\n", v, bestadj[v][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
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


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
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


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A-vertex per point of S (joined to its lines) and a new B-vertex per line of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_candidates(d, deadline, rng):
    """Return (n, edges) arc-extended PG(2,q) graphs for every prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [_greedy_arc(m, s, pl, lp, rng, 40, deadline)]
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if S and _loads_ok(S, s, m, pl, lp):
            out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# Other diameter-3 bases: Araujo-Lopez graphs and generalized quadrangles.
# ----------------------------------------------------------------------------

def _al_candidates(d):
    """Araujo-Lopez graphs for the two largest usable prime powers q with q + 2 <= d."""
    qs = [q for q in range(3, d - 1) if lib.is_prime_power(q)]
    out = []
    for q in sorted(qs, reverse=True)[:2]:
        try:
            n, e = lib.araujo_lopez_graph(q)
        except (ValueError, KeyError):
            continue
        if lib.max_degree(n, e) <= d:
            out.append((n, e))
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


# ----------------------------------------------------------------------------
# Twin-cloning call into the C engine.
# ----------------------------------------------------------------------------

def _clone_grow(n, edges, d, D, seed, budget):
    """Run the C clone blow-up on (n, edges); return (n, edges) or None on failure."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, budget], stdin_graph=(n, edges),
                        timeout=budget + 60.0)
        return lib.parse_graph_text(out)
    except (RuntimeError, ValueError):
        return None


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (from parent).
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
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.8 * time_limit
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

    # Collect diameter-valid bases, then blow each one up by twin cloning.
    bases = []
    if D >= 3:
        bases += _arc_candidates(d, t0 + 0.2 * time_limit, random.Random(seed * 7919 + d))
        bases += _al_candidates(d)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            bases.append(gq)
    bases.sort(key=lambda t: -t[0])

    budget = max(0.2, min(2.0, 0.03 * time_limit))
    clone_end = t0 + 0.45 * time_limit
    for i, (n_b, e_b) in enumerate(bases):
        if time.monotonic() > clone_end:
            break
        consider(n_b, e_b)
        grown = _clone_grow(n_b, e_b, d, D, seed * 131 + i, budget)
        if grown is not None:
            consider(*grown)

    # Remaining time: annealed group voltage lifts. For D >= 5 use larger bases.
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
