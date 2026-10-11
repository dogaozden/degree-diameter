import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: greedy vertex insertion with ball-cover certificates.
#
# Reads a valid graph (bipartite, degree <= d, diameter <= D) and repeatedly
# inserts a new vertex w on one colour side whose neighbourhood N (opposite
# colour, degree < d, |N| <= d) covers every old vertex within distance D-1 of
# some u in N. Then every old x satisfies dist(w, x) <= D. Old distances never
# grow, so validity is kept. When no insertion works, a random spare cross edge
# is added (also valid, bipartite-preserving) to change the spare-capacity
# pattern. Prints the largest graph reached as "n m" plus m edges.
# On any problem it prints "0 0" and the Python side keeps its own graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4096
#define MAXW 64

static int n, d, D, W;
static int *deg, *col, *adjl;
static uint64_t cur[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];
static int pool[MAXN];
static int chosen[MAXN];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }

static int pc(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int has_edge(int u, int v) {
    for (int k = 0; k < deg[u]; k++)
        if (adjl[(size_t)u * d + k] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adjl[(size_t)u * d + deg[u]++] = v;
    adjl[(size_t)v * d + deg[v]++] = u;
}

static void compute_balls(int R) {
    W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = adjl[(size_t)v * d + k];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) cur[v][w] = nxt[v][w];
    }
}

static int gain(int u, const uint64_t *cov) {
    int g = 0;
    for (int w = 0; w < W; w++) g += pc(cur[u][w] & ~cov[w]);
    return g;
}

static int covers_all(const uint64_t *cov, const uint64_t *full) {
    for (int w = 0; w < W; w++)
        if (cov[w] != full[w]) return 0;
    return 1;
}

static void augment(int R, double budget, int max_fails) {
    clock_t t0 = clock();
    int fails = 0;
    uint64_t cov[MAXW], full[MAXW];
    while (fails < max_fails && n < MAXN - 2) {
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        compute_balls(R);
        for (int w = 0; w < W; w++) full[w] = 0;
        for (int v = 0; v < n; v++) full[v >> 6] |= 1ULL << (v & 63);
        int added = 0;
        int s0 = rndi(2);
        for (int kk = 0; kk < 2 && !added; kk++) {
            int side = (kk == 0) ? s0 : 1 - s0;
            for (int att = 0; att < 4 && !added; att++) {
                int np = 0;
                for (int u = 0; u < n; u++)
                    if (col[u] == 1 - side && deg[u] < d) pool[np++] = u;
                if (np == 0) break;
                for (int i = np - 1; i > 0; i--) {
                    int j = rndi(i + 1);
                    int t = pool[i]; pool[i] = pool[j]; pool[j] = t;
                }
                for (int w = 0; w < W; w++) cov[w] = 0;
                int nc = 0;
                while (nc < d && np > 0 && !covers_all(cov, full)) {
                    int bi = -1, bg = 0;
                    for (int i = 0; i < np; i++) {
                        int g = gain(pool[i], cov);
                        if (g > bg) { bg = g; bi = i; }
                    }
                    if (bi < 0) break;
                    int u = pool[bi];
                    chosen[nc++] = u;
                    for (int w = 0; w < W; w++) cov[w] |= cur[u][w];
                    pool[bi] = pool[--np];
                }
                if (covers_all(cov, full)) {
                    int w = n++;
                    col[w] = side;
                    deg[w] = 0;
                    for (int i = 0; i < nc; i++) add_edge(chosen[i], w);
                    added = 1;
                }
            }
        }
        if (added) { fails = 0; continue; }
        fails++;
        for (int t = 0; t < 2000; t++) {
            int u = rndi(n), v = rndi(n);
            if (u != v && col[u] != col[v] && deg[u] < d && deg[v] < d && !has_edge(u, v)) {
                add_edge(u, v);
                break;
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || n0 > 1500 || m0 < 0 || d < 1 || D < 2) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(m0 > 0 ? m0 : 1));
    int *ev = malloc(sizeof(int) * (size_t)(m0 > 0 ? m0 : 1));
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) {
            printf("0 0\n");
            return 0;
        }
    }

    n = n0;
    deg = calloc(MAXN, sizeof(int));
    col = malloc(sizeof(int) * MAXN);
    adjl = malloc(sizeof(int) * (size_t)MAXN * (size_t)d);
    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    /* 2-colouring by BFS (input is bipartite). */
    for (int v = 0; v < n; v++) col[v] = -1;
    int *q = malloc(sizeof(int) * MAXN);
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int u = q[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adjl[(size_t)u * d + k];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    q[qt++] = v;
                }
            }
        }
    }

    augment(D - 1, budget, 400);

    long m = 0;
    for (int v = 0; v < n; v++) m += deg[v];
    m /= 2;
    printf("%d %ld\n", n, m);
    for (int u = 0; u < n; u++)
        for (int k = 0; k < deg[u]; k++) {
            int v = adjl[(size_t)u * d + k];
            if (u < v) printf("%d %d\n", u, v);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Old vertices
# have degree q+1, so spare s = d - q - 1.
#   A-side: a point set SA; each SA point gets a new vertex joined to its q+1
#           lines. Each line may hold <= s points of SA.
#   B-side: a line set SB; each j in SB gets a new vertex joined to its q+1
#           points. Each point may lie on <= s lines of SB.
# The sides are independent, so they are maximized separately.
# Order is 2(q^2+q+1) + |SA| + |SB|. Diameter stays 3.
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
    """True if every target is hit by <= s elements of S, element x hitting nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice of elements so every target is hit by <= s of them."""
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
    """Old PG incidence plus one A-vertex per SA point and one B-vertex per SB line."""
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
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
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


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (D = 4 baseline).
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
# Simulated annealing over bi-Cayley voltage lifts (for D >= 4 cases).
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
# build
# ----------------------------------------------------------------------------

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

    # Stage 1: arc-extended projective plane graphs (diameter 3, valid for D >= 3).
    if D >= 3:
        cands = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands[:3]:
            consider(n_c, e_c)

    # Stage 2: generalized quadrangle baseline for D >= 4.
    if D >= 4 and time.monotonic() < start + 0.25 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Stage 3: C greedy vertex insertion on the best graph so far.
    # For D <= 3 it gets most of the budget; for larger D it gets a smaller share.
    frac = 0.75 if D <= 3 else 0.30
    c_budget = frac * time_limit - (time.monotonic() - start)
    if c_budget >= 0.5:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                            stdin_graph=best, timeout=c_budget + 15.0)
            n_c, e_c = lib.parse_graph_text(out)
            if n_c > 0 and e_c:
                consider(n_c, e_c)
        except Exception:
            pass  # keep the Python graph if the C engine fails

    # Stage 4: annealed group voltage lifts for the remaining time when D >= 4.
    if D >= 4:
        search_end = start + 0.90 * time_limit
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < search_end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, search_end, iters=400)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
