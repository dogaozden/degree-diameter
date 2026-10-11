import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: greedy vertex insertion with ball-cover certificates.
#
# Input: a valid graph (bipartite, max degree d, diameter <= D) on stdin.
# A new vertex w of colour c, joined to a set N of colour 1-c vertices, is
# within distance D of every old vertex x whenever x lies in the (D-1)-ball of
# some u in N. Adding a vertex never increases old distances, and cross-colour
# edges keep bipartiteness and only shorten paths, so the graph stays valid at
# every step. When no full cover exists, the engine adds a random spare
# cross-colour edge to change the spare-capacity pattern.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAX_ADD 1500

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int dmax, R, n, cap, W;
static int *adjv, *degv, *colv, *chosen;
static char *used;
static uint64_t *balls, *tmpb, *covered, *fullm;

static int has_edge(int u, int v) {
    for (int k = 0; k < degv[u]; k++)
        if (adjv[u * dmax + k] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adjv[u * dmax + degv[u]++] = v;
    adjv[v * dmax + degv[v]++] = u;
}

static void compute_balls(void) {
    for (int v = 0; v < n; v++) {
        uint64_t *bv = balls + (size_t)v * W;
        memset(bv, 0, (size_t)W * sizeof(uint64_t));
        bv[v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < R; it++) {
        memcpy(tmpb, balls, (size_t)n * W * sizeof(uint64_t));
        for (int v = 0; v < n; v++) {
            uint64_t *bv = balls + (size_t)v * W;
            for (int k = 0; k < degv[v]; k++) {
                const uint64_t *bu = tmpb + (size_t)adjv[v * dmax + k] * W;
                for (int w = 0; w < W; w++) bv[w] |= bu[w];
            }
        }
    }
}

/* Greedy cover for a new vertex of colour `side`. Returns number of chosen
   neighbours if the whole vertex set is covered, else -1. */
static int try_insert(int side) {
    int start = (int)(rnd() % (uint64_t)n);
    memset(covered, 0, (size_t)W * sizeof(uint64_t));
    memset(used, 0, (size_t)n);
    int k = 0;
    while (k < dmax) {
        int best = -1, bestg = 0;
        for (int t = 0; t < n; t++) {
            int u = start + t;
            if (u >= n) u -= n;
            if (colv[u] == side || degv[u] >= dmax || used[u]) continue;
            const uint64_t *bu = balls + (size_t)u * W;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(bu[w] & ~covered[w]);
            if (g > bestg) {
                bestg = g;
                best = u;
            }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[k++] = best;
        const uint64_t *bb = balls + (size_t)best * W;
        for (int w = 0; w < W; w++) covered[w] |= bb[w];
        int full = 1;
        for (int w = 0; w < W; w++) {
            if (covered[w] != fullm[w]) {
                full = 0;
                break;
            }
        }
        if (full) return k;
    }
    return -1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;
    dmax = d;
    R = DD - 1;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    if (n0 <= 0 || dmax < 1 || R < 1) {
        printf("0 0\n");
        return 0;
    }
    cap = n0 + MAX_ADD;
    W = (cap + 63) / 64;
    adjv = malloc(sizeof(int) * (size_t)cap * dmax);
    degv = calloc((size_t)cap, sizeof(int));
    colv = malloc(sizeof(int) * (size_t)cap);
    chosen = malloc(sizeof(int) * (size_t)(dmax + 1));
    used = malloc((size_t)cap);
    balls = malloc(sizeof(uint64_t) * (size_t)cap * W);
    tmpb = malloc(sizeof(uint64_t) * (size_t)cap * W);
    covered = malloc(sizeof(uint64_t) * (size_t)W);
    fullm = malloc(sizeof(uint64_t) * (size_t)W);
    int *stack = malloc(sizeof(int) * (size_t)cap);

    n = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (degv[u] >= dmax || degv[v] >= dmax) continue;
        add_edge(u, v);
    }

    for (int v = 0; v < n; v++) colv[v] = -1;
    for (int s = 0; s < n; s++) {
        if (colv[s] >= 0) continue;
        colv[s] = 0;
        int sp = 0;
        stack[sp++] = s;
        while (sp) {
            int u = stack[--sp];
            for (int k = 0; k < degv[u]; k++) {
                int v = adjv[u * dmax + k];
                if (colv[v] < 0) {
                    colv[v] = 1 - colv[u];
                    stack[sp++] = v;
                }
            }
        }
    }

    clock_t t0 = clock();
    clock_t deadline = t0 + (clock_t)(tl * (double)CLOCKS_PER_SEC);

    while (clock() < deadline && n < cap) {
        memset(fullm, 0, sizeof(uint64_t) * (size_t)W);
        for (int v = 0; v < n; v++) fullm[v >> 6] |= 1ULL << (v & 63);
        compute_balls();

        int side0 = (int)(rnd() & 1ULL);
        int placed = 0;
        for (int s2 = 0; s2 < 2 && !placed; s2++) {
            int side = (s2 == 0) ? side0 : 1 - side0;
            int k = try_insert(side);
            if (k > 0) {
                int w = n++;
                colv[w] = side;
                degv[w] = 0;
                for (int i = 0; i < k; i++) add_edge(w, chosen[i]);
                placed = 1;
            }
        }
        if (!placed) {
            for (int t = 0; t < 200; t++) {
                int u = (int)(rnd() % (uint64_t)n);
                int v = (int)(rnd() % (uint64_t)n);
                if (colv[u] != colv[v] && degv[u] < dmax && degv[v] < dmax && !has_edge(u, v)) {
                    add_edge(u, v);
                    break;
                }
            }
        }
    }

    long long m = 0;
    for (int v = 0; v < n; v++) m += degv[v];
    m /= 2;
    printf("%d %lld\n", n, m);
    for (int u = 0; u < n; u++) {
        for (int k = 0; k < degv[u]; k++) {
            int v = adjv[u * dmax + k];
            if (u < v) printf("%d %d\n", u, v);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). With d >= q+1
# each old vertex has spare s = d - q - 1. Choose a point set S with every line
# holding <= s points of S and every point on <= s lines indexed by S. Add an
# A-vertex per point of S (joined to its q+1 lines) and a B-vertex per element
# of S used as a line (joined to its q+1 points).
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
    """Old PG incidence plus a new A and a new B vertex per element of S."""
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
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
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
# Simulated annealing over bi-Cayley voltage lifts (small cases).
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    def elapsed():
        return time.monotonic() - start

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

    # 1. Structured constructions (fast).
    if D >= 3:
        arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)

    if D >= 4 and elapsed() < 0.15 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # 2. Annealed voltage lifts. Useful for small graphs; brief for large ones.
    anneal_end = start + (0.35 if best_n < 120 else 0.05) * time_limit
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < anneal_end:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, anneal_end, iters=400)
        if res is not None:
            consider(res[0], res[1])

    # 3. C engine: greedy ball-cover vertex insertion from the best graph so far.
    c_end = start + 0.85 * time_limit
    budget = c_end - time.monotonic() - 2.0
    if D >= 2 and budget > 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best, timeout=budget + 3.0)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
