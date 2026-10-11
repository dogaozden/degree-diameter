import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: greedy vertex insertion with ball-cover certificates.
#
# Given a valid bipartite graph, R = D-1. A new vertex w on one colour side,
# joined to a set N of opposite-side vertices with spare degree, is valid when
# every existing vertex lies within distance R of some member of N. Adding a
# vertex never increases an old distance, so validity is preserved. Random
# cross edges between spare vertices are added as perturbations; they also
# keep validity. The engine outputs the largest graph it reached.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

typedef uint64_t u64;

static int N, DEG, R, CAP, WMAX, W;
static int *deg, *nb, *col, *used, *chosen;
static u64 *ballA, *ballB, *cov;
static long ecount;
static u64 rs = 88172645463325252ULL;

static unsigned rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return (unsigned)(rs >> 16);
}

static int pc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (nb[(size_t)u * DEG + i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    nb[(size_t)u * DEG + deg[u]++] = v;
    nb[(size_t)v * DEG + deg[v]++] = u;
    ecount++;
}

static void compute_balls(void) {
    W = (N + 63) / 64;
    memset(ballA, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++) ballA[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < N; v++) {
            u64 *dst = ballB + (size_t)v * W;
            u64 *src = ballA + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < deg[v]; i++) {
                int u = nb[(size_t)v * DEG + i];
                u64 *s2 = ballA + (size_t)u * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        u64 *t = ballA; ballA = ballB; ballB = t;
    }
}

static int is_full(const u64 *c) {
    for (int w = 0; w < W; w++) {
        u64 want = (w == W - 1 && (N % 64)) ? ((1ULL << (N % 64)) - 1) : ~0ULL;
        if ((c[w] & want) != want) return 0;
    }
    return 1;
}

static int try_insert(int s) {
    memset(cov, 0, sizeof(u64) * (size_t)W);
    memset(used, 0, sizeof(int) * (size_t)N);
    int nc = 0;
    while (nc < DEG && !is_full(cov)) {
        int best = -1, bestg = 0, ties = 0;
        for (int u = 0; u < N; u++) {
            if (col[u] == s || used[u] || deg[u] >= DEG) continue;
            const u64 *bu = ballA + (size_t)u * W;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc(bu[w] & ~cov[w]);
            if (g > bestg) { bestg = g; best = u; ties = 1; }
            else if (g == bestg && g > 0) {
                ties++;
                if (rnd() % (unsigned)ties == 0) best = u;
            }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nc++] = best;
        const u64 *bb = ballA + (size_t)best * W;
        for (int w = 0; w < W; w++) cov[w] |= bb[w];
    }
    if (!is_full(cov)) return 0;
    int w = N++;
    col[w] = s;
    deg[w] = 0;
    for (int i = 0; i < nc; i++) add_edge(chosen[i], w);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= (seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    DEG = d;
    R = D - 1;
    if (R < 0) R = 0;
    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || DEG < 1) {
        printf("1 0\n");
        return 0;
    }
    CAP = 3 * n0 + 256;
    WMAX = (CAP + 63) / 64;
    deg = calloc(CAP, sizeof(int));
    nb = calloc((size_t)CAP * DEG, sizeof(int));
    col = calloc(CAP, sizeof(int));
    used = calloc(CAP, sizeof(int));
    chosen = calloc(DEG + 1, sizeof(int));
    ballA = calloc((size_t)CAP * WMAX, sizeof(u64));
    ballB = calloc((size_t)CAP * WMAX, sizeof(u64));
    cov = calloc(WMAX + 1, sizeof(u64));
    int *q = calloc(CAP, sizeof(int));

    N = n0;
    ecount = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (deg[u] >= DEG || deg[v] >= DEG || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int x = q[h++];
            for (int i = 0; i < deg[x]; i++) {
                int y = nb[(size_t)x * DEG + i];
                if (col[y] == -1) { col[y] = 1 - col[x]; q[t++] = y; }
            }
        }
    }

    clock_t t0 = clock();
    int fails = 0;
    while (1) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (el >= tl) break;
        if (fails > 4000) break;
        compute_balls();
        int ok = 0;
        if (N < CAP) {
            int first = (int)(rnd() & 1u);
            ok = try_insert(first);
            if (!ok) ok = try_insert(1 - first);
        }
        if (ok) { fails = 0; continue; }
        fails++;
        for (int t = 0; t < 50; t++) {
            int a = (int)(rnd() % (unsigned)N), b = (int)(rnd() % (unsigned)N);
            if (col[a] == col[b] || deg[a] >= DEG || deg[b] >= DEG || has_edge(a, b)) continue;
            add_edge(a, b);
            break;
        }
    }

    printf("%d %ld\n", N, ecount);
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = nb[(size_t)v * DEG + i];
            if (u > v) printf("%d %d\n", v, u);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so spare capacity s = d - q - 1. A point set S with at most s points of S on
# each line, and at most s lines indexed by S through each point, gives a
# valid extension: one new A-vertex per P in S (joined to lines through P) and
# one new B-vertex per j in S (joined to points on line j).
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
    for t, j in enumerate(S):  # S is also a set of line indices (same vectors)
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
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 4).
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
    tl = float(time_limit)
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

    # Stage 1: algebraic constructions.
    if D >= 3:
        arcs = _arc_extensions(d, start + 0.08 * tl, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < start + 0.3 * tl:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Calibration cases already at the Moore bound return immediately.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Stage 2: annealed group voltage lifts (only for D >= 4).
    if D >= 4:
        anneal_end = start + 0.3 * tl
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

    # Stage 3: C greedy vertex insertion with ball-cover certificates,
    # started from the best valid graph found so far.
    c_budget = start + 0.85 * tl - time.monotonic()
    if D >= 2 and c_budget > 0.5:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                            stdin_graph=best, timeout=c_budget + 2)
            n_c, e_c = lib.parse_graph_text(out)
            consider(n_c, e_c)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
