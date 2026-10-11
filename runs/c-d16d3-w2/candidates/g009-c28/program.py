import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New D = 3 construction: bi-Cayley (Haar-type) graphs from difference covers.
#
# For a group G of order n and a d-subset S of G, let a_x ~ b_{x s} for s in S.
# The graph is d-regular on 2n vertices. Same-side pairs are at distance <= 2
# iff S S^{-1} = G, and cross pairs are at distance <= 3 iff S^{-1} S = G.
# Both conditions hold when S S^{-1} = G and S^{-1} S = G, so the search minimises
# the number of uncovered elements of each of the two sets. The Moore bound gives
# n <= d^2 - d + 1, so the order is at most 2(d^2 - d + 1).
#
# Groups are Z_m x|_r Z_k (element (a, b) coded as a*k + b). k = 1 is cyclic.
# ----------------------------------------------------------------------------

DIFF_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 256

static int G, d;
static int mul[MAXG][MAXG];
static int iv[MAXG];
static int c1[MAXG], c2[MAXG];
static int u1, u2;
static int S[64];
static int inS[MAXG];
static uint64_t rs = 1;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* Add (sgn=+1) or remove (sgn=-1) the ordered pair (s,t) from both covering counts. */
static void upd(int s, int t, int sgn) {
    int A = mul[s][iv[t]];      /* s t^{-1} */
    int B = mul[iv[s]][t];      /* s^{-1} t */
    if (sgn > 0) {
        if (c1[A]++ == 0) u1--;
        if (c2[B]++ == 0) u2--;
    } else {
        if (--c1[A] == 0) u1++;
        if (--c2[B] == 0) u2++;
    }
}

/* Replace S[idx] by y. */
static void swap_at(int idx, int y) {
    int x = S[idx];
    for (int j = 0; j < d; j++) {
        if (j == idx) continue;
        int s = S[j];
        upd(x, s, -1);
        upd(s, x, -1);
    }
    upd(x, x, -1);
    for (int j = 0; j < d; j++) {
        if (j == idx) continue;
        int s = S[j];
        upd(y, s, 1);
        upd(s, y, 1);
    }
    upd(y, y, 1);
    S[idx] = y;
    inS[x] = 0;
    inS[y] = 1;
}

int main(int argc, char **argv) {
    if (argc < 7) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    uint64_t seed = (uint64_t)strtoull(argv[2], NULL, 10);
    double tl = atof(argv[3]);
    int m = atoi(argv[4]), k = atoi(argv[5]), r = atoi(argv[6]);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 777ULL);
    if (rs == 0) rs = 1;

    G = m * k;
    if (d < 1 || d > 64 || m < 1 || k < 1 || G > MAXG || G < d) { printf("0 0\n"); return 0; }

    int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long long)rp[b - 1] * r % m);

    for (int x = 0; x < G; x++) {
        for (int y = 0; y < G; y++) {
            int a = x / k, b = x % k, c = y / k, e = y % k;
            long long A = ((long long)a + (long long)rp[b] * c) % m;
            mul[x][y] = (int)(A * k + (b + e) % k);
        }
    }
    for (int x = 0; x < G; x++) {
        iv[x] = -1;
        for (int y = 0; y < G; y++) {
            if (mul[x][y] == 0) { iv[x] = y; break; }
        }
        if (iv[x] < 0) { printf("0 0\n"); return 0; }
    }

    /* Random initial d-subset. */
    int nS = 0;
    while (nS < d) {
        int y = rint_(G);
        if (!inS[y]) { inS[y] = 1; S[nS++] = y; }
    }
    memset(c1, 0, sizeof(c1));
    memset(c2, 0, sizeof(c2));
    u1 = G; u2 = G;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            upd(S[i], S[j], 1);

    clock_t t0 = clock();
    long it = 0;
    const long EP = 150000;
    while (u1 + u2 > 0) {
        if ((it & 1023) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > tl) break;
        }
        it++;
        double ph = (double)(it % EP) / (double)EP;
        double T = 0.1 + 1.0 * (1.0 - ph) * (1.0 - ph);

        int idx = rint_(d);
        int y;
        do { y = rint_(G); } while (inS[y]);
        int x = S[idx];
        int before = u1 + u2;
        swap_at(idx, y);
        int delta = u1 + u2 - before;
        if (delta > 0 && rdbl() >= exp(-(double)delta / T)) {
            swap_at(idx, x);
        }
    }

    if (u1 + u2 != 0) { printf("0 0\n"); return 0; }

    printf("%d %d\n", 2 * G, G * d);
    for (int x = 0; x < G; x++) {
        for (int j = 0; j < d; j++) {
            printf("%d %d\n", x, G + mul[x][S[j]]);
        }
    }
    return 0;
}
"""


def _groups_of_order(n, rng):
    """Candidate groups Z_m x|_r Z_k of order n; the cyclic group is always first."""
    opts = [(n, 1, 1)]
    for k in range(2, n):
        if n % k:
            continue
        m = n // k
        if m < 2:
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if rs:
            for r in rng.sample(rs, min(2, len(rs))):
                opts.append((m, k, r))
    return opts


def _diff_cover_search(d, n_lo, end, rng, seed):
    """Search for a group of order n >= n_lo with a d-set S satisfying S S^-1 = S^-1 S = G.

    Targets rise one at a time: each success moves the target up by one.
    Returns (vertex count, edges) for the best valid graph found, or None.
    """
    max_n = d * d - d + 1
    best = None
    target = n_lo
    trial = 0
    while target <= max_n:
        if end - time.monotonic() < 1.5:
            break
        opts = _groups_of_order(target, rng)
        rest = opts[1:]
        rng.shuffle(rest)
        groups = [opts[0]] + rest
        success = False
        for (m, k, r) in groups[:3]:
            remaining = end - time.monotonic()
            if remaining < 1.5:
                break
            slice_t = min(remaining - 0.5, 5.0)
            try:
                out = lib.run_c(DIFF_SOURCE,
                                [d, seed * 100003 + target * 31 + trial, round(slice_t, 2), m, k, r],
                                timeout=slice_t + 5.0)
                nn, E = lib.parse_graph_text(out)
            except Exception:
                continue
            trial += 1
            if nn == 2 * target and len(E) == target * d and lib.is_valid(nn, E, d, 3):
                best = (nn, E)
                success = True
                break
        if success:
            target += 1
    return best


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). With d >= q+1 each vertex has
# spare capacity s = d - q - 1. Choose S so that every line holds <= s points
# of S and every point lies on <= s lines indexed by S. Add an A-vertex joined
# to the q+1 lines through each P in S, and a B-vertex joined to the q+1 points
# on each line j in S.
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
# Generalized quadrangle W(q) (diameter 4), used for D >= 4.
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
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    end = t_start + 0.8 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = (g[0], g[1])

    # Arc-extended projective plane graphs (valid for D >= 3).
    if D >= 3 and time.monotonic() < end:
        cands = _arc_extensions(d, end, random.Random(seed * 7919 + d))
        for g in sorted(cands, key=lambda t: -t[0]):
            consider(g)

    # Bold change for D = 3: bi-Cayley graphs from difference covers in groups of order n.
    # Each success gives a valid graph on 2n vertices, so the target n keeps rising.
    if D == 3 and time.monotonic() < end - 2.0:
        n_lo = best[0] // 2 + 1
        cand = _diff_cover_search(d, n_lo, end, rng, seed)
        if cand is not None:
            consider(cand)

    # Generalized quadrangle (valid for D >= 4).
    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # Voltage-lift annealing for D >= 4 (unchanged from parent).
    if D >= 4:
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < end:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, end, iters=400)
            if res is not None:
                consider(res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
