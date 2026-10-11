import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: cyclic Haar graphs with a difference cover (diameter 3).
#
# The Haar graph H(Z_m, S) has a_i ~ b_{i+s} for s in S, |S| = d. Same-side
# distance is even, so a_i and a_k are within distance 2 iff i-k lies in S-S.
# Cross distance is at most 3 once S-S covers Z_m, since x = s1-s2+s3 for any x.
# So H(Z_m, S) has diameter <= 3 whenever S-S = Z_m, and has order 2m.
# The engine grows m and searches S by simulated annealing over the number of
# uncovered nonzero residues. The best (m, S) found is printed as a graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 1500
#define MAXK 64
#define ITER_CAP 400000L

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d, m;
static int S[MAXK];
static int cnt[MAXM];
static int zeros;

static int md(int x) { x %= m; return x < 0 ? x + m : x; }
static void inc(int x) { if (cnt[x] == 0) zeros--; cnt[x]++; }
static void dec(int x) { cnt[x]--; if (cnt[x] == 0) zeros++; }

static void rebuild(void) {
    for (int x = 0; x < m; x++) cnt[x] = 0;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            if (i != j) cnt[md(S[i] - S[j])]++;
    zeros = 0;
    for (int x = 1; x < m; x++) if (cnt[x] == 0) zeros++;
}

static void remove_elem(int idx) {
    int a = S[idx];
    for (int t = 0; t < d; t++) {
        if (t != idx) { dec(md(a - S[t])); dec(md(S[t] - a)); }
    }
}

static void add_elem(int idx, int b) {
    S[idx] = b;
    for (int t = 0; t < d; t++) {
        if (t != idx) { inc(md(b - S[t])); inc(md(S[t] - b)); }
    }
}

static int in_set(int b) {
    for (int t = 0; t < d; t++) if (S[t] == b) return 1;
    return 0;
}

static int in_prefix(int b, int k) {
    for (int t = 0; t < k; t++) if (S[t] == b) return 1;
    return 0;
}

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    int D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    clock_t t0 = clock();

    if (d < 2 || d > MAXK || D < 3) { printf("0 0\n"); return 0; }

    long mmax_l = (long)d * (d - 1) + 1;
    int mmax = (int)(mmax_l < MAXM - 1 ? mmax_l : MAXM - 1);

    int bestm = d;
    int bestS[MAXK];
    for (int i = 0; i < d; i++) bestS[i] = i;   /* Z_d: K_{d,d}, always valid */

    int level = bestm + 1;
    int warm = 1;
    while (level <= mmax && elapsed(t0) < tl) {
        m = level;
        if (warm) {
            for (int i = 0; i < d; i++) S[i] = bestS[i];
        } else {
            for (int i = 0; i < d; i++) {
                int b;
                do { b = rint_(m); } while (in_prefix(b, i));
                S[i] = b;
            }
        }
        rebuild();
        int ok = (zeros == 0);
        for (long it = 0; !ok && it < ITER_CAP; it++) {
            if ((it & 4095) == 0 && elapsed(t0) > tl) break;
            double frac = (double)it / (double)ITER_CAP;
            double T = 0.5 * (1.0 - frac) + 0.05;
            int idx = rint_(d);
            int a = S[idx];
            int b;
            do { b = rint_(m); } while (in_set(b));
            int old = zeros;
            remove_elem(idx);
            add_elem(idx, b);
            int delta = zeros - old;
            if (!(delta <= 0 || rdbl() < exp(-(double)delta / T))) {
                remove_elem(idx);
                add_elem(idx, a);
            }
            if (zeros == 0) ok = 1;
        }
        if (ok) {
            bestm = m;
            for (int i = 0; i < d; i++) bestS[i] = S[i];
            level = m + 1;
            warm = 1;
        } else {
            warm = 0;   /* retry the same level from a random start */
        }
    }

    int n = 2 * bestm, E = bestm * d;
    printf("%d %d\n", n, E);
    for (int i = 0; i < bestm; i++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", i, bestm + (i + bestS[k]) % bestm);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Singer difference set (diameter 3, perfect when d - 1 = q is a prime power).
# S = {i < q^2+q+1 : Tr(g^i) = 0} with Tr(x) = x + x^q + x^(q^2) in GF(q^3).
# ----------------------------------------------------------------------------

def _singer_haar(d):
    """Return (m, S) with |S| = d and S-S = Z_m for m = d^2 - d + 1, or None."""
    q = d - 1
    if q < 2 or not lib.is_prime_power(q) or q ** 3 > 1000:
        return None
    try:
        F = lib.GF(q ** 3)
    except Exception:
        return None
    g = F.primitive_element()
    m = q * q + q + 1
    S = []
    x = 1
    for i in range(m):
        t = F.add(F.add(x, F.pow(x, q)), F.pow(x, q * q))
        if t == 0:
            S.append(i)
        x = F.mul(x, g)
    if len(S) != d:
        return None
    return m, S


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
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
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

def _run_haar_search(d, D, seed, budget):
    """Run the cyclic Haar difference-cover engine; return (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                    stdin_graph=None, timeout=budget + 10)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    end = t_start + 0.8 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        try:
            if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
                best = (g[0], list(g[1]))
        except Exception:
            pass

    if D == 2:
        return best[0], list(best[1])

    # Diameter 3 candidates: Singer difference set (perfect when d-1 is a prime power).
    if D >= 3:
        sg = _singer_haar(d)
        if sg is not None:
            consider(lib.haar_graph(sg[0], sg[1]))

        # Arc-extended projective plane graphs (valid for D >= 3).
        if time.monotonic() < end:
            cands = _arc_extensions(d, end, random.Random(seed * 7919 + d))
            for g in sorted(cands, key=lambda t: -t[0]):
                consider(g)

    # Main bold change for D = 3: cyclic Haar graphs from difference covers.
    # Most of the budget goes here. The engine always prints a valid graph.
    if D == 3:
        budget = end - time.monotonic() - 0.5
        if budget > 2.0:
            try:
                consider(_run_haar_search(d, D, seed, budget))
            except Exception:
                pass
    else:
        # D >= 4: generalized quadrangle, then a short Haar search, then voltage lifts.
        if time.monotonic() < end:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq)
        budget = 0.2 * (end - time.monotonic())
        if budget > 2.0:
            try:
                consider(_run_haar_search(d, D, seed, budget))
            except Exception:
                pass

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
