import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: search for a "difference cover" S of size d in a finite group G
# (containing the identity) with S * S^{-1} = G. The bi-Cayley graph with
# a_x ~ b_{x*s} (s in S), for x in G, is bipartite, d-regular, has 2|G|
# vertices and diameter <= 3. The engine minimises the number of uncovered
# group elements by simulated annealing and prints the graph when it reaches 0.
#
# Input (stdin, in lib.graph_to_text format): "n m", then m lines "idx val",
# where n = |G| and idx = x*n + y, val = x*y (the multiplication table, identity 0).
# Args: d seed time_limit.
# ----------------------------------------------------------------------------

C_CAVE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 600
#define MAXK 64

static int G, K;
static int T[MAXG][MAXG];
static int INV[MAXG];
static int S[MAXK];
static int inS[MAXG];
static int cnt[MAXG];
static int uncovered;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static void inc_c(int g) { if (cnt[g] == 0) uncovered--; cnt[g]++; }
static void dec_c(int g) { cnt[g]--; if (cnt[g] == 0) uncovered++; }

/* Add (sign > 0) or remove (sign < 0) all ordered pairs that involve S[i]. */
static void touch(int i, int sign) {
    int a = S[i], ia = INV[a];
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        int b = S[j];
        int g1 = T[b][ia];
        int g2 = T[a][INV[b]];
        if (sign > 0) { inc_c(g1); inc_c(g2); }
        else { dec_c(g1); dec_c(g2); }
    }
    if (sign > 0) inc_c(0); else dec_c(0);
}

int main(int argc, char **argv) {
    if (argc < 4) return 1;
    K = atoi(argv[1]);
    uint64_t seed = (uint64_t)strtoull(argv[2], NULL, 10);
    double tl = atof(argv[3]);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 991ULL);
    if (rs == 0) rs = 1;

    int m = 0;
    if (scanf("%d %d", &G, &m) != 2 || G < 2 || G > MAXG || K < 2 || K > MAXK || K > G || m < 0) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m; i++) {
        int idx, val;
        if (scanf("%d %d", &idx, &val) != 2) break;
        if (idx < 0 || idx >= G * G || val < 0 || val >= G) continue;
        T[idx / G][idx % G] = val;
    }
    for (int g = 0; g < G; g++) {
        if (T[0][g] != g || T[g][0] != g) { printf("0 0\n"); return 0; }
        INV[g] = -1;
        for (int h = 0; h < G; h++) if (T[g][h] == 0) { INV[g] = h; break; }
        if (INV[g] < 0) { printf("0 0\n"); return 0; }
    }

    clock_t t0 = clock();
    int found = 0, timed_out = 0;
    const long L = 400000;

    while (!found && !timed_out) {
        memset(cnt, 0, sizeof(int) * (size_t)G);
        memset(inS, 0, sizeof(int) * (size_t)G);
        S[0] = 0; inS[0] = 1;
        for (int i = 1; i < K; i++) {
            int z;
            do { z = rint_(G); } while (inS[z]);
            S[i] = z; inS[z] = 1;
        }
        uncovered = G;
        for (int i = 0; i < K; i++)
            for (int j = 0; j < K; j++)
                inc_c(T[S[i]][INV[S[j]]]);
        if (uncovered == 0) { found = 1; break; }

        for (long k = 0; k < L; k++) {
            if ((k & 4095) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > tl) {
                timed_out = 1;
                break;
            }
            double ph = (double)k / (double)L;
            double Tm = 0.6 * (1.0 - ph) + 0.05;
            int i = 1 + rint_(K - 1);
            int z = rint_(G);
            if (inS[z]) continue;
            int old = S[i];
            int before = uncovered;
            touch(i, -1);
            S[i] = z;
            touch(i, +1);
            int delta = uncovered - before;
            if (delta <= 0 || rdbl() < exp(-(double)delta / Tm)) {
                inS[old] = 0;
                inS[z] = 1;
                if (uncovered == 0) { found = 1; break; }
            } else {
                touch(i, -1);
                S[i] = old;
                touch(i, +1);
            }
        }
    }

    if (!found) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * G, G * K);
    for (int x = 0; x < G; x++)
        for (int i = 0; i < K; i++)
            printf("%d %d\n", x, G + T[x][S[i]]);
    return 0;
}
"""

_MAXG_PY = 599


# ----------------------------------------------------------------------------
# Group candidates for the difference-cover search (D = 3).
# A group of order v is Z_m x|_r Z_k with m * k = v; r = 1 gives the direct product.
# ----------------------------------------------------------------------------

def _groups(v, rng):
    """Candidate groups of order v as (m, k, r): cyclic first, then semidirect products."""
    out = [(v, 1, 1)]
    for k in range(2, v + 1):
        if v % k:
            continue
        m = v // k
        if m < 2:
            continue
        alt = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        picks = [1] + rng.sample(alt, min(2, len(alt)))
        out += [(m, k, r) for r in picks]
    return out


def _group_table(m, k, r):
    """Multiplication table of Z_m x|_r Z_k (element (a, b) coded a*k + b, identity 0)."""
    v = m * k
    x = np.arange(v, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    A = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    B = (b[:, None] + b[None, :]) % k
    return v, A * k + B


def _try_group(d, seed, grp, budget, deadline):
    """Run the C cover search on one group; return (n, edges) if the graph is valid, else None."""
    m, k, r = grp
    left = deadline - time.monotonic()
    if left < 0.1:
        return None
    budget = min(budget, left)
    v, tab = _group_table(m, k, r)
    edges = list(zip(range(v * v), tab.ravel().tolist()))
    try:
        out = lib.run_c(C_CAVE, [d, seed + 131 * v + 7 * k + r, round(budget, 3)],
                        stdin_graph=(v, edges), timeout=budget + 10)
        n, E = lib.parse_graph_text(out)
    except Exception:
        return None
    if n <= 0 or not E:
        return None
    if not lib.is_valid(n, E, d, 3):
        return None
    return n, E


def _cover_search(d, seed, deadline, rng):
    """Find the largest bi-Cayley graph of degree d and diameter 3 over the groups we try."""
    if d < 2:
        return None
    hi = min(d * (d - 1) + 1, _MAXG_PY)   # difference-cover bound: |G| <= d(d-1)+1
    lo = max(2, d)
    # Pass 1: cyclic groups, descending order; stop at the first success (largest order).
    best = None
    for v in range(hi, lo - 1, -1):
        if time.monotonic() > deadline:
            break
        res = _try_group(d, seed, (v, 1, 1), 0.25, deadline)
        if res is not None:
            best = res
            break
    if best is None:
        return None
    # Pass 2: non-cyclic groups of orders above the cyclic result.
    bestv = best[0] // 2
    for v in range(hi, bestv, -1):
        for grp in _groups(v, rng)[1:]:
            if time.monotonic() > deadline:
                return best
            res = _try_group(d, seed, grp, 0.25, deadline)
            if res is not None:
                return res
    return best


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

    # D = 3: difference-cover bi-Cayley graphs over groups of order up to d(d-1)+1.
    if D == 3 and time.monotonic() < end:
        try:
            res = _cover_search(d, seed, end, rng)
        except Exception:
            res = None
        if res is not None:
            consider(res)

    # Arc-extended projective plane graphs (valid for D >= 3).
    if D >= 3 and time.monotonic() < end:
        try:
            cands = _arc_extensions(d, end, random.Random(seed * 7919 + d))
        except Exception:
            cands = []
        for g in sorted(cands, key=lambda t: -t[0]):
            consider(g)

    # Generalized quadrangle (valid for D >= 4).
    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # Voltage-lift annealing for D >= 4.
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
