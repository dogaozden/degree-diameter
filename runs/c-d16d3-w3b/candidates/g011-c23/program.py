import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New D = 3 construction: bi-Cayley (Haar-type) graphs from difference covers.
#
# Let G = Z_a x Z_b be an abelian group of order m and S a k-subset of G
# (k = d). Join a_g to b_h iff h - g is in S. The graph is bipartite and
# k-regular with 2m vertices. A-A and B-B distances are at most 2 when every
# element of G is a difference s - t of S, and A-B distances are at most 3
# then, since S-S+S covers G. So a difference cover of size k with m elements
# gives a valid diameter-3 graph of order 2m. A perfect difference set would
# reach m = k^2 - k + 1 (the Moore bound), but such sets are rare, so the C
# engine searches for near-perfect covers with simulated annealing. Its cost is
# the number of nonzero group elements not yet covered as a difference.
#
# The C engine binary-searches the group order m in [lo, hi]. Each attempt
# picks a random factorisation of m (so both cyclic and non-cyclic groups are
# tried) and anneals with restarts. The best cover found is printed as a graph.
# Python keeps the arc-extended projective plane graph as the floor and checks
# every candidate with lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 64
#define MAXM 1200

static int K = 0, AA = 1, BB = 1, MM = 1;
static int S[MAXK];
static int cnt[MAXM];
static int cost = 0;
static uint64_t rs = 88172645463325252ULL;
static clock_t T0C;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - T0C) / CLOCKS_PER_SEC; }

/* Elements of Z_AA x Z_BB are coded e = x*BB + y. */
static int gadd(int e1, int e2) {
    int x = (e1 / BB + e2 / BB) % AA;
    int y = (e1 % BB + e2 % BB) % BB;
    return x * BB + y;
}
static int gsub(int e1, int e2) {
    int x = (e1 / BB - e2 / BB + AA) % AA;
    int y = (e1 % BB - e2 % BB + BB) % BB;
    return x * BB + y;
}

/* cost = number of nonzero group elements with cnt == 0. */
static void inc_d(int x) {
    if (cnt[x] == 0 && x != 0) cost--;
    cnt[x]++;
}
static void dec_d(int x) {
    cnt[x]--;
    if (cnt[x] == 0 && x != 0) cost++;
}

static int in_set(int v) {
    for (int j = 0; j < K; j++) if (S[j] == v) return 1;
    return 0;
}
static int in_prefix(int v, int upto) {
    for (int j = 0; j < upto; j++) if (S[j] == v) return 1;
    return 0;
}

/* Replace S[i] by v and update the difference counts. */
static void repl(int i, int v) {
    int old = S[i];
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        dec_d(gsub(old, S[j]));
        dec_d(gsub(S[j], old));
        inc_d(gsub(v, S[j]));
        inc_d(gsub(S[j], v));
    }
    S[i] = v;
}

static int sa_run(long iters, double T0, double T1) {
    for (int i = 0; i < K; i++) {
        int v;
        do { v = rint_(MM); } while (in_prefix(v, i));
        S[i] = v;
    }
    memset(cnt, 0, sizeof(int) * (size_t)MM);
    cost = MM - 1;
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            if (i != j) inc_d(gsub(S[i], S[j]));
    if (cost == 0) return 1;
    double lr = log(T1 / T0) / (double)iters;
    for (long t = 0; t < iters; t++) {
        double T = T0 * exp(lr * (double)t);
        int i = rint_(K);
        int v;
        do { v = rint_(MM); } while (in_set(v));
        int old = S[i];
        int c0 = cost;
        repl(i, v);
        int delta = cost - c0;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            if (cost == 0) return 1;
        } else {
            repl(i, old);
        }
    }
    return 0;
}

static int divs[MAXM];
static int ndiv = 0;

static int attempt(int m, double slice) {
    MM = m;
    double endt = elapsed() + slice;
    while (elapsed() < endt) {
        ndiv = 0;
        for (int a = 1; a <= m; a++) if (m % a == 0) divs[ndiv++] = a;
        int a = divs[rint_(ndiv)];
        AA = a;
        BB = m / a;
        if (sa_run(300000, 1.0, 0.08)) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 7) { printf("0 0\n"); return 0; }
    K = atoi(argv[1]);
    int D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int hi = atoi(argv[5]);
    int lo = atoi(argv[6]);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 777ULL);
    if (rs == 0) rs = 1;
    T0C = clock();

    if (D != 3 || K < 2 || K > MAXK) { printf("0 0\n"); return 0; }
    long kk = (long)K * K - K + 1;
    if (hi > kk) hi = (int)kk;
    if (hi > MAXM - 1) hi = MAXM - 1;
    if (lo < K + 1) lo = K + 1;

    int best_m = 0, bestA = 1, bestB = 1;
    int bestS[MAXK];
    while (lo <= hi && elapsed() < tl) {
        double remain = tl - elapsed();
        double slice = tl / 8.0;
        if (slice < 0.5) slice = 0.5;
        if (slice > remain) slice = remain;
        int mid = (lo + hi + 1) / 2;
        if (attempt(mid, slice)) {
            best_m = mid;
            bestA = AA;
            bestB = BB;
            memcpy(bestS, S, sizeof(int) * (size_t)K);
            lo = mid + 1;
        } else {
            hi = mid - 1;
        }
    }

    if (best_m == 0) { printf("0 0\n"); return 0; }
    AA = bestA;
    BB = bestB;
    MM = best_m;
    int m = best_m;
    printf("%d %d\n", 2 * m, m * K);
    for (int g = 0; g < m; g++)
        for (int k = 0; k < K; k++)
            printf("%d %d\n", g, m + gadd(g, bestS[k]));
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
    end = t_start + 0.88 * time_limit - 1.0
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

    # Arc-extended projective plane graphs (valid for D >= 3). Floor for D = 3.
    if D >= 3 and time.monotonic() < end:
        cands = _arc_extensions(d, end, random.Random(seed * 7919 + d))
        for g in sorted(cands, key=lambda t: -t[0]):
            consider(g)

    # New D = 3 search: bi-Cayley graphs from difference covers over Z_a x Z_b.
    # A cover S of size d with S - S = G gives a valid Haar graph of order 2|G|.
    if D == 3 and d >= 2:
        hi = d * d - d + 1
        lo = best[0] // 2 + 1
        cbudget = end - time.monotonic()
        if lo <= hi and cbudget > 3.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(cbudget - 1.5, 2), hi, lo],
                                stdin_graph=None, timeout=cbudget + 5)
                consider(lib.parse_graph_text(out))
            except Exception:
                pass

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
