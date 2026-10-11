import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction for D = 3: cyclic Haar graphs from difference coverings.
#
# H(Z_m, S) has parts A = {a_i} and B = {b_j}, with a_i ~ b_{i+s} for s in S.
# It is bipartite and |S|-regular, and has 2m vertices. Diameter 3 needs
#   (1) S - S covers Z_m, so any two A-vertices (and any two B-vertices) have
#       a common neighbour, and
#   (2) S - S + S covers Z_m, so every A-B pair is within distance 3.
# Since |S-S| <= k(k-1)+1, this family is capped at m <= k^2-k+1, so order
# 2(k^2-k+1) is the Moore bound. The C engine below searches for S of size k
# that covers the nonzero residues by differences, for increasing m.
# Python re-checks the result with lib.is_valid.
# ----------------------------------------------------------------------------

HAAR_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 64
#define MAXM 2048

static uint64_t rs = 1;
static clock_t T0;
static int K, M;
static int S[MAXK];
static int cnt[MAXM];
static int zeros;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) { return (double)(clock() - T0) / CLOCKS_PER_SEC; }

static int md(int x) { x %= M; if (x < 0) x += M; return x; }
static void inc(int r) { if (cnt[r]++ == 0) zeros--; }
static void dec(int r) { if (--cnt[r] == 0) zeros++; }

/* cnt[r] = number of ordered pairs (s, t) in S, s != t, with s - t = r; zeros = #r in 1..M-1 uncovered. */
static void build_cnt(void) {
    memset(cnt, 0, sizeof(cnt));
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            if (i != j) cnt[md(S[i] - S[j])]++;
    zeros = 0;
    for (int r = 1; r < M; r++) if (cnt[r] == 0) zeros++;
}

static void rem_el(int i) {
    int a = S[i];
    for (int j = 0; j < K; j++) {
        if (j != i) { dec(md(a - S[j])); dec(md(S[j] - a)); }
    }
}

static void add_el(int i, int x) {
    S[i] = x;
    for (int j = 0; j < K; j++) {
        if (j != i) { inc(md(x - S[j])); inc(md(S[j] - x)); }
    }
}

static int inset(int x) {
    for (int i = 0; i < K; i++) if (S[i] == x) return 1;
    return 0;
}

/* Simulated annealing on S for the fixed modulus m. Returns 1 when S covers all differences. */
static int try_m(int m, double deadline) {
    M = m;
    for (int i = 0; i < K;) {
        int x = rint_(M);
        int dup = 0;
        for (int j = 0; j < i; j++) if (S[j] == x) { dup = 1; break; }
        if (!dup) S[i++] = x;
    }
    build_cnt();
    long it = 0;
    const long CYCLE = 3000000L;
    while (zeros > 0) {
        if ((it & 4095) == 0 && now() > deadline) return 0;
        it++;
        double phase = (double)(it % CYCLE) / (double)CYCLE;
        double T = 0.05 + 0.9 * (1.0 - phase) * (1.0 - phase);
        int i = rint_(K);
        int x = rint_(M);
        if (inset(x)) continue;
        int a = S[i];
        int z0 = zeros;
        rem_el(i);
        add_el(i, x);
        int delta = zeros - z0;
        if (!(delta <= 0 || rdbl() < exp(-(double)delta / T))) {
            rem_el(i);
            add_el(i, a);
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 7) return 1;
    K = atoi(argv[1]);
    uint64_t seed = (uint64_t)strtoull(argv[2], NULL, 10);
    double tl = atof(argv[3]);
    int mlo = atoi(argv[4]), mhi = atoi(argv[5]);
    double per = atof(argv[6]);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (rs == 0) rs = 1;
    T0 = clock();

    int bestM = 0;
    int bestS[MAXK];
    for (int i = 0; i < MAXK; i++) bestS[i] = 0;
    if (K < 1 || K > MAXK) { printf("0 %d\n", K); return 0; }

    for (int m = mlo; m <= mhi && m < MAXM; m++) {
        if (m < K) continue;
        double left = tl - now();
        if (left <= 0.05) break;
        double dl = now() + (per < left ? per : left);
        if (try_m(m, dl)) {
            bestM = m;
            memcpy(bestS, S, sizeof(int) * (size_t)K);
        }
    }
    printf("%d %d\n", bestM, K);
    for (int i = 0; i < K; i++) printf("%d ", bestS[i]);
    printf("\n");
    return 0;
}
"""


def _haar_search(d, seconds, seed):
    """Search cyclic difference coverings of size d; return (2m, edges) or None."""
    hi = d * d - d + 1                # Moore-type cap for cyclic Haar graphs
    lo = max(d, int(0.8 * hi))
    out = lib.run_c(HAAR_SOURCE, [d, seed, round(seconds, 2), lo, hi, 4.0],
                    timeout=seconds + 5)
    toks = out.split()
    m, k = int(toks[0]), int(toks[1])
    if m < 1:
        return None
    S = [int(x) for x in toks[2:2 + k]]
    if len(S) != k:
        return None
    edges = [(i, m + (i + s) % m) for i in range(m) for s in S]
    return 2 * m, edges


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# Start from PG(2, q); with d >= q+1 each vertex has spare capacity
# s = d - q - 1. Choose an arc S so that every line holds <= s points of S and
# every point lies on <= s lines indexed by S. Add an A-vertex joined to the
# q+1 lines through each P in S, and a B-vertex joined to the q+1 points on
# each line j in S.
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


def _swap_improve(S, s, m, point_lines, line_points, rng, deadline, iters):
    """Ejection-based local search growing the arc set S; returns the best set seen."""
    cur = list(S)
    inS = set(cur)
    best = list(cur)
    pl_set = [set(point_lines[X]) for X in range(m)]
    lp_set = [set(line_points[X]) for X in range(m)]
    for _ in range(iters):
        if time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if P in inS:
            continue
        cl = [0] * m
        cp = [0] * m
        for X in cur:
            for L in point_lines[X]:
                cl[L] += 1
            for Q in line_points[X]:
                cp[Q] += 1
        Lset = set(point_lines[P])
        Qset = set(line_points[P])
        Lfull = {L for L in Lset if cl[L] >= s}
        Qfull = {Q for Q in Qset if cp[Q] >= s}
        block = [X for X in cur if (pl_set[X] & Lfull) or (lp_set[X] & Qfull)]
        if len(block) > 2:
            continue
        if not block and rng.random() > 0.5:
            continue
        bset = set(block)
        new = [X for X in cur if X not in bset] + [P]
        if not _loads_ok(new, s, m, point_lines, line_points):
            continue
        if len(new) >= len(cur) or rng.random() < 0.1:
            cur = new
            inS = set(cur)
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


def _arc_candidates(d, deadline, rng):
    """Return (n, edges) candidates for the two largest prime powers q with q + 1 <= d."""
    out = []
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]
    for q in qs[-2:]:
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            g = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
            g = _swap_improve(g, s, m, point_lines, line_points, rng,
                              min(deadline, time.monotonic() + 2.0), iters=6000)
            cands.append(g)
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cs = _swap_improve(cs, s, m, point_lines, line_points, rng,
                                   min(deadline, time.monotonic() + 1.0), iters=3000)
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
    end = t_start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g is None:
            return
        if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = (g[0], g[1])

    if D == 3:
        # Stage 1: arc-extended projective plane graphs (short budget).
        arc_end = min(end, t_start + 0.2 * time_limit)
        for g in sorted(_arc_candidates(d, arc_end, random.Random(seed * 7919 + d)),
                        key=lambda t: -t[0]):
            consider(g)

        # Stage 2: cyclic Haar graphs from difference coverings (main new search).
        haar_end = t_start + 0.8 * time_limit - 1.0
        remaining = haar_end - time.monotonic()
        if d >= 3 and remaining > 2.0:
            try:
                consider(_haar_search(d, remaining - 1.0, seed))
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
