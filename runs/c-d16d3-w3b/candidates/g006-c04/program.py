import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing for "difference covers" in a finite group.
#
# Input (stdin): "M M*M", then M*M lines "x v" where v = x-th row, y-th column
# of the multiplication table in x-major order (element 0 is the identity).
# Search: find S with |S| = K, 0 in S, such that S*S^{-1} = G and S^{-1}*S = G.
# The bipartite Haar graph H(G, S) (a_g ~ b_{g s}) then has diameter 3.
# Output: "OK k s_1 ... s_k" or "FAIL".
# ----------------------------------------------------------------------------

DIFF_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 1024
#define MAXK 64
#define RESTART 400000L

static int M, K;
static int mul[MAXM][MAXM];
static int invv[MAXM];
static int S[MAXK];
static unsigned char inS[MAXM];
static int cnt1[MAXM], cnt2[MAXM];
static int zeros;
static uint64_t rs = 1;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static void dec_(int *c, int x) { if (--c[x] == 0) zeros++; }
static void inc_(int *c, int x) { if (c[x]++ == 0) zeros--; }

/* ordered pair (a, b): contributes a*b^-1 to cnt1 and a^-1*b to cnt2 */
static void touch_pair(int a, int b, int sg) {
    int x1 = mul[a][invv[b]];
    int x2 = mul[invv[a]][b];
    if (sg < 0) { dec_(cnt1, x1); dec_(cnt2, x2); }
    else { inc_(cnt1, x1); inc_(cnt2, x2); }
}

/* add or remove every ordered pair involving position i (current S[i]) */
static void touch(int i, int sg) {
    int si = S[i];
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        touch_pair(si, S[j], sg);
        touch_pair(S[j], si, sg);
    }
    touch_pair(si, si, sg);
}

static void full_init(void) {
    memset(cnt1, 0, sizeof(int) * (size_t)M);
    memset(cnt2, 0, sizeof(int) * (size_t)M);
    zeros = 2 * M;
    for (int a = 0; a < K; a++)
        for (int b = 0; b < K; b++)
            touch_pair(S[a], S[b], +1);
}

int main(int argc, char **argv) {
    if (argc < 4) return 1;
    K = atoi(argv[1]);
    double tl = atof(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 991ULL);
    if (rs == 0) rs = 1;

    int hn = 0, hm = 0;
    if (scanf("%d %d", &hn, &hm) != 2) { printf("FAIL\n"); return 0; }
    M = hn;
    if (M < 1 || M > MAXM || K < 1 || K > MAXK || K > M) { printf("FAIL\n"); return 0; }
    for (long i = 0; i < (long)M * M; i++) {
        int u = 0, v = 0;
        if (scanf("%d %d", &u, &v) != 2) { printf("FAIL\n"); return 0; }
        if (v < 0 || v >= M) { printf("FAIL\n"); return 0; }
        mul[i / M][i % M] = v;
    }
    for (int x = 0; x < M; x++) {
        invv[x] = -1;
        for (int y = 0; y < M; y++) {
            if (mul[x][y] == 0) { invv[x] = y; break; }
        }
        if (invv[x] < 0) { printf("FAIL\n"); return 0; }
    }

    clock_t t0 = clock();
    int found = 0;
    while (!found) {
        memset(inS, 0, (size_t)M);
        S[0] = 0; inS[0] = 1;
        for (int i = 1; i < K; i++) {
            int y;
            do { y = (int)(rnd() % (uint64_t)M); } while (inS[y]);
            S[i] = y; inS[y] = 1;
        }
        full_init();
        if (zeros == 0) { found = 1; break; }
        if (K < 2) break;
        for (long step = 0; step < RESTART; step++) {
            if ((step & 4095) == 0 &&
                (double)(clock() - t0) / CLOCKS_PER_SEC > tl) goto done;
            double frac = (double)step / (double)RESTART;
            double T = 1.5 * pow(0.03, frac);
            int i = 1 + (int)(rnd() % (uint64_t)(K - 1));
            int y = (int)(rnd() % (uint64_t)M);
            if (inS[y]) continue;
            int old = S[i];
            int c0 = zeros;
            touch(i, -1);
            inS[old] = 0; S[i] = y; inS[y] = 1;
            touch(i, +1);
            int delta = zeros - c0;
            if (delta > 0 && !(rdbl() < exp(-(double)delta / T))) {
                touch(i, -1);
                inS[y] = 0; S[i] = old; inS[old] = 1;
                touch(i, +1);
            }
            if (zeros == 0) { found = 1; goto done; }
        }
    }
done:
    if (found) {
        printf("OK\n");
        for (int i = 0; i < K; i++) printf("%d ", S[i]);
        printf("\n");
    } else {
        printf("FAIL\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Group-based bipartite Haar graphs (diameter 3).
# ----------------------------------------------------------------------------

def _group_options(M, rng):
    """Return multiplication functions for several groups of order M (cyclic first)."""
    opts = [lib.cyclic_group(M)[1]]
    for k2 in (2, 3, 4, 5, 6, 7, 8):
        if M % k2:
            continue
        m = M // k2
        if m < 2:
            continue
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not cands:
            continue
        for r in rng.sample(cands, min(2, len(cands))):
            try:
                _, mul, _ = lib.semidirect_group(m, k2, r)
            except ValueError:
                continue
            opts.append(mul)
    return opts[:6]


_OPT_CACHE = {}


def _options(M, rng):
    if M not in _OPT_CACHE:
        _OPT_CACHE[M] = _group_options(M, rng)
    return _OPT_CACHE[M]


def _parse_S(out, k):
    toks = out.split()
    if len(toks) < 1 + k or toks[0] != "OK":
        return None
    S = [int(t) for t in toks[1:1 + k]]
    if len(set(S)) != k:
        return None
    return S


def _haar_edges(M, mul, S):
    """Bipartite Haar graph of group G: a_g ~ b_{g s} for s in S, vertices a_g = g, b_x = M + x."""
    return 2 * M, [(g, M + mul(g, s)) for g in range(M) for s in S]


def _diff_search(d, end, rng, consider):
    """Search for the largest group order M with a k-element difference cover (k = d)."""
    k = d
    Mmax = k * (k - 1) + 1
    found = [None]

    def attempt(M, idx, budget):
        opts = _options(M, rng)
        if idx >= len(opts):
            return None
        mul = opts[idx]
        left = end - time.monotonic() - 0.3
        budget = min(budget, left)
        if budget < 0.05:
            return None
        pairs = [(x, mul(x, y)) for x in range(M) for y in range(M)]
        try:
            out = lib.run_c(DIFF_C, [k, round(budget, 3), rng.randrange(1 << 30)],
                            stdin_graph=(M, pairs), timeout=budget + 5.0)
        except RuntimeError:
            return None
        S = _parse_S(out, k)
        if S is None or 0 not in S:
            return None
        return _haar_edges(M, mul, S)

    # Phase 1: descend from the perfect-difference-set bound with cyclic groups.
    M = Mmax
    while M >= 2 and time.monotonic() < end - 0.5 and found[0] is None:
        g = attempt(M, 0, 0.25)
        if g is not None:
            found[0] = (M, g)
            consider(g)
        M -= 1

    # Phase 2: try slightly larger orders with more groups and longer runs.
    while found[0] is not None and found[0][0] < Mmax and time.monotonic() < end - 0.5:
        best = found[0][0]
        if rng.random() < 0.5:
            M = best + 1
        else:
            M = rng.randint(best + 1, min(Mmax, best + 12))
        idx = rng.randrange(len(_options(M, rng)))
        g = attempt(M, idx, 1.0)
        if g is not None and g[0] > found[0][0]:
            found[0] = (M, g)
            consider(g)


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


def _swap_improve(S, s, m, point_lines, line_points, rng, deadline, iters):
    """Local search that grows the arc set S by ejection moves."""
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


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates from the two largest usable prime powers q <= d - 1."""
    out = []
    qs = [q for q in range(min(d - 1, 23), 1, -1) if lib.is_prime_power(q)][:2]
    for q in qs:
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
    t0 = time.monotonic()
    end = t0 + 0.8 * time_limit - 1.0
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
            best = (g[0], list(g[1]))

    if D == 3:
        # Known-construction candidates first (fast, safe fallback).
        arc_end = min(end, t0 + 0.25 * time_limit)
        for g in sorted(_arc_extensions(d, arc_end, random.Random(seed * 7919 + d)),
                        key=lambda t: -t[0]):
            consider(g)
        # New construction: Haar graphs on groups whose difference set covers G.
        if d >= 2 and time.monotonic() < end:
            try:
                _diff_search(d, end, random.Random(seed + 1), consider)
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
