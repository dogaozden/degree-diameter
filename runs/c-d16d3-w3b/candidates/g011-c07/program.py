import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New D = 3 construction: Haar graphs of abelian groups.
#
# For an abelian group G of order M and a K-subset S of G, the Haar graph has
# a_x ~ b_y iff y - x in S. Same-side distance is 2 exactly when x - y lies in
# S - S, and every cross-side distance is at most 3 once S - S = G. So the
# graph has degree K, is bipartite, has 2M vertices, and has diameter 3 iff S
# is a "difference cover" of G. Since |S - S| <= K(K-1) + 1, we need
# M <= K^2 - K + 1, which is the Moore bound 2(K^2-K+1) for D = 3.
#
# The C engine searches over groups Z_a x Z_b (a*b = M) and subsets S by
# simulated annealing on the number of uncovered nonzero differences. It tries
# M upward from a threshold that beats the current graph and keeps the largest
# M that is covered.
# ----------------------------------------------------------------------------

HAAR_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 260
#define MAXK 64
#define MAXC 4096

typedef struct { int m, a, b; } Cand;

static int K, A, B, M;
static int sadd[MAXM][MAXM];
static int dif[MAXM][MAXM];
static int S[MAXK];
static int inS[MAXM];
static int cnt[MAXM];
static int uncov;
static uint64_t rs = 88172645463325252ULL;

static int bestS[MAXK];
static int bestA, bestB, bestM = -1;
static Cand cands[MAXC];
static int nc = 0;
static clock_t t0;
static double budget;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }

static void build_group(void) {
    for (int x = 0; x < M; x++) {
        int i1 = x / B, j1 = x % B;
        for (int y = 0; y < M; y++) {
            int i2 = y / B, j2 = y % B;
            sadd[x][y] = ((i1 + i2) % A) * B + (j1 + j2) % B;
            dif[x][y] = ((i1 - i2 + A) % A) * B + ((j1 - j2 + B) % B);
        }
    }
}

static inline void inc_pair(int g) { if (cnt[g]++ == 0) uncov--; }
static inline void dec_pair(int g) { if (--cnt[g] == 0) uncov++; }

static void add_at(int i) {
    int x = S[i];
    for (int j = 0; j < K; j++) if (j != i) {
        inc_pair(dif[x][S[j]]);
        inc_pair(dif[S[j]][x]);
    }
}
static void rem_at(int i) {
    int x = S[i];
    for (int j = 0; j < K; j++) if (j != i) {
        dec_pair(dif[x][S[j]]);
        dec_pair(dif[S[j]][x]);
    }
}

static void init_state(void) {
    memset(inS, 0, sizeof(inS));
    memset(cnt, 0, sizeof(cnt));
    uncov = M - 1;
    for (int i = 0; i < K; i++) {
        int x;
        do { x = rint_(M); } while (inS[x]);
        S[i] = x;
        inS[x] = 1;
    }
    for (int i = 0; i < K; i++)
        for (int j = 0; j < i; j++) {
            inc_pair(dif[S[i]][S[j]]);
            inc_pair(dif[S[j]][S[i]]);
        }
}

/* Returns 1 when every nonzero element of the group is a difference of S. */
static int anneal(clock_t until) {
    const long cyc = 200000;
    double T = 1.0;
    for (long it = 0; ; it++) {
        if (uncov == 0) return 1;
        if ((it & 4095) == 0) {
            if (clock() >= until) return 0;
            double frac = (double)(it % cyc) / (double)cyc;
            T = 1.2 * pow(0.04 / 1.2, frac);
        }
        int i = rint_(K);
        int x;
        do { x = rint_(M); } while (inS[x]);
        int old = S[i];
        int u0 = uncov;
        rem_at(i);
        S[i] = x;
        add_at(i);
        int delta = uncov - u0;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            inS[old] = 0;
            inS[x] = 1;
        } else {
            rem_at(i);
            S[i] = old;
            add_at(i);
        }
    }
}

static int try_cand(int c, double slice) {
    A = cands[c].a; B = cands[c].b; M = cands[c].m;
    build_group();
    init_state();
    clock_t until = clock() + (clock_t)(slice * CLOCKS_PER_SEC);
    if (anneal(until)) {
        if (M > bestM) {
            bestM = M; bestA = A; bestB = B;
            memcpy(bestS, S, sizeof(int) * (size_t)K);
        }
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 7) { printf("0 0\n"); return 0; }
    K = atoi(argv[1]);
    int D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int mlo = atoi(argv[5]), mhi = atoi(argv[6]);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 777ULL);
    if (rs == 0) rs = 1;
    if (K < 1 || K > MAXK || D != 3) { printf("0 0\n"); return 0; }
    if (mhi >= MAXM) mhi = MAXM - 1;
    t0 = clock();
    budget = tl;

    int start = mlo < K + 1 ? K + 1 : mlo;
    for (int m = start; m <= mhi; m++) {
        if ((long)(m - 1) > (long)K * (K - 1)) break;
        for (int a = 1; a * a <= m; a++) {
            if (m % a) continue;
            if (nc < MAXC) {
                cands[nc].m = m;
                cands[nc].a = a;
                cands[nc].b = m / a;
                nc++;
            }
        }
    }
    if (nc == 0) { printf("0 0\n"); return 0; }

    /* Pass 1: short equal slices, ascending M. */
    double slice1 = 0.4 * budget / nc;
    for (int c = 0; c < nc; c++) {
        if (elapsed() > budget) break;
        try_cand(c, slice1);
    }

    /* Pass 2: spend the rest on candidates larger than the best found. */
    for (int c = 0; c < nc; c++) {
        if (cands[c].m <= bestM) continue;
        double rem = budget - elapsed();
        if (rem < 0.05) break;
        int left = 0;
        for (int e = c; e < nc; e++) if (cands[e].m > bestM) left++;
        if (left < 1) left = 1;
        try_cand(c, rem / left);
    }

    if (bestM < 0) { printf("0 0\n"); return 0; }
    A = bestA; B = bestB; M = bestM;
    build_group();
    printf("%d %d\n", 2 * M, M * K);
    for (int x = 0; x < M; x++)
        for (int j = 0; j < K; j++)
            printf("%d %d\n", x, M + sadd[x][bestS[j]]);
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

    # Arc-extended projective plane graphs (valid for D >= 3).
    if D >= 3 and time.monotonic() < end:
        cands = _arc_extensions(d, end, random.Random(seed * 7919 + d))
        for g in sorted(cands, key=lambda t: -t[0]):
            consider(g)

    # New D = 3 construction: abelian Haar graphs from difference covers.
    # A success on M gives 2M vertices, degree d and diameter 3. Only M values
    # above the current best half are searched, so every hit is an improvement.
    if D == 3:
        lo = best[0] // 2 + 1
        hi = d * d - d + 1
        remaining = end - time.monotonic()
        htl = 0.9 * remaining
        if lo <= hi and htl > 2.0:
            try:
                out = lib.run_c(HAAR_SOURCE, [d, D, seed, round(htl, 2), lo, hi],
                                stdin_graph=None, timeout=htl + 5)
                consider(lib.parse_graph_text(out))
            except Exception:
                pass

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
