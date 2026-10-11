import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing for a large "arc" S in PG(2, q).
#
# Input (stdin): point-line incidence graph, points 0..M-1, lines M..2M-1.
# Args: s seed time_limit_seconds.
# Constraint: every line holds <= s points of S, and every point lies on
# <= s lines whose index is in S (the dual condition). Objective: max |S|.
# Penalty SA over single-point toggles, O(q) per move. Output: k, then k indices.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 1;
static inline uint64_t rnd64(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static inline double rndu(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int g_M, g_W, g_s;
static int *g_through, *g_tdeg;   /* g_through[P*W+k]: lines through point P */
static int *g_onl, *g_odeg;       /* g_onl[L*W+k]: points on line L */
static int *g_cl, *g_cp;          /* g_cl[L]: S-points on L; g_cp[Q]: S-indexed lines through Q */
static char *g_inS;
static int g_sz = 0, g_V = 0;

static int dv_add(int P) {
    int dv = 0;
    const int *th = g_through + (size_t)P * g_W;
    for (int k = 0; k < g_tdeg[P]; k++) if (g_cl[th[k]] >= g_s) dv++;
    const int *ol = g_onl + (size_t)P * g_W;
    for (int k = 0; k < g_odeg[P]; k++) if (g_cp[ol[k]] >= g_s) dv++;
    return dv;
}

static int dv_rem(int P) {
    int dv = 0;
    const int *th = g_through + (size_t)P * g_W;
    for (int k = 0; k < g_tdeg[P]; k++) if (g_cl[th[k]] > g_s) dv--;
    const int *ol = g_onl + (size_t)P * g_W;
    for (int k = 0; k < g_odeg[P]; k++) if (g_cp[ol[k]] > g_s) dv--;
    return dv;
}

static void do_add(int P) {
    g_V += dv_add(P);
    g_inS[P] = 1;
    g_sz++;
    const int *th = g_through + (size_t)P * g_W;
    for (int k = 0; k < g_tdeg[P]; k++) g_cl[th[k]]++;
    const int *ol = g_onl + (size_t)P * g_W;
    for (int k = 0; k < g_odeg[P]; k++) g_cp[ol[k]]++;
}

static void do_rem(int P) {
    g_V += dv_rem(P);
    g_inS[P] = 0;
    g_sz--;
    const int *th = g_through + (size_t)P * g_W;
    for (int k = 0; k < g_tdeg[P]; k++) g_cl[th[k]]--;
    const int *ol = g_onl + (size_t)P * g_W;
    for (int k = 0; k < g_odeg[P]; k++) g_cp[ol[k]]--;
}

int main(int argc, char **argv) {
    if (argc < 4) {
        fprintf(stderr, "usage: prog s seed time\n");
        return 1;
    }
    int s = atoi(argv[1]);
    unsigned long long seed = strtoull(argv[2], NULL, 10);
    double tl = atof(argv[3]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();

    int n = 0, me = 0;
    if (scanf("%d %d", &n, &me) != 2 || n < 2 || me < 0) {
        printf("0\n");
        return 0;
    }
    int M = n / 2;
    int *eu = malloc(sizeof(int) * (size_t)(me + 1));
    int *ev = malloc(sizeof(int) * (size_t)(me + 1));
    int cnt = 0;
    for (int i = 0; i < me; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u > v) { int t = u; u = v; v = t; }
        if (u < 0 || v >= n || u >= M || v < M) continue;
        eu[cnt] = u;
        ev[cnt] = v;
        cnt++;
    }

    int *tdeg = calloc(M, sizeof(int));
    int *odeg = calloc(M, sizeof(int));
    for (int i = 0; i < cnt; i++) {
        tdeg[eu[i]]++;
        odeg[ev[i] - M]++;
    }
    int W = 1;
    for (int P = 0; P < M; P++) {
        if (tdeg[P] > W) W = tdeg[P];
        if (odeg[P] > W) W = odeg[P];
    }
    int *through = malloc(sizeof(int) * (size_t)M * W);
    int *onl = malloc(sizeof(int) * (size_t)M * W);
    int *ft = calloc(M, sizeof(int));
    int *fo = calloc(M, sizeof(int));
    for (int i = 0; i < cnt; i++) {
        int u = eu[i], L = ev[i] - M;
        through[(size_t)u * W + ft[u]++] = L;
        onl[(size_t)L * W + fo[L]++] = u;
    }

    g_M = M; g_W = W; g_s = s;
    g_through = through; g_tdeg = tdeg;
    g_onl = onl; g_odeg = odeg;
    g_cl = calloc(M, sizeof(int));
    g_cp = calloc(M, sizeof(int));
    g_inS = calloc(M, 1);
    char *bestS = calloc(M, 1);
    int best_sz = 0;

    const double lambda = 1.3, T0 = 1.0, T1 = 0.04;
    const long long epoch = 2000000LL;
    clock_t c0 = clock();
    int stop = 0;
    while (!stop) {
        for (long long e = 0; e < epoch; e++) {
            if ((e & 4095) == 0) {
                double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
                if (el >= tl) { stop = 1; break; }
            }
            double T = T0 * pow(T1 / T0, (double)e / (double)epoch);
            int P = (int)(rnd64() % (uint64_t)M);
            if (!g_inS[P]) {
                int dv = dv_add(P);
                double dg = 1.0 - lambda * dv;
                if (dg >= 0.0 || rndu() < exp(dg / T)) do_add(P);
            } else {
                int dv = dv_rem(P);
                double dg = -1.0 - lambda * dv;
                if (dg >= 0.0 || rndu() < exp(dg / T)) do_rem(P);
            }
            if (g_V == 0 && g_sz > best_sz) {
                best_sz = g_sz;
                memcpy(bestS, g_inS, (size_t)M);
            }
        }
    }

    printf("%d\n", best_sz);
    for (int P = 0; P < M; P++) {
        if (bestS[P]) printf("%d\n", P);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S
# with every line holding <= s points of S and every point on <= s lines
# indexed by S. For each P in S add an A-vertex joined to the q+1 lines through
# P; for each j in S add a B-vertex joined to the q+1 points on line j.
# Order is 2(q^2+q+1) + 2|S|.
# ----------------------------------------------------------------------------

def _pg(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, m, point_lines, line_points):
    """True if S has distinct valid indices and all loads are <= s."""
    if len(set(S)) != len(S) or any(not (0 <= P < m) for P in S):
        return False
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _build_arc(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return 2 * m + 2 * k, E


def _arc_order(d):
    """Prime powers q with q+1 <= d, sorted by an upper bound on the order."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        m = q * q + q + 1
        ub = 2 * m + 2 * min(m, s * m // (q + 1))
        out.append((ub, q, s))
    out.sort(reverse=True)
    return out


def _c_arc_search(q, s, seed, budget):
    """Run the C annealer on PG(2, q) incidence; return the point index list S."""
    n2, edges = lib.projective_plane_incidence(q)
    text = lib.run_c(C_SOURCE, [s, seed, f"{budget:.2f}"],
                     stdin_graph=(n2, edges), timeout=budget + 30.0)
    nums = [int(x) for x in text.split()]
    if not nums:
        return []
    k = nums[0]
    return nums[1:1 + k]


def _arc_phase(d, D, seed, deadline, use_c, floor_n):
    """Return the best valid arc-extended graph (n, edges) above floor_n, or None."""
    best = None
    best_n = floor_n
    order = _arc_order(d)
    for i, (ub, q, s) in enumerate(order[:3]):
        if ub <= best_n or time.monotonic() > deadline:
            break
        m, edges, pl, lp, index = _pg(q)
        S = []
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                S = cs
        if use_c and s >= 1:
            remaining = deadline - time.monotonic()
            frac = 0.9 if i == 0 else 0.5
            cbudget = remaining * frac - 1.0
            if cbudget >= 0.5:
                try:
                    T = _c_arc_search(q, s, seed * 131 + i, cbudget)
                    if len(T) > len(S) and _loads_ok(T, s, m, pl, lp):
                        S = T
                except RuntimeError:
                    pass
        n_c, e_c = _build_arc(m, edges, pl, lp, S)
        if n_c > best_n and lib.is_valid(n_c, e_c, d, D):
            best = (n_c, e_c)
            best_n = n_c
    return best


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
# Simulated annealing over bi-Cayley voltage lifts (unchanged from parent).
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + (0.88 if D == 3 else 0.7) * time_limit
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

    # Arc-extended projective plane graphs (diameter 3). For D == 3 the C
    # annealer does the heavy search; otherwise only cheap baselines are used.
    if D >= 3:
        res = _arc_phase(d, D, seed, deadline, use_c=(D == 3), floor_n=best_n)
        if res is not None:
            consider(res[0], res[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed group voltage lifts for D != 3 (the D == 3 time goes to the arc search).
    if D != 3:
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
