import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: cyclic Haar graphs H(m, S) from difference covers (diameter 3).
#
# H(m, S) has a_i ~ b_{i+s} for s in S, |S| = k. If every nonzero residue of
# Z_m is a difference s - t (s, t in S), then A-A and B-B pairs are within
# distance 2 and S - S + S = Z_m gives A-B pairs within distance 3. So the graph
# is k-regular with diameter 3 and 2m vertices. The ceiling is m <= k(k-1)+1.
# The engine runs simulated annealing on the number of uncovered residues for
# increasing m, starting near 0.8 * ceiling, and prints the largest cover found.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 64
#define MAXM 4200

static uint64_t rs;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static double urand(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static int K, M;
static int S[MAXK];
static int cnt[MAXM];
static char inS[MAXM];
static int zeros;

static int md(int x) {
    x %= M;
    if (x < 0) x += M;
    return x;
}

/* Add (sign > 0) or remove (sign < 0) the differences between value val and every S[j], j != i. */
static void apply(int i, int val, int sign) {
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        int a = md(val - S[j]);
        int b = md(S[j] - val);
        if (sign < 0) {
            if (--cnt[a] == 0) zeros++;
            if (--cnt[b] == 0) zeros++;
        } else {
            if (cnt[a]++ == 0) zeros--;
            if (cnt[b]++ == 0) zeros--;
        }
    }
}

static void rand_set(void) {
    for (int i = 0; i < K; i++) {
        int y, ok;
        do {
            y = (int)(rnd() % (uint64_t)M);
            ok = 1;
            for (int j = 0; j < i; j++) {
                if (S[j] == y) { ok = 0; break; }
            }
        } while (!ok);
        S[i] = y;
    }
}

static void init_state(void) {
    memset(cnt, 0, sizeof(int) * (size_t)M);
    memset(inS, 0, (size_t)M);
    zeros = M - 1;
    for (int i = 0; i < K; i++) inS[S[i]] = 1;
    for (int i = 0; i < K; i++) {
        for (int j = 0; j < K; j++) {
            if (i == j) continue;
            int a = md(S[i] - S[j]);
            if (cnt[a]++ == 0) zeros--;
        }
    }
}

/* Returns 1 with S holding a difference cover of Z_M, or 0 if the time runs out. */
static int try_cover(double end) {
    long R = 300000L + 20000L * K;
    long it = 0;
    rand_set();
    init_state();
    while (1) {
        if (zeros == 0) return 1;
        if ((it & 1023) == 0 && (double)clock() / CLOCKS_PER_SEC > end) return 0;
        if (it >= R) {
            rand_set();
            init_state();
            it = 0;
        }
        double frac = (double)it / (double)R;
        double T = 0.6 * (1.0 - frac) + 0.05;
        it++;
        int i = (int)(rnd() % (uint64_t)K);
        int y = (int)(rnd() % (uint64_t)M);
        if (inS[y]) continue;
        int old = S[i];
        int oz = zeros;
        apply(i, old, -1);
        apply(i, y, 1);
        int delta = zeros - oz;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            inS[old] = 0;
            inS[y] = 1;
            S[i] = y;
        } else {
            apply(i, y, -1);
            apply(i, old, 1);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    int d = atoi(argv[1]);
    long seed = atol(argv[3]);
    double tl = atof(argv[4]);
    K = d;
    if (K < 2 || K > MAXK) {
        printf("0 0\n");
        return 0;
    }
    rs = 0x9E3779B97F4A7C15ULL ^ ((uint64_t)seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    double now0 = (double)clock() / CLOCKS_PER_SEC;
    double deadline = now0 + tl;

    int cap = K * (K - 1) + 1;
    if (cap > MAXM - 1) cap = MAXM - 1;

    int best_m = K;
    int bestS[MAXK];
    for (int i = 0; i < K; i++) bestS[i] = i;   /* K_{K,K}: valid fallback */

    int cur = (int)(0.8 * cap);
    if (cur < K + 1) cur = K + 1;
    if (cur > cap) cur = cap;
    int fails = 0;

    while (1) {
        double now = (double)clock() / CLOCKS_PER_SEC;
        double left = deadline - now;
        if (left < 0.05) break;
        if (cur > cap) cur = cap;
        if (cur <= K) break;
        double slice = left * 0.25;
        if (slice > left) slice = left;
        M = cur;
        if (try_cover(now + slice)) {
            best_m = cur;
            for (int i = 0; i < K; i++) bestS[i] = S[i];
            fails = 0;
            if (cur >= cap) break;
            cur++;
        } else {
            fails++;
            if (fails >= 3) {
                if (best_m > K) break;
                fails = 0;
                int nc = cur - (cur - K) / 8 - 1;
                if (nc < K + 1) nc = K + 1;
                cur = nc;
            }
        }
    }

    int m = best_m;
    printf("%d %d\n", 2 * m, m * K);
    for (int i = 0; i < m; i++) {
        for (int t = 0; t < K; t++) {
            printf("%d %d\n", i, m + (i + bestS[t]) % m);
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). With d >= q+1
# each vertex has spare capacity s = d - q - 1. Pick a point set S with every
# line holding <= s points of S and every point on <= s lines indexed by S.
# For each P in S add an A-vertex on the lines through P; for each j in S add a
# B-vertex on the points of line j. Diameter stays 3.
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
# Greedy vertex insertion with ball-cover certificates.
#
# With R = D-1 and ball(u) the vertices within distance R of u, a new vertex w
# joined to a set N on the opposite side reaches x within D exactly when x lies
# in ball(u) for some u in N. Spare degree is used to add such vertices.
# ----------------------------------------------------------------------------

def _side_colors(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _ball_masks(n, adj, R):
    """Bitmask of all vertices within distance R of each vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return reach


def _augment(n, edges, d, D, rng, deadline, max_fails=60):
    """Greedily insert vertices whose neighbourhoods cover the graph within D. Returns (n, edges)."""
    if n == 0 or D < 2:
        return n, list(edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _side_colors(n, adj)
    R = D - 1
    fails = 0
    while time.monotonic() < deadline and fails < max_fails:
        balls = _ball_masks(n, adj, R)
        full = (1 << n) - 1
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for side in sides:
            base_cand = [u for u in range(n) if color[u] == 1 - side and len(adj[u]) < d]
            if not base_cand:
                continue
            for _attempt in range(4):
                cand = base_cand[:]
                rng.shuffle(cand)
                covered = 0
                chosen = []
                pool = cand
                while covered != full and len(chosen) < d and pool:
                    best_gain, bu, bi = 0, None, -1
                    for i, u in enumerate(pool):
                        g = (balls[u] & ~covered).bit_count()
                        if g > best_gain:
                            best_gain, bu, bi = g, u, i
                    if bu is None:
                        break
                    chosen.append(bu)
                    covered |= balls[bu]
                    pool = pool[:bi] + pool[bi + 1:]
                if covered == full:
                    w = n
                    n += 1
                    adj.append(set())
                    color.append(side)
                    for u in chosen:
                        adj[u].add(w)
                        adj[w].add(u)
                    added = True
                    break
            if added:
                break
        if added:
            fails = 0
            continue
        fails += 1
        spare_a = [u for u in range(n) if len(adj[u]) < d and color[u] == 0]
        spare_b = [u for u in range(n) if len(adj[u]) < d and color[u] == 1]
        if spare_a and spare_b:
            for _ in range(20):
                u = rng.choice(spare_a)
                v = rng.choice(spare_b)
                if u != v and v not in adj[u]:
                    adj[u].add(v)
                    adj[v].add(u)
                    break
    out = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, out


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
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        # Projective plane when d-1 is a prime power (meets the Moore bound).
        if d >= 3 and lib.is_prime_power(d - 1):
            n_p, e_p = lib.projective_plane_incidence(d - 1)
            consider(n_p, e_p)

        # Arc-extended PG(2, q) graphs, then spare-degree augmentation.
        arcs = _arc_extensions(d, start + 0.05 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)
        if arcs:
            n_a, e_a = arcs[0]
            n2, e2 = _augment(n_a, e_a, d, D, rng, start + 0.10 * time_limit)
            consider(n2, e2)

        # Main search: difference-cover Haar graphs, searched in C.
        elapsed = time.monotonic() - start
        budget = 0.75 * time_limit - elapsed - 0.5
        if 2 <= d <= 60 and budget > 0.3:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                timeout=budget + 2.0)
                n_c, e_c = lib.parse_graph_text(out)
                consider(n_c, e_c)
            except (RuntimeError, ValueError):
                pass
    else:
        arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)
        if arcs:
            n_a, e_a = arcs[0]
            n2, e2 = _augment(n_a, e_a, d, D, rng, start + 0.30 * time_limit)
            consider(n2, e2)

        if D >= 4 and time.monotonic() < start + 0.30 * time_limit:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])

        search_end = start + 0.55 * time_limit
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < search_end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, search_end, iters=400)
            if res is not None:
                consider(res[0], res[1])

    if time.monotonic() < start + 0.85 * time_limit:
        n_f, e_f = _augment(best[0], best[1], d, D, rng, start + 0.85 * time_limit)
        consider(n_f, e_f)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
