import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: difference-cover search for cyclic Haar graphs (diameter 3).
#
# H(m, S) has parts A = Z_m and B = Z_m with a_i ~ b_{i+s} for s in S, |S| = d.
# If every nonzero residue of Z_m is a difference s - t (s, t in S), then all
# A-A pairs are within distance 2, and S - S + S = Z_m gives all A-B pairs
# within distance 3. The C annealer minimises the number of uncovered
# differences with incremental counts and a Metropolis rule, and it increases m
# while covers are found. Output is the Haar graph as "n m" plus edge lines.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 64
#define MAXM 8192
#define TEMP 0.3

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static unsigned rndint(unsigned n) {
    return (unsigned)(rnd64() % n);
}

static double rndu(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    return (double)clock() / (double)CLOCKS_PER_SEC;
}

static int K, M;
static int S[MAXK];
static unsigned char inS[MAXM];
static int cnt[MAXM];
static int zeros;

static void cnt_init(void) {
    for (int x = 0; x < M; x++) cnt[x] = 0;
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            if (i != j) cnt[(S[i] - S[j] + M) % M]++;
    zeros = 0;
    for (int x = 1; x < M; x++)
        if (cnt[x] == 0) zeros++;
}

/* Replace S[i] by y (y not in S), updating counts and the number of uncovered differences. */
static void move(int i, int y) {
    int old = S[i];
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        int t = S[j];
        int a = (old - t + M) % M;
        int b = (t - old + M) % M;
        if (--cnt[a] == 0) zeros++;
        if (--cnt[b] == 0) zeros++;
    }
    inS[old] = 0;
    S[i] = y;
    inS[y] = 1;
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        int t = S[j];
        int a = (y - t + M) % M;
        int b = (t - y + M) % M;
        if (cnt[a]++ == 0) zeros--;
        if (cnt[b]++ == 0) zeros--;
    }
}

/* Look for a K-subset of Z_M covering all nonzero residues as differences. */
static int search(int m_, double deadline) {
    M = m_;
    while (1) {
        if (now_s() > deadline) return 0;
        for (int x = 0; x < M; x++) inS[x] = 0;
        for (int i = 0; i < K; i++) {
            int y;
            do {
                y = (int)rndint((unsigned)M);
            } while (inS[y]);
            inS[y] = 1;
            S[i] = y;
        }
        cnt_init();
        long it = 0;
        while (zeros > 0) {
            ++it;
            if (it > 3000000L) break;            /* restart from a fresh random set */
            if ((it & 4095) == 0 && now_s() > deadline) return 0;
            int i = (int)rndint((unsigned)K);
            int y = (int)rndint((unsigned)M);
            if (inS[y]) continue;
            int old = S[i];
            int zb = zeros;
            move(i, y);
            int delta = zeros - zb;
            if (delta > 0 && rndu() >= exp(-(double)delta / TEMP))
                move(i, old);
        }
        if (zeros == 0) return 1;
    }
}

int main(int argc, char **argv) {
    int d = argc > 1 ? atoi(argv[1]) : 0;
    int D = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long seed = argc > 3 ? strtoul(argv[3], NULL, 10) : 1UL;
    double budget = argc > 4 ? atof(argv[4]) : 10.0;

    int c;
    while ((c = getchar()) != EOF) {}  /* the start graph is not needed */

    rs ^= ((uint64_t)seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (d < 2 || d > MAXK || D < 3) {
        printf("0 0\n");
        return 0;
    }
    K = d;
    int cap = K * (K - 1) + 1;
    if (cap >= MAXM) cap = MAXM - 1;

    double deadline = now_s() + budget;
    int best_m = 0;
    int best_S[MAXK];
    int m = (int)(0.8 * cap);
    if (m < K + 1) m = K + 1;
    int fails = 0;

    while (now_s() < deadline && m >= K + 1 && m <= cap) {
        double rem = deadline - now_s();
        double slice = rem * 0.3;
        if (slice < 0.05) slice = 0.05;
        double slice_end = now_s() + slice;
        if (slice_end > deadline) slice_end = deadline;
        if (search(m, slice_end)) {
            best_m = m;
            memcpy(best_S, S, sizeof(int) * K);
            m++;
            fails = 0;
        } else {
            fails++;
            if (best_m > 0) {
                if (fails >= 2) break;
            } else {
                m--;
            }
        }
    }

    if (best_m == 0) {
        printf("0 0\n");
        return 0;
    }
    int n = 2 * best_m;
    int e = best_m * K;
    printf("%d %d\n", n, e);
    for (int i = 0; i < best_m; i++)
        for (int k = 0; k < K; k++)
            printf("%d %d\n", i, best_m + (i + best_S[k]) % best_m);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S
# such that every line holds <= s points of S and every point lies on <= s
# lines indexed by S. For each P in S add a new A-vertex joined to the q+1
# lines through P; for each j in S add a new B-vertex joined to the q+1 points
# on line j.
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
# Greedy vertex insertion with ball-cover certificates.
#
# Let R = D-1 and let ball(u) be the set of vertices within distance R of u.
# A new vertex w joined to a set N of vertices on the opposite colour class
# reaches x within D exactly when x lies in ball(u) for some u in N.
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
# Build: arc-extended PG(2,q) baseline, C difference-cover Haar search, and
# ball-cover augmentation of the arc graph.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    best = fallback
    best_n = fallback[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # Baseline: arc-extended projective planes (diameter 3).
        arcs = _arc_extensions(d, start + 0.08 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)

        if D == 4 and time.monotonic() < start + 0.2 * time_limit:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])

        # New search: C annealer for difference covers of size d in Z_m.
        # Haar graphs H(m, S) have diameter 3, so they are valid for every D >= 3.
        c_end = start + 0.70 * time_limit
        budget = c_end - time.monotonic()
        if budget > 0.2:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                timeout=budget + 0.12 * time_limit + 1.0)
                n_h, e_h = lib.parse_graph_text(out)
                if n_h > 0:
                    consider(n_h, e_h)
            except Exception:
                pass

        # Spare degree on the arc graph: greedily add vertices with ball covers.
        if arcs and time.monotonic() < start + 0.85 * time_limit:
            n_a, e_a = arcs[0]
            n2, e2 = _augment(n_a, e_a, d, D, rng, start + 0.85 * time_limit)
            consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
