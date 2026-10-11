import random
import time

import lib


# ----------------------------------------------------------------------------
# Main new family: cyclic Haar graphs from difference covers (diameter 3).
#
# The Haar graph H(m, S) on Z_m x {A, B} has a_i ~ b_{i+s} for s in S, so it is
# |S|-regular and bipartite. It has diameter <= 3 exactly when S - S = Z_m:
#   * a_i and a_k meet at distance 2 iff k - i is in S - S;
#   * b-b pairs are symmetric;
#   * a_i and b_j are at distance <= 3 because Z_m = S - S + S whenever S - S = Z_m.
# So a difference cover S of size d in Z_m gives a valid d-regular graph on 2m
# vertices. The Moore-type ceiling for this family is m <= d(d-1)+1.
#
# The C engine searches for such covers by simulated annealing on the number of
# uncovered nonzero residues, then climbs m upward while covers are found.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 64
#define MAXM 4096

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int K, M, nS, zeros;
static int S[MAXK];
static int inS[MAXM];
static int cnt[MAXM];

/* cnt[x] = number of ordered pairs (s, t) of distinct elements of S with s - t = x (mod M).
   zeros = number of x in 1..M-1 with cnt[x] == 0. */

static void add_el(int x) {
    for (int i = 0; i < nS; i++) {
        int t = S[i];
        int d1 = x - t; if (d1 < 0) d1 += M;
        if (cnt[d1]++ == 0) zeros--;
        int d2 = t - x; if (d2 < 0) d2 += M;
        if (cnt[d2]++ == 0) zeros--;
    }
    S[nS++] = x;
    inS[x] = 1;
}

static void rem_el(int idx) {
    int x = S[idx];
    S[idx] = S[--nS];
    inS[x] = 0;
    for (int i = 0; i < nS; i++) {
        int t = S[i];
        int d1 = x - t; if (d1 < 0) d1 += M;
        if (--cnt[d1] == 0) zeros++;
        int d2 = t - x; if (d2 < 0) d2 += M;
        if (--cnt[d2] == 0) zeros++;
    }
}

static void reset_random(void) {
    memset(cnt, 0, sizeof(int) * (size_t)M);
    memset(inS, 0, sizeof(int) * (size_t)M);
    nS = 0;
    zeros = M - 1;
    while (nS < K) {
        int r = rndint(M);
        if (!inS[r]) add_el(r);
    }
}

/* One annealing run from a random start. Returns 1 if a difference cover was found. */
static int run_anneal(long maxit, clock_t deadline) {
    reset_random();
    const double T = 0.5;
    for (long it = 0; it < maxit && zeros > 0; it++) {
        if ((it & 4095) == 0 && clock() > deadline) break;
        int idx = rndint(nS);
        int old = S[idx];
        int r;
        do { r = rndint(M); } while (inS[r]);
        int before = zeros;
        rem_el(idx);
        add_el(r);
        int delta = zeros - before;
        if (delta > 0 && rnd01() >= exp(-(double)delta / T)) {
            rem_el(nS - 1);   /* r was appended last */
            add_el(old);
        }
    }
    return zeros == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int m0 = argc > 5 ? atoi(argv[5]) : 0;
    if (d < 3 || D < 3 || d > MAXK || tl <= 0) { printf("0 0\n"); return 0; }
    K = d;
    rs ^= ((uint64_t)seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    clock_t end = clock() + (clock_t)(tl * CLOCKS_PER_SEC);
    int best_m = 0;
    int best_S[MAXK];
    int m = m0 > K ? m0 : K + 1;
    int fails = 0;
    long max_m = (long)K * (K - 1) + 1;
    while (m <= max_m && m < MAXM && clock() < end && fails < 3) {
        M = m;
        int found = 0;
        clock_t mend = clock() + (clock_t)(tl * 0.08 * CLOCKS_PER_SEC);
        if (mend > end) mend = end;
        while (clock() < mend) {
            if (run_anneal(1500000L, mend)) { found = 1; break; }
        }
        if (found) {
            best_m = m;
            memcpy(best_S, S, sizeof(int) * (size_t)K);
            fails = 0;
        } else {
            fails++;
        }
        m++;
    }

    if (best_m == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * best_m, K * best_m);
    for (int i = 0; i < best_m; i++) {
        for (int j = 0; j < K; j++) {
            printf("%d %d\n", i, best_m + (i + best_S[j]) % best_m);
        }
    }
    return 0;
}
"""


def _haar_search(d, D, seed, budget):
    """Run the C difference-cover search; return (n, edges) or None."""
    if d < 3 or D < 3:
        return None
    m0 = max(d + 1, (d * d) // 2)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", m0],
                         stdin_graph=None, timeout=budget + 10.0)
        n, edges = lib.parse_graph_text(text)
    except (RuntimeError, ValueError):
        return None
    if n <= 0 or not edges:
        return None
    return n, edges


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
# Greedy vertex insertion with ball-cover certificates (D = 3 uses radius 2).
# A new vertex w joined to chosen vertices on the opposite side reaches every
# old vertex within D if the chosen neighbourhoods cover all old vertices'
# (D-1)-balls. Adding a vertex never lengthens old distances.
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3 and d >= 3:
        # Difference-cover Haar graphs (new bold family), most of the time budget.
        budget = max(0.5, 0.45 * time_limit - 1.0)
        res = _haar_search(d, D, seed, budget)
        if res is not None:
            consider(res[0], res[1])

    if D >= 3:
        # Arc-extended projective planes, then greedy insertion on the best one.
        arcs = _arc_extensions(d, start + 0.60 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)
        if arcs:
            n_a, e_a = arcs[0]
            n2, e2 = _augment(n_a, e_a, d, D, rng, start + 0.80 * time_limit)
            consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
