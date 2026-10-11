import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S
# with every line holding <= s points of S and every point lying on <= s lines
# indexed by S. For each P in S add a new A-vertex joined to the q+1 lines
# through P; for each j in S add a new B-vertex joined to the q+1 points on j.
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
# Greedy vertex insertion with ball-cover certificates ("_augment").
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
# C engine: cyclic Haar graphs from difference covers (D = 3).
#
# H(m, S) with |S| = d and S - S = Z_m (every nonzero residue is a difference)
# is d-regular bipartite with 2m vertices and diameter 3. The C search anneals
# over d-subsets S of Z_m, minimising the number of uncovered nonzero residues,
# and climbs m upward while it keeps succeeding. Moore ceiling: m <= d(d-1)+1.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int K, M, CAP;
static int *S, *cnt, *bestS;
static int zeros;

static int modm(int x) {
    x %= M;
    return x < 0 ? x + M : x;
}

static void dec_c(int x) {
    if (--cnt[x] == 0) zeros++;
}

static void inc_c(int x) {
    if (cnt[x] == 0) zeros--;
    cnt[x]++;
}

static void rebuild(void) {
    int i, j, x;
    memset(cnt, 0, sizeof(int) * (size_t)M);
    for (i = 0; i < K; i++)
        for (j = 0; j < K; j++)
            if (i != j) cnt[modm(S[i] - S[j])]++;
    zeros = 0;
    for (x = 1; x < M; x++)
        if (cnt[x] == 0) zeros++;
}

static void replace_elem(int i, int y) {
    int old = S[i], j;
    for (j = 0; j < K; j++) {
        if (j != i) {
            int t = S[j];
            dec_c(modm(old - t));
            dec_c(modm(t - old));
        }
    }
    S[i] = y;
    for (j = 0; j < K; j++) {
        if (j != i) {
            int t = S[j];
            inc_c(modm(y - t));
            inc_c(modm(t - y));
        }
    }
}

static int in_set(int y) {
    int j;
    for (j = 0; j < K; j++)
        if (S[j] == y) return 1;
    return 0;
}

static void randomize(void) {
    int i, j, y, dup;
    for (i = 0; i < K; i++) {
        do {
            y = rndint(M);
            dup = 0;
            for (j = 0; j < i; j++)
                if (S[j] == y) dup = 1;
        } while (dup);
        S[i] = y;
    }
    rebuild();
}

/* Try to find a K-subset of Z_m covering all nonzero differences before deadline. */
static int attempt(int m, double deadline) {
    long long it = 0, since_restart = 0;
    const double T = 0.3;
    M = m;
    randomize();
    for (;;) {
        if (zeros == 0) return 1;
        if ((it & 4095) == 0 && now_s() > deadline) return 0;
        it++;
        if (++since_restart >= 300000) {
            since_restart = 0;
            randomize();
            continue;
        }
        {
            int i = rndint(K);
            int y = rndint(M);
            int old, before, delta;
            if (in_set(y)) continue;
            old = S[i];
            before = zeros;
            replace_elem(i, y);
            delta = zeros - before;
            if (delta > 0 && rnd01() >= exp(-(double)delta / T)) replace_elem(i, old);
        }
    }
}

int main(int argc, char **argv) {
    double t0, end, budget;
    int D, m, best = 0, i, j;
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    K = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 2654435761ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (i = 0; i < 20; i++) rnd64();
    budget = atof(argv[4]);
    if (D != 3 || K < 2 || budget <= 0) {
        printf("0 0\n");
        return 0;
    }
    CAP = K * (K - 1) + 1;
    S = malloc(sizeof(int) * (size_t)K);
    cnt = malloc(sizeof(int) * (size_t)(CAP + 2));
    bestS = malloc(sizeof(int) * (size_t)K);
    if (!S || !cnt || !bestS) {
        printf("0 0\n");
        return 0;
    }
    t0 = now_s();
    end = t0 + budget;
    m = (int)(0.8 * CAP);
    if (m < K + 1) m = K + 1;
    if (m > CAP) m = CAP;
    for (;;) {
        double nw = now_s(), left = end - nw, slice;
        if (left < 0.2) break;
        slice = left * 0.3;
        if (slice < 1.0) slice = left;
        if (attempt(m, nw + slice)) {
            best = m;
            memcpy(bestS, S, sizeof(int) * (size_t)K);
            if (m >= CAP) break;
            m++;
        } else if (best == 0) {
            m -= 3;
            if (m < K + 1) m = K + 1;
        }
    }
    if (best == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", 2 * best, best * K);
    for (i = 0; i < best; i++)
        for (j = 0; j < K; j++)
            printf("%d %d\n", i, best + (i + bestS[j]) % best);
    return 0;
}
"""


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
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    arcs = []
    if D >= 3:
        arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)

    if D == 3 and d >= 2:
        budget = 0.72 * time_limit - (time.monotonic() - start)
        if budget > 2:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"], timeout=budget + 8)
                n_h, e_h = lib.parse_graph_text(out)
                consider(n_h, e_h)
            except Exception:
                pass

    if D >= 2 and time.monotonic() < start + 0.85 * time_limit:
        n_f, e_f = _augment(best[0], best[1], d, D, rng, start + 0.85 * time_limit)
        consider(n_f, e_f)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
