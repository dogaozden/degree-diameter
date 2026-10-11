import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# NEW (bold): Haar-type bipartite graphs over abelian groups.
#
# Let G be an abelian group of order N and S a k-subset (k = d). Join
# A-vertex x to B-vertex y iff y - x lies in S. Then:
#   * two A-vertices x, x' are at distance 2 iff x - x' = s1 - s2 for some
#     s1 != s2 in S, so if S - S covers G every same-side pair is within 2;
#   * an A-vertex x and a B-vertex z are at distance <= 3 when z - x lies in
#     S - S + S, which contains G + s3 = G once S - S = G.
# So the single condition S - S = G gives a valid bipartite graph of max degree
# k, diameter 3 and order 2N. The search is simulated annealing over k-sets
# that maximise the number of nonzero residues covered by differences.
# This is a different family from the projective-plane arc extensions below,
# which stay in the fallback pool so the result never drops below them.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double wall_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}
static double T0w = 0.0;
static double now_s(void) { return wall_s() - T0w; }

static double run_end = 0.0;  /* time (seconds since start) at which the current search stops */

static int K;        /* degree = |S| */
static int NMAX;     /* K*(K-1)+1, the difference-cover bound */
static int N;        /* current group order */
static int GA, GB;   /* group Z_GA x Z_GB, element x = i*GB + j */
static int *subt;    /* subt[x*N+y] = x - y, capacity NMAX*NMAX */
static int *cnt;     /* cnt[g]: ordered pairs (s,t), s != t, with s - t = g */
static int *S;       /* current connection set */
static char *inS;
static int unc;      /* number of nonzero g with cnt[g] == 0 */

static int *bestS;
static int bestN = 0, bestA = 1;

static int gsub(int x, int y) {
    int i = x / GB, j = x % GB, p = y / GB, q = y % GB;
    int a = ((i - p) % GA + GA) % GA;
    int b = ((j - q) % GB + GB) % GB;
    return a * GB + b;
}

static int gadd(int x, int y) {
    int i = x / GB, j = x % GB, p = y / GB, q = y % GB;
    return ((i + p) % GA) * GB + (j + q) % GB;
}

static void setup_group(int n, int a) {
    N = n;
    GA = a;
    GB = n / a;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            subt[x * N + y] = gsub(x, y);
}

/* Remove the element at position pos from the difference counts. */
static void drop(int pos) {
    int x = S[pos];
    for (int j = 0; j < K; j++) {
        if (j == pos) continue;
        int g = subt[x * N + S[j]];
        if (--cnt[g] == 0) unc++;
        g = subt[S[j] * N + x];
        if (--cnt[g] == 0) unc++;
    }
}

/* Put element x at position pos and add its differences. */
static void put(int pos, int x) {
    S[pos] = x;
    for (int j = 0; j < K; j++) {
        if (j == pos) continue;
        int g = subt[x * N + S[j]];
        if (cnt[g]++ == 0) unc--;
        g = subt[S[j] * N + x];
        if (cnt[g]++ == 0) unc--;
    }
}

/* Returns 1 if a difference cover was found, 0 if iterations ran out, -1 on time out. */
static int anneal(long iters, double Ta, double Tb) {
    for (int x = 0; x < N; x++) inS[x] = 0;
    for (int i = 0; i < K; i++) {
        int x;
        do { x = rndint(N); } while (inS[x]);
        inS[x] = 1;
        S[i] = x;
    }
    for (int g = 0; g < N; g++) cnt[g] = 0;
    unc = N - 1;
    for (int i = 0; i < K; i++)
        for (int j = 0; j < i; j++) {
            int g = subt[S[i] * N + S[j]];
            if (cnt[g]++ == 0) unc--;
            g = subt[S[j] * N + S[i]];
            if (cnt[g]++ == 0) unc--;
        }
    if (unc == 0) return 1;
    for (long it = 0; it < iters; it++) {
        if ((it & 1023) == 0 && now_s() > run_end) return -1;
        double T = Ta * pow(Tb / Ta, (double)it / (double)iters);
        int pos = rndint(K);
        int x = rndint(N);
        if (inS[x]) continue;
        int old = S[pos];
        int before = unc;
        drop(pos);
        put(pos, x);
        int delta = unc - before;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            inS[old] = 0;
            inS[x] = 1;
            if (unc == 0) return 1;
        } else {
            drop(pos);
            put(pos, old);
        }
    }
    return 0;
}

/* Try to find a difference cover of Z_n-type groups of order n until slice_end. */
static int try_order(int n, double slice_end) {
    int divs[512], nd = 0;
    for (int a = 1; a <= n && nd < 512; a++)
        if (n % a == 0) divs[nd++] = a;
    double saved = run_end;
    run_end = slice_end;
    int ok = 0;
    while (now_s() < slice_end) {
        int a = divs[rndint(nd)];
        setup_group(n, a);
        int r = anneal(200000L, 1.0, 0.12);
        if (r == 1) {
            memcpy(bestS, S, sizeof(int) * (size_t)K);
            bestN = n;
            bestA = a;
            ok = 1;
            break;
        }
        if (r < 0) break;
    }
    run_end = saved;
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);

    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    rs += 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    T0w = wall_s();

    K = d;
    if (D < 3 || K < 2) {
        printf("0 0\n");
        return 0;
    }
    NMAX = K * (K - 1) + 1;
    subt = malloc(sizeof(int) * (size_t)NMAX * (size_t)NMAX);
    cnt = malloc(sizeof(int) * (size_t)(NMAX + 1));
    inS = malloc((size_t)(NMAX + 1));
    S = malloc(sizeof(int) * (size_t)K);
    bestS = malloc(sizeof(int) * (size_t)K);
    if (!subt || !cnt || !inS || !S || !bestS) return 1;

    /* Ascending phase: small orders succeed quickly; stop after three failures in a row. */
    double slice = budget * 0.08;
    if (slice > 3.0) slice = 3.0;
    if (slice < 0.2) slice = 0.2;
    int fails = 0;
    int start_n = K > 2 ? K : 2;
    for (int n = start_n; n <= NMAX && fails < 3; n++) {
        if (now_s() > budget) break;
        double end = now_s() + slice;
        if (end > budget) end = budget;
        if (try_order(n, end)) fails = 0;
        else fails++;
    }

    /* Final phase: push on from the best order with the remaining time. */
    while (bestN > 0 && bestN + 1 <= NMAX && now_s() < budget - 0.05) {
        if (!try_order(bestN + 1, budget)) break;
    }

    if (bestN <= 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(bestN, bestA);
    printf("%d %d\n", 2 * bestN, bestN * K);
    for (int x = 0; x < bestN; x++)
        for (int t = 0; t < K; t++)
            printf("%d %d\n", x, bestN + gadd(x, bestS[t]));
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), from the parent.
# Kept as a second candidate family and as a safe fallback.
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
# Greedy vertex insertion with ball-cover certificates (from the parent).
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
# Build
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

    if D == 2 or d < 2:
        return best

    # 1. Projective plane incidence when d - 1 is a prime power (diameter 3).
    if d - 1 >= 2 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))

    # 2. Arc-extended projective plane graphs (the parent's record source).
    arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
    arcs.sort(key=lambda t: -t[0])
    for n_c, e_c in arcs[:3]:
        consider(n_c, e_c)
    arc_best = arcs[0] if arcs else None

    # 3. Bold new family: difference-cover Haar graphs searched by C annealing.
    c_budget = start + 0.70 * time_limit - time.monotonic() - 1.0
    if c_budget > 0.5:
        try:
            txt = lib.run_c(
                C_SOURCE,
                [d, D, seed, round(c_budget, 2)],
                timeout=max(1.0, start + 0.80 * time_limit - time.monotonic()),
            )
            n_h, e_h = lib.parse_graph_text(txt)
            if n_h > 0:
                consider(n_h, e_h)
        except Exception:
            pass

    # 4. Greedy vertex insertion on the best arc graph, with the remaining time.
    if arc_best is not None and time.monotonic() < start + 0.90 * time_limit:
        n_a, e_a = arc_best
        n2, e2 = _augment(n_a, e_a, d, D, rng, start + 0.90 * time_limit)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
