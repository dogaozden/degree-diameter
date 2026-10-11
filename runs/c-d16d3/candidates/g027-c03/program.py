import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: cyclic Haar-graph search for diameter 3.
#
# The Haar graph of Z_m with connection set S (|S| = d) has parts a_i and b_j,
# with a_i ~ b_j iff j - i is in S. Its diameter is at most 3 exactly when
#   (1) S - S covers every nonzero residue (same-side pairs, distance 2), and
#   (2) S - S + S covers every residue (opposite-side pairs, distance 1 or 3).
# The search anneals S with incremental difference counts, then climbs m.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;
static int K = 0, M = 0;
static int *S = NULL;
static int *cnt = NULL;
static int cost = 0;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

/* Add (delta=+1) or remove (delta=-1) the ordered differences of the pair a, b. */
static void add_pair(int a, int b, int delta) {
    int r1 = a - b;
    if (r1 < 0) r1 += M;
    int r2 = b - a;
    if (r2 < 0) r2 += M;
    if (delta > 0) {
        if (cnt[r1]++ == 0) cost--;
        if (cnt[r2]++ == 0) cost--;
    } else {
        if (--cnt[r1] == 0) cost++;
        if (--cnt[r2] == 0) cost++;
    }
}

static int in_set(int y, int skip) {
    for (int j = 0; j < K; j++)
        if (j != skip && S[j] == y) return 1;
    return 0;
}

static int anneal(long iters, double deadline) {
    for (int i = 0; i < K; i++) {
        int y, ok;
        do {
            y = rndint(M);
            ok = 1;
            for (int j = 0; j < i; j++)
                if (S[j] == y) { ok = 0; break; }
        } while (!ok);
        S[i] = y;
    }
    memset(cnt, 0, sizeof(int) * (size_t)(M + 1));
    cost = M - 1;
    for (int i = 0; i < K; i++)
        for (int j = i + 1; j < K; j++)
            add_pair(S[i], S[j], +1);
    if (cost == 0) return 1;

    const double T0 = 1.0, T1 = 0.08;
    for (long it = 0; it < iters; it++) {
        if ((it & 4095) == 0 && now() > deadline) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int i = rndint(K);
        int y = rndint(M);
        if (in_set(y, i)) continue;
        int x = S[i];
        int c0 = cost;
        for (int j = 0; j < K; j++)
            if (j != i) add_pair(x, S[j], -1);
        for (int j = 0; j < K; j++)
            if (j != i) add_pair(y, S[j], +1);
        S[i] = y;
        int delta = cost - c0;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            if (cost == 0) return 1;
        } else {
            for (int j = 0; j < K; j++)
                if (j != i) add_pair(y, S[j], -1);
            for (int j = 0; j < K; j++)
                if (j != i) add_pair(x, S[j], +1);
            S[i] = x;
        }
    }
    return 0;
}

/* Check that S - S + S covers all residues mod M (the cross-side condition). */
static int cross_ok(void) {
    char *hit = (char *)calloc((size_t)M, 1);
    if (!hit) return 0;
    for (int a = 0; a < K; a++)
        for (int b = 0; b < K; b++)
            for (int c = 0; c < K; c++) {
                int t = S[a] - S[b] + S[c];
                t %= M;
                if (t < 0) t += M;
                hit[t] = 1;
            }
    int ok = 1;
    for (int r = 0; r < M; r++)
        if (!hit[r]) { ok = 0; break; }
    free(hit);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int ms = atoi(argv[5]);

    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;

    K = d;
    if (D != 3 || K < 2) {
        printf("0 0\n");
        return 0;
    }
    int mmax = K * (K - 1) + 1;
    if (ms < K) ms = K;
    double deadline = tl - 0.5;

    S = (int *)malloc(sizeof(int) * (size_t)K);
    int *bestS = (int *)malloc(sizeof(int) * (size_t)K);
    if (!S || !bestS) {
        printf("0 0\n");
        return 0;
    }

    int best_m = 0;
    for (int m = ms; m <= mmax; m++) {
        if (now() > deadline) break;
        M = m;
        cnt = (int *)calloc((size_t)M + 1, sizeof(int));
        if (!cnt) break;
        int found = 0;
        while (now() < deadline) {
            if (anneal(2000000L, deadline) && cross_ok()) {
                found = 1;
                break;
            }
        }
        free(cnt);
        cnt = NULL;
        if (!found) break;
        best_m = m;
        memcpy(bestS, S, sizeof(int) * (size_t)K);
    }

    if (best_m == 0) {
        printf("0 0\n");
        return 0;
    }
    M = best_m;
    printf("%d %d\n", 2 * M, M * K);
    for (int i = 0; i < M; i++)
        for (int k = 0; k < K; k++)
            printf("%d %d\n", i, M + (i + bestS[k]) % M);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3). Kept as the
# safe baseline: for d = 16 this gives the record 394.
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
# Build.
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

    if D >= 3:
        arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < start + 0.30 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Bold change: cyclic Haar-graph difference-cover search in C. Each level m
    # gives an order-2m graph with degree d. Start near half the Moore bound and
    # climb while the annealer finds valid connection sets.
    if D == 3 and d >= 2:
        left = start + 0.80 * time_limit - time.monotonic()
        if left > 3.0:
            mstart = max(d, (d * (d - 1) + 1) // 2)
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(left - 1.0, 2), mstart],
                                 timeout=left + 2.0)
                n_h, e_h = lib.parse_graph_text(text)
                consider(n_h, e_h)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
