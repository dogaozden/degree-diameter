"""Diameter-3 bipartite search with cyclic Haar graphs.

Main idea: the Haar graph H(m, S) of Z_m with connection set S (|S| = d) has
2m vertices and max degree d. It has diameter at most 3 exactly when S - S covers
all of Z_m (a difference cover). Then:
  - a_i and a_k are at distance 2 when k - i is a difference of S,
  - a_0 and b_j are at distance 1 when j is in S, and otherwise at distance 3 via
    j = (s1 - s2) + s3, since S - S covers Z_m,
  - b-b distances follow the same way as a-a.
So the search is a simulated-annealing hunt for difference covers of size d in Z_m
for the largest m that works. The C engine ascends m and keeps the largest m it covers.
Arc-extended projective planes and the generalized quadrangle stay as starts, and K_{d,d}
is the fallback. Python re-checks every result with lib.is_valid.
"""
import itertools
import random
import time

import lib

C_HAAR = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 64
#define MAXM 1024

static int M, K;
static int S[MAXK];
static int inS[MAXM];
static int cnt[MAXM];
static int cost;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double cpu_now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static void set_random(void) {
    memset(inS, 0, sizeof(int) * (size_t)M);
    for (int k = 0; k < K; k++) {
        int y;
        do { y = rndint(M); } while (inS[y]);
        S[k] = y;
        inS[y] = 1;
    }
}

/* cnt[t] = number of ordered pairs (a, b), a != b in S, with a - b = t (mod M). */
static void init_cnt(void) {
    memset(cnt, 0, sizeof(int) * (size_t)M);
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            if (i != j) cnt[(S[i] - S[j] + M) % M]++;
    cost = 0;
    for (int t = 1; t < M; t++)
        if (!cnt[t]) cost++;
}

/* Remove the element at index i from S, updating counts and cost. */
static void remove_el(int i) {
    int x = S[i];
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        int a = (x - S[j] + M) % M;
        int b = (S[j] - x + M) % M;
        if (--cnt[a] == 0) cost++;
        if (--cnt[b] == 0) cost++;
    }
    inS[x] = 0;
}

/* Put value y at index i, updating counts and cost. */
static void add_el(int i, int y) {
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        int a = (y - S[j] + M) % M;
        int b = (S[j] - y + M) % M;
        if (cnt[a]++ == 0) cost--;
        if (cnt[b]++ == 0) cost--;
    }
    S[i] = y;
    inS[y] = 1;
}

/* One annealing run for the current M. Returns 1 and leaves S as a difference cover if found. */
static int sa_run(long iters, double T0, double T1) {
    set_random();
    init_cnt();
    for (long it = 0; it < iters; it++) {
        if (cost == 0) return 1;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int i = rndint(K);
        int x = S[i];
        int y;
        if (cost > 0 && (rnd() & 1)) {
            int t = -1;
            for (int tries = 0; tries < 64; tries++) {
                int c = 1 + rndint(M - 1);
                if (!cnt[c]) { t = c; break; }
            }
            if (t < 0) {
                y = rndint(M);
            } else {
                int s = S[rndint(K)];
                y = (s + t) % M;
            }
        } else {
            y = rndint(M);
        }
        if (inS[y]) continue;
        int old = cost;
        remove_el(i);
        add_el(i, y);
        int delta = cost - old;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) continue;
        remove_el(i);
        add_el(i, x);
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    unsigned long seed = strtoul(argv[2], NULL, 10);
    double budget = atof(argv[3]);
    int lo = atoi(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;

    K = d;
    if (K < 1 || K > MAXK) {
        printf("0 0\n");
        return 0;
    }
    int hi = K * (K - 1) + 1;
    if (hi > MAXM - 1) hi = MAXM - 1;
    if (lo < K + 1) lo = K + 1;

    double tend = cpu_now() + budget;
    double per_m = budget / 10.0;
    if (per_m < 0.3) per_m = 0.3;

    int bestM = 0;
    int bestS[MAXK];
    int fails = 0;
    for (M = lo; M <= hi; M++) {
        double now = cpu_now();
        if (now >= tend) break;
        double cap = now + per_m;
        if (cap > tend) cap = tend;
        int ok = 0;
        while (!ok) {
            now = cpu_now();
            if (now >= cap) break;
            ok = sa_run(150000, 1.0, 0.1);
        }
        if (ok) {
            bestM = M;
            memcpy(bestS, S, sizeof(int) * (size_t)K);
            fails = 0;
        } else {
            if (++fails >= 3) break;
        }
    }

    if (bestM == 0) {
        printf("0 0\n");
        return 0;
    }
    int m = bestM;
    printf("%d %d\n", 2 * m, m * K);
    for (int i = 0; i < m; i++)
        for (int k = 0; k < K; k++)
            printf("%d %d\n", i, m + (i + bestS[k]) % m);
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
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4), used for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
# Haar-graph difference-cover search (diameter 3).
# ----------------------------------------------------------------------------

def _haar_search(d, seed, budget, lo):
    """Run the C difference-cover search; return the Haar graph it found (may be (0, []))."""
    text = lib.run_c(C_HAAR, [d, seed, f"{budget:.2f}", lo],
                     stdin_graph=None, timeout=budget + 10.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 88% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.88 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))

    starts = []
    if D >= 3:
        starts.extend(_arc_extensions(d, t0 + 0.2 * time_limit, rng))
    if D >= 4 and time.monotonic() < t0 + 0.25 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    starts.append(fallback)
    valid = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    if not valid:
        return fallback
    best = max(valid, key=lambda g: g[0])

    # Bold step: cyclic Haar graphs from difference covers of size d.
    if D >= 3 and d >= 2:
        remaining = hard_end - time.monotonic() - 2.0
        if remaining > 3.0:
            lo = max(d + 1, (d * d) // 2)
            try:
                n1, e1 = _haar_search(d, seed * 31 + 7, remaining, lo)
                if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                    best = (n1, e1)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
