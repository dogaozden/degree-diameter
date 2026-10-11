"""Diameter-3 bipartite search: cyclic Haar-graph covers plus arc-extended projective plane starts.

New in this version: for D = 3 the main route is a cyclic Haar graph H(Z_m, S) with |S| = d.
It is d-regular on 2m vertices and has diameter 3 exactly when
  (1) S - S covers every nonzero residue mod m (a-a and b-b pairs at distance 2), and
  (2) S union (S - S + S) covers all of Z_m (a-b pairs at distance 1 or 3).
The Moore bound is m = d^2 - d + 1, reached only by perfect difference sets. For d = 16
the search aims for m >= 198, which beats the record 394 (order 2m). A C simulated-annealing
engine searches S for the largest feasible m, using bisection over m.

The previous engine (PG(2,q) arc extensions plus C augmentation) remains as a second route
and as the fallback. Every candidate is checked with lib.is_valid and the largest valid one
is returned. D >= 4 uses the old pipeline unchanged.
"""
import itertools
import random
import time

import lib

HAAR_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXM 4200

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int DD, MM;
static int S[MAXD];
static int inS[MAXM];
static int dif[MAXM];
static int mk[MAXM];
static int stamp = 0;

/* Number of uncovered requirements: nonzero x not in S-S, plus x not in S u (S-S+S). */
static int cost(void) {
    int d = DD, m = MM;
    for (int x = 0; x < m; x++) dif[x] = 0;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) {
            if (i == j) continue;
            int x = S[i] - S[j];
            if (x < 0) x += m;
            dif[x]++;
        }
    int c = 0;
    for (int x = 1; x < m; x++)
        if (!dif[x]) c++;

    stamp++;
    for (int i = 0; i < d; i++) mk[S[i]] = stamp;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) {
            int t = S[i] - S[j];
            if (t < 0) t += m;
            for (int k = 0; k < d; k++) {
                int x = t + S[k];
                if (x >= m) x -= m;
                mk[x] = stamp;
            }
        }
    for (int x = 0; x < m; x++)
        if (mk[x] != stamp) c++;
    return c;
}

/* Anneal S (0 fixed in S) for modulus m. Returns 1 and leaves S valid on success. */
static int try_m(int m, double cap) {
    if (m <= DD || m >= MAXM) return 0;
    MM = m;
    memset(inS, 0, sizeof(int) * (size_t)m);
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < DD; i++) {
        int x;
        do {
            x = rndint(m);
        } while (inS[x]);
        inS[x] = 1;
        S[i] = x;
    }
    int cur = cost();
    double t0 = now();
    double T = 1.0;
    long it = 0;
    while (cur > 0) {
        if ((it & 127) == 0) {
            double el = now() - t0;
            if (el > cap) return 0;
            T = 1.0 - 0.9 * (el / cap);
            if (T < 0.1) T = 0.1;
        }
        it++;
        int i = 1 + rndint(DD - 1);
        int x;
        do {
            x = rndint(m);
        } while (inS[x]);
        int old = S[i];
        inS[old] = 0;
        inS[x] = 1;
        S[i] = x;
        int nc = cost();
        int delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            inS[x] = 0;
            inS[old] = 1;
            S[i] = old;
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) return 1;
    DD = atoi(argv[1]);
    int mtop = atoi(argv[2]);
    int mlo = atoi(argv[3]);
    unsigned long seed = strtoul(argv[4], NULL, 10);
    double budget = atof(argv[5]);
    if (DD < 2 || DD > MAXD) {
        printf("0 0\n");
        return 0;
    }
    if (mtop > MAXM - 1) mtop = MAXM - 1;
    if (mlo < DD + 1) mlo = DD + 1;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 99991ULL;
    if (rs == 0) rs = 1;

    int lo = mlo - 1, hi = mtop;
    int bestm = 0;
    int bestS[MAXD];
    double t_start = now();
    while (lo < hi) {
        double rem = budget - (now() - t_start);
        if (rem <= 0.05) break;
        int mid = (lo + hi + 1) / 2;
        double cap = rem / 3.0;
        if (try_m(mid, cap)) {
            lo = mid;
            bestm = mid;
            memcpy(bestS, S, sizeof(int) * (size_t)DD);
        } else {
            hi = mid - 1;
        }
    }
    if (bestm == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestm, DD);
    for (int i = 0; i < DD; i++) printf("%d ", bestS[i]);
    printf("\n");
    return 0;
}
"""

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define WORDS (MAXN / 64)
#define MAXDEG 64

static int N, Dd, Dist, W;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static uint64_t ball[MAXN][WORDS];
static int mark[MAXN], lev[MAXN], bq[MAXN];
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Bitset of all vertices within distance r of src. */
static void ball_of(int src, int r, uint64_t *bits) {
    int head = 0, t = 0;
    stamp++;
    for (int i = 0; i < W; i++) bits[i] = 0;
    bq[t++] = src;
    mark[src] = stamp;
    lev[src] = 0;
    while (head < t) {
        int u = bq[head++];
        bits[u >> 6] |= 1ULL << (u & 63);
        if (lev[u] >= r) continue;
        for (int k = 0; k < deg[u]; k++) {
            int v = adj[u][k];
            if (mark[v] != stamp) {
                mark[v] = stamp;
                lev[v] = lev[u] + 1;
                bq[t++] = v;
            }
        }
    }
}

static void recompute_balls(void) {
    for (int v = 0; v < N; v++) ball_of(v, Dist - 1, ball[v]);
}

/* Try to add one new vertex on side X. Returns 1 if the graph grew. */
static int try_add(int X) {
    uint64_t U[WORDS];
    int sel[MAXN];
    int T[MAXDEG];
    int nt = 0;
    if (N + 1 >= MAXN) return 0;
    for (int i = 0; i < W; i++) U[i] = ~0ULL;
    if (N & 63) U[W - 1] = (1ULL << (N & 63)) - 1ULL;
    memset(sel, 0, sizeof(sel));
    while (nt < Dd) {
        int best = -1;
        long bestsc = -1;
        for (int v = 0; v < N; v++) {
            if (side[v] == X || deg[v] >= Dd || sel[v]) continue;
            int g = 0;
            for (int i = 0; i < W; i++) g += popc(ball[v][i] & U[i]);
            if (g <= 0) continue;
            long sc = (long)g * 8 + rndint(8);
            if (sc > bestsc) {
                bestsc = sc;
                best = v;
            }
        }
        if (best < 0) break;
        sel[best] = 1;
        T[nt++] = best;
        for (int i = 0; i < W; i++) U[i] &= ~ball[best][i];
    }
    for (int i = 0; i < W; i++)
        if (U[i]) return 0;
    if (nt == 0) return 0;
    int x = N;
    side[x] = X;
    deg[x] = nt;
    for (int k = 0; k < nt; k++) {
        int t = T[k];
        adj[x][k] = t;
        adj[t][deg[t]++] = x;
    }
    N++;
    W = (N + 63) / 64;
    recompute_balls();
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    if (Dd > MAXDEG) Dd = MAXDEG;
    Dist = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 2 || Dist < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= MAXDEG || deg[v] >= MAXDEG) continue;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }

    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, t = 0;
        bq[t++] = s;
        while (head < t) {
            int u = bq[head++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    bq[t++] = v;
                }
            }
        }
    }

    W = (N + 63) / 64;
    recompute_balls();

    double t_end = elapsed() + budget;
    int fails = 0;
    while (elapsed() < t_end && N < MAXN - 2 && fails < 4000) {
        int X = rndint(2);
        if (try_add(X)) fails = 0;
        else fails++;
    }

    int M = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) M++;
    printf("%d %d\n", N, M);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) printf("%d %d\n", v, adj[v][k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Cyclic Haar graphs of diameter 3 (new main route for D = 3).
# ----------------------------------------------------------------------------

def _haar_cyclic(d, seed, budget):
    """Search a cyclic Haar graph H(Z_m, S), |S| = d, with diameter 3; return (n, edges) or None."""
    try:
        mtop = d * d - d + 1          # Moore bound for bipartite diameter 3: m = d^2 - d + 1
        mlo = d + 1
        text = lib.run_c(HAAR_C, [d, mtop, mlo, seed, f"{budget:.2f}"],
                         timeout=budget + 10.0)
        nums = text.split()
        if len(nums) < 1 + d:
            return None
        m = int(nums[0])
        S = [int(x) for x in nums[1:1 + d]]
        if m <= 0 or len(set(s % m for s in S)) != d:
            return None
        return lib.haar_graph(m, S)
    except Exception:
        return None


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has spare capacity s = d - q - 1. Choose a point set S that is an arc, so each
# line holds at most s points of S. Add an A-vertex for each P in S (joined to
# lines through P) and a B-vertex for each j in S (joined to points on line j).
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
# C augmentation driver (old route, kept as second candidate source).
# ----------------------------------------------------------------------------

def _augment(n0, e0, d, D, seed, budget, timeout):
    """Run the C engine from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=timeout)
    return lib.parse_graph_text(text)


def _parent_build(d, D, seed, time_limit):
    """Old pipeline: arc-extended PG starts, GQ for D >= 4, then C augmentation. Always valid."""
    t0 = time.monotonic()
    hard_end = t0 + 0.80 * time_limit
    rng = random.Random(seed * 7919 + d)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))

    starts = []
    if D >= 3:
        starts.extend(_arc_extensions(d, t0 + 0.25 * time_limit, rng))
    if D >= 4 and time.monotonic() < t0 + 0.25 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    starts = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    starts.sort(key=lambda g: -g[0])
    if lib.is_valid(fallback[0], fallback[1], d, D):
        starts.append(fallback)
    if not starts:
        return fallback

    best = max(starts, key=lambda g: g[0])

    plan = starts[:3]
    for idx in range(len(plan) + 1):
        remaining = hard_end - time.monotonic()
        if remaining < 2.0:
            break
        if idx < len(plan):
            src = plan[idx]
            share = remaining / (len(plan) + 1 - idx)
        else:
            src = best
            share = remaining
        try:
            n1, e1 = _augment(src[0], src[1], d, D, seed * 31 + idx,
                              max(0.3, share - 1.0), share + 3.0)
        except Exception:
            continue
        if n1 > best[0] and lib.is_valid(n1, e1, d, D):
            best = (n1, e1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best


def build(d, D, seed, time_limit):
    """Return the largest valid (n, edges) found; the cyclic Haar search runs first for D = 3."""
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for every D >= 2 (d >= 1).
    fallback = lib.haar_graph(d, range(d))
    best = fallback if lib.is_valid(fallback[0], fallback[1], d, D) else (1, [])

    # Bold route: cyclic Haar graphs of diameter 3 (order 2m, m near d^2 - d + 1).
    if D == 3 and d >= 3:
        g = _haar_cyclic(d, seed, 0.50 * time_limit)
        if g is not None and g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = g

    # Old route with the remaining time.
    left = 0.80 * time_limit - (time.monotonic() - t0)
    if left > 3.0:
        try:
            g = _parent_build(d, D, seed, left / 0.80)
            if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
                best = g
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
