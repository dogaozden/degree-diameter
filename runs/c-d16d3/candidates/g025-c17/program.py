import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C stage: greedy vertex insertion with a set-cover test.
#
# A new vertex v on side X joins a set N of spare vertices on the opposite side.
# Every existing vertex w is then within distance D of v exactly when w lies
# within distance D-1 of N. Existing distances can only shrink, so the old graph
# stays valid. The engine picks N greedily by coverage of balls of radius D-1,
# with random tie-breaking, and keeps inserting until it stalls.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4096
#define MAXDEG 64
#define NW (MAXN / 64)

static int n = 0, d = 3, D = 3;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int col[MAXN];
static int nw = 1;
static uint64_t rs = 88172645463325252ULL;
static uint64_t full[NW];

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int pc64(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int stamp_of[MAXN];
static int stamp_now = 0;
static int bq[MAXN], bd[MAXN];

static void ball(int u, int radius, uint64_t *bits) {
    int head = 0, tail = 0;
    for (int w = 0; w < nw; w++) bits[w] = 0;
    stamp_now++;
    bq[tail] = u; bd[tail] = 0; tail++;
    stamp_of[u] = stamp_now;
    while (head < tail) {
        int x = bq[head], dx = bd[head];
        head++;
        bits[x >> 6] |= (uint64_t)1 << (x & 63);
        if (dx >= radius) continue;
        for (int k = 0; k < deg[x]; k++) {
            int y = adj[x][k];
            if (stamp_of[y] != stamp_now) {
                stamp_of[y] = stamp_now;
                bq[tail] = y; bd[tail] = dx + 1; tail++;
            }
        }
    }
}

static int cand[MAXN];
static uint64_t balls[MAXN][NW];

static void set_full(void) {
    for (int w = 0; w < NW; w++) full[w] = 0;
    for (int u = 0; u < n; u++) full[u >> 6] |= (uint64_t)1 << (u & 63);
}

static int try_insert(int tries) {
    nw = (n + 63) >> 6;
    set_full();
    int X = (int)(rnd() & 1u);
    int want = 1 - X;
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (col[u] == want && deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int i = 0; i < nc; i++) ball(cand[i], D - 1, balls[i]);

    for (int t = 0; t < tries; t++) {
        uint64_t covered[NW];
        for (int w = 0; w < nw; w++) covered[w] = 0;
        int taken[MAXN];
        memset(taken, 0, sizeof(int) * (size_t)nc);
        int chosen[MAXDEG];
        int nch = 0;
        while (nch < d) {
            int best = -1;
            long long bestscore = -1;
            for (int i = 0; i < nc; i++) {
                if (taken[i]) continue;
                int g = 0;
                for (int w = 0; w < nw; w++)
                    g += pc64(balls[i][w] & ~covered[w]);
                if (g == 0) continue;
                long long sc = (long long)g * 256 + (long long)(rnd() & 255u);
                if (sc > bestscore) { bestscore = sc; best = i; }
            }
            if (best < 0) break;
            taken[best] = 1;
            chosen[nch++] = best;
            for (int w = 0; w < nw; w++) covered[w] |= balls[best][w];
        }
        int ok = 1;
        for (int w = 0; w < nw; w++)
            if (covered[w] != full[w]) { ok = 0; break; }
        if (!ok) continue;

        int v = n++;
        col[v] = X;
        deg[v] = 0;
        for (int k = 0; k < nch; k++) {
            int u = cand[chosen[k]];
            adj[v][deg[v]++] = u;
            adj[u][deg[u]++] = v;
        }
        return 1;
    }
    return 0;
}

static void read_graph(void) {
    int m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; return; }
    if (n < 0 || n > MAXN - 64) { n = 0; return; }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= MAXDEG || deg[v] >= MAXDEG) continue;
        int dup = 0;
        for (int k = 0; k < deg[u]; k++)
            if (adj[u][k] == v) { dup = 1; break; }
        if (dup) continue;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }
    for (int u = 0; u < n; u++) col[u] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        bq[tail++] = s;
        while (head < tail) {
            int x = bq[head++];
            for (int k = 0; k < deg[x]; k++) {
                int y = adj[x][k];
                if (col[y] < 0) {
                    col[y] = 1 - col[x];
                    bq[tail++] = y;
                }
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (d < 1) d = 1;
    if (d > MAXDEG) d = MAXDEG;
    if (D < 1) D = 1;
    rs = seed * 0x9E3779B97F4A7C15ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;

    read_graph();

    clock_t t0 = clock();
    int fails = 0;
    const int LIMIT = 4000;
    while (n >= 2 && n < MAXN - 2 && fails < LIMIT) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (el >= budget) break;
        if (try_insert(6)) fails = 0;
        else fails++;
    }

    int m2 = 0;
    for (int u = 0; u < n; u++) m2 += deg[u];
    m2 /= 2;
    printf("%d %d\n", n, m2);
    for (int u = 0; u < n; u++)
        for (int k = 0; k < deg[u]; k++) {
            int v = adj[u][k];
            if (u < v) printf("%d %d\n", u, v);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions: arc-extended projective plane incidence graphs (D = 3),
# plus the generalized quadrangle W(q) for D = 4. Both are valid starts for the
# C insertion stage.
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


_LP = None  # line_points for the current q


def _arc_graph(m, edges, point_lines, S):
    """Build the extended graph: old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in _LP[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    global _LP
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        _LP = line_points
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
        n_c, e_c = _arc_graph(m, edges, point_lines, S)
        out.append((n_c, e_c))
    return out


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


def build(d, D, seed, time_limit):
    start = time.monotonic()

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

    rng = random.Random(seed * 7919 + d)

    if D >= 3:
        for n_c, e_c in _arc_extensions(d, start + 0.25 * time_limit, rng):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Insertion search in C, starting from the best valid graph found so far.
    elapsed = time.monotonic() - start
    budget = 0.6 * time_limit - elapsed
    if budget >= 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                             stdin_graph=best, timeout=0.85 * time_limit - elapsed)
            n2, e2 = lib.parse_graph_text(text)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
