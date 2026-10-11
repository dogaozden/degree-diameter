import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: the voltage-lift annealing is gone. The Python side now builds
# the strongest algebraic starts it can (arc-extended projective planes, the
# W(q) quadrangle), and a C engine grows the best one.
#
# C engine ("grow and repair"):
#   * Grow: pick k disjoint edges (a_i, b_i), a_i on side 0, b_i on side 1.
#     Remove them, add a new vertex x (side 0) joined to all b_i, and a new
#     vertex y (side 1) joined to all a_i. Every old degree is unchanged and
#     the order rises by 2. Bipartiteness is preserved.
#   * Repair: simulated annealing with degree-preserving 2-switches (plus edge
#     additions into spare degree). Cost = number of unordered pairs at
#     distance > D, computed with bitsets. Zero cost means valid.
#   * Whenever the state is valid, its order is saved. Failed repairs roll
#     back to the best saved graph.
#
# The output is always re-checked in Python with lib.is_valid. On any failure
# the Python fallback (K_{d,d} or the best construction) is returned.
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


def _loads_ok(S, s, m, nbr):
    """True if every target t is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice of elements so that every target is hit <= s times."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
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


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Yield (n, edges) candidates of diameter 3 for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
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


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXD 32
#define W 18
#define ANNEAL_IT 6000

static int N, DEG, DIA;
static unsigned char side[MAXN];
static unsigned char A[MAXN][MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXD];
static uint64_t RA[MAXN][W], RB[MAXN][W];

static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static clock_t deadline;
static int timeup(void) { return clock() > deadline; }

static void add_edge(int u, int v) {
    A[u][v] = A[v][u] = 1;
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
}
static void del_nb(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (nb[u][i] == v) { nb[u][i] = nb[u][--deg[u]]; return; }
}
static void rem_edge(int u, int v) {
    A[u][v] = A[v][u] = 0;
    del_nb(u, v);
    del_nb(v, u);
}

static int pc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* number of unordered pairs at distance > DIA */
static long cost(void) {
    int nw = (N + 63) / 64;
    uint64_t (*cur)[W] = RA, (*nxt)[W] = RB;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < nw; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < DIA; s++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < nw; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = nb[v][i];
                for (int w = 0; w < nw; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[W] = cur; cur = nxt; nxt = t;
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += pc(cur[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

static int mv_type, mu, mb, mc, me;

static int move_switch(void) {
    int u = rndint(N);
    if (deg[u] == 0) return 0;
    int b = nb[u][rndint(deg[u])];
    int c = rndint(N);
    if (c == u || side[c] != side[u] || deg[c] == 0) return 0;
    int e = nb[c][rndint(deg[c])];
    if (A[u][e] || A[c][b]) return 0;
    rem_edge(u, b);
    rem_edge(c, e);
    add_edge(u, e);
    add_edge(c, b);
    mv_type = 1; mu = u; mb = b; mc = c; me = e;
    return 1;
}

static int move_add(void) {
    int u = rndint(N), c = rndint(N);
    if (u == c || side[u] == side[c] || deg[u] >= DEG || deg[c] >= DEG || A[u][c]) return 0;
    add_edge(u, c);
    mv_type = 2; mu = u; mc = c;
    return 1;
}

static void undo(void) {
    if (mv_type == 1) {
        rem_edge(mu, me);
        rem_edge(mc, mb);
        add_edge(mu, mb);
        add_edge(mc, me);
    } else {
        rem_edge(mu, mc);
    }
}

static long anneal(long iters, double T) {
    long c = cost();
    for (long it = 0; it < iters && c > 0; it++) {
        if ((it & 255) == 0 && timeup()) break;
        int ok = (rnd01() < 0.9) ? move_switch() : move_add();
        if (!ok) continue;
        long c2 = cost();
        if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) c = c2;
        else undo();
    }
    return c;
}

static unsigned char used[MAXN];

/* insert two vertices x (side 0), y (side 1) by splitting k disjoint edges */
static int grow(int k) {
    if (N + 2 > MAXN) return 0;
    if (k > DEG) k = DEG;
    if (k < 1) return 0;
    memset(used, 0, N);
    int ua[MAXD], ub[MAXD], cnt = 0;
    for (int tries = 0; tries < 4000 && cnt < k; tries++) {
        int a = rndint(N);
        if (side[a] != 0 || deg[a] == 0 || used[a]) continue;
        int b = nb[a][rndint(deg[a])];
        if (used[b]) continue;
        used[a] = used[b] = 1;
        ua[cnt] = a; ub[cnt] = b; cnt++;
    }
    if (cnt < k) return 0;
    int x = N, y = N + 1;
    side[x] = 0; side[y] = 1;
    deg[x] = deg[y] = 0;
    N += 2;
    for (int i = 0; i < cnt; i++) {
        rem_edge(ua[i], ub[i]);
        add_edge(x, ub[i]);
        add_edge(ua[i], y);
    }
    return 1;
}

static int bN = 0, bM = 0;
static int bu[MAXN * MAXD / 2 + 16], bv[MAXN * MAXD / 2 + 16];
static unsigned char bside[MAXN];

static void save_best(void) {
    bN = N; bM = 0;
    for (int u = 0; u < N; u++)
        for (int i = 0; i < deg[u]; i++) {
            int v = nb[u][i];
            if (u < v) { bu[bM] = u; bv[bM] = v; bM++; }
        }
    memcpy(bside, side, N);
}

static void load_best(void) {
    for (int u = 0; u < N; u++) {
        for (int i = 0; i < deg[u]; i++) A[u][nb[u][i]] = 0;
        deg[u] = 0;
    }
    N = bN;
    memcpy(side, bside, N);
    for (int i = 0; i < bM; i++) add_edge(bu[i], bv[i]);
}

static int load(int n, int m) {
    N = n;
    memset(A, 0, sizeof(A));
    for (int u = 0; u < N; u++) deg[u] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v || A[u][v]) return 0;
        if (deg[u] >= DEG || deg[v] >= DEG) return 0;
        add_edge(u, v);
    }
    return 1;
}

static int bipart(void) {
    static int col[MAXN];
    static int stk[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp) {
            int u = stk[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (col[v] < 0) { col[v] = 1 - col[u]; stk[sp++] = v; }
                else if (col[v] == col[u]) return 0;
            }
        }
    }
    for (int v = 0; v < N; v++) side[v] = (unsigned char)col[v];
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIA = atoi(argv[2]);
    uint64_t sd = (uint64_t)atoll(argv[3]);
    rs ^= sd * 0x2545F4914F6CDD1DULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    deadline = clock() + (clock_t)(tl * 0.9 * CLOCKS_PER_SEC);
    if (DEG < 1 || DEG > MAXD || DIA < 1) { printf("0 0\n"); return 0; }

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || m < 0 || n > MAXN - 2) {
        printf("0 0\n");
        return 0;
    }
    if (!load(n, m) || !bipart()) { printf("0 0\n"); return 0; }

    int hasBest = 0;
    int curValid = (cost() == 0);
    if (curValid) { save_best(); hasBest = 1; }

    while (!timeup()) {
        if (!curValid) {
            double T = 0.3 + 1.2 * rnd01();
            long c = anneal(ANNEAL_IT, T);
            if (c == 0) {
                curValid = 1;
            } else {
                if (timeup()) break;
                if (hasBest) {
                    load_best();
                    curValid = 1;
                }
                continue;
            }
        }
        /* state is valid here */
        if (!hasBest || N > bN) { save_best(); hasBest = 1; }
        if (!grow(DEG)) {
            load_best();
            continue;
        }
        curValid = 0;
    }

    if (!hasBest) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bN, bM);
    for (int i = 0; i < bM; i++) printf("%d %d\n", bu[i], bv[i]);
    return 0;
}
"""


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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

    # Diameter-3 starts: arc-extended projective planes.
    if D >= 3:
        rng = random.Random(seed * 7919 + d)
        cands = _arc_extensions(d, t0 + 0.2 * time_limit, rng)
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

    # Diameter-4 start: generalized quadrangle W(q).
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Bold step: C grow-and-repair search from the best start.
    elapsed = time.monotonic() - t0
    budget = 0.8 * time_limit - elapsed - 3.0
    if budget >= 1.0:
        timeout = min(budget + 6.0, 0.95 * time_limit - elapsed)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best, timeout=max(1.0, timeout))
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
