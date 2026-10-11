"""Diameter-D bipartite search: voltage-lift simulated annealing above the arc-extension record.

Change from the parent: the parent's arc-extended projective plane start (394 for d=16, D=3)
is kept as the safe fallback, but the main effort now goes to a different construction.
A bipartite graph is built as a Z_m voltage lift of a base with t vertices per side. Each
base pair (i, j) carries K[i][j] distinct voltages, with row and column sums equal to d, so
every vertex has degree exactly d and parallel edges cannot occur. Because Z_m acts by
translation on each side, the diameter condition only needs BFS from the 2t base roots.
The C engine runs simulated annealing on the voltages to minimise the number of pairs at
distance greater than D. A zero-defect state is a valid graph with n = 2tm vertices. Python
only accepts a lift when it is strictly larger than the current best and passes lib.is_valid.
Every returned graph is validated, and the arc-extension start is always the fallback.
"""
import itertools
import random
import time

import lib

LIFT_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXT 8
#define MAXM 1024
#define MAXD 32
#define MAXN (2 * MAXT * MAXM)

static int t, m, d, D, n;
static int K[MAXT][MAXT];
static int V[MAXT][MAXT][MAXD];
static int bestV[MAXT][MAXT][MAXD];
static unsigned char used[MAXT][MAXT][MAXM];
static int mark[MAXN], lev[MAXN], que[MAXN];
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double unif(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

/* Neighbours of lift vertex x. A-vertex i*m+g (x < t*m) joins B-vertex (j,g+v);
   B-vertex (j,g) joins A-vertex (i,g-v) for each voltage v in V[i][j]. */
static int nbrs(int x, int *out) {
    int c = 0;
    if (x < t * m) {
        int i = x / m, g = x % m;
        for (int j = 0; j < t; j++)
            for (int k = 0; k < K[i][j]; k++) {
                int y = (g + V[i][j][k]) % m;
                out[c++] = t * m + j * m + y;
            }
    } else {
        int y0 = x - t * m;
        int j = y0 / m, g = y0 % m;
        for (int i = 0; i < t; i++)
            for (int k = 0; k < K[i][j]; k++) {
                int y = (g - V[i][j][k] + m) % m;
                out[c++] = i * m + y;
            }
    }
    return c;
}

/* Number of vertices NOT within distance D of root r. */
static int defect_root(int r) {
    int head = 0, tail = 0;
    int nb[MAXD];
    stamp++;
    que[tail++] = r;
    mark[r] = stamp;
    lev[r] = 0;
    while (head < tail) {
        int u = que[head++];
        if (lev[u] >= D) continue;
        int c = nbrs(u, nb);
        for (int k = 0; k < c; k++) {
            int w = nb[k];
            if (mark[w] != stamp) {
                mark[w] = stamp;
                lev[w] = lev[u] + 1;
                que[tail++] = w;
            }
        }
    }
    return n - tail;
}

/* Translation symmetry: roots at the 2t base vertices cover every pair. */
static int total_defect(void) {
    int s = 0;
    for (int b = 0; b < 2 * t; b++) s += defect_root(b * m);
    return s;
}

static void init_K(void) {
    int base[MAXT];
    for (int s = 0; s < t; s++) base[s] = d / t + (s < d % t ? 1 : 0);
    for (int i = 0; i < t; i++)
        for (int j = 0; j < t; j++)
            K[i][j] = base[((j - i) % t + t) % t];
}

static void rebuild_used(void) {
    memset(used, 0, sizeof(used));
    for (int i = 0; i < t; i++)
        for (int j = 0; j < t; j++)
            for (int k = 0; k < K[i][j]; k++)
                used[i][j][V[i][j][k]] = 1;
}

static void random_init(void) {
    for (int i = 0; i < t; i++)
        for (int j = 0; j < t; j++)
            for (int k = 0; k < K[i][j]; k++) {
                int x;
                do x = rndint(m); while (used[i][j][x]);
                used[i][j][x] = 1;
                V[i][j][k] = x;
            }
}

static void output_graph(void) {
    int M = 0;
    for (int i = 0; i < t; i++)
        for (int j = 0; j < t; j++) M += K[i][j] * m;
    printf("%d %d\n", n, M);
    for (int i = 0; i < t; i++)
        for (int g = 0; g < m; g++) {
            int x = i * m + g;
            int nb[MAXD];
            int c = nbrs(x, nb);
            for (int k = 0; k < c; k++) printf("%d %d\n", x, nb[k]);
        }
}

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    t = atoi(argv[1]);
    m = atoi(argv[2]);
    d = atoi(argv[3]);
    D = atoi(argv[4]);
    unsigned long seed = strtoul(argv[5], NULL, 10);
    double budget = atof(argv[6]);
    if (t < 1 || t > MAXT || m < 1 || m > MAXM || d < 1 || d > MAXD || m < d || D < 1) {
        printf("0 0\n");
        return 0;
    }
    n = 2 * t * m;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x51ED27ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 16; w++) rnd();

    init_K();
    random_init();
    int cur = total_defect();
    int best = cur;
    memcpy(bestV, V, sizeof(V));

    double t_end = elapsed() + budget;
    const long L = 30000;
    const double T0 = 4.0, T1 = 0.2;
    while (best > 0 && elapsed() < t_end) {
        for (long s = 0; s < L && best > 0; s++) {
            double T = T0 * pow(T1 / T0, (double)s / (double)L);
            int i = rndint(t), j = rndint(t);
            if (K[i][j] == 0) continue;
            int k = rndint(K[i][j]);
            int old = V[i][j][k];
            int x;
            do x = rndint(m); while (used[i][j][x]);
            used[i][j][old] = 0;
            used[i][j][x] = 1;
            V[i][j][k] = x;
            int nw = total_defect();
            int delta = nw - cur;
            if (delta <= 0 || unif() < exp(-(double)delta / T)) {
                cur = nw;
                if (cur < best) {
                    best = cur;
                    memcpy(bestV, V, sizeof(V));
                }
            } else {
                used[i][j][x] = 0;
                used[i][j][old] = 1;
                V[i][j][k] = old;
            }
        }
        /* Restart the next epoch from the best state found so far. */
        memcpy(V, bestV, sizeof(V));
        rebuild_used();
        cur = best;
    }

    if (best > 0) {
        printf("0 0\n");
        return 0;
    }
    memcpy(V, bestV, sizeof(V));
    rebuild_used();
    output_graph();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3). These are the
# safe starts. For d = 16 the conic extension gives 2*183 + 2*14 = 394.
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
# Voltage-lift search.
# ----------------------------------------------------------------------------

def _lift_candidates(d, D, n0, nmax):
    """(n, t, m) lift shapes with n > n0, n <= nmax, n <= 2*6*1024, smallest n first."""
    if d > 32:
        return []
    cap = min(nmax, 2 * 6 * 1024)
    cands = []
    for t in range(1, 7):
        m = max(d, n0 // (2 * t) + 1)
        found = 0
        while found < 2 and 2 * t * m <= cap and m <= 1024:
            cands.append((2 * t * m, t, m))
            found += 1
            m += 1
    cands.sort()
    return cands[:6]


def _lift_search(d, D, seed, t, m, budget, timeout):
    """Run the C annealer on a t-class Z_m voltage lift; return (n, edges) or (0, [])."""
    text = lib.run_c(LIFT_C, [t, m, d, D, seed, f"{budget:.2f}"], timeout=timeout)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.80 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))

    starts = []
    if D >= 3:
        starts.extend(_arc_extensions(d, t0 + 0.20 * time_limit, rng))
    if D >= 4 and time.monotonic() < t0 + 0.20 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    starts = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    if lib.is_valid(fallback[0], fallback[1], d, D):
        starts.append(fallback)
    if not starts:
        return 1, []
    best = max(starts, key=lambda g: g[0])

    # Main new search: voltage-lift annealing for graphs larger than the current best.
    cands = _lift_candidates(d, D, best[0], lib.moore_bound(d, D))
    for idx, (nn, t, m) in enumerate(cands):
        if nn <= best[0]:
            continue
        remaining = hard_end - time.monotonic()
        if remaining < 2.0:
            break
        share = remaining / (len(cands) - idx)
        try:
            n1, e1 = _lift_search(d, D, seed * 131 + idx, t, m,
                                  max(0.5, share - 1.0), share + 1.0)
        except Exception:
            continue
        if n1 > best[0] and lib.is_valid(n1, e1, d, D):
            best = (n1, e1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
