"""Diameter-D bipartite search: arc-extended projective plane starts plus a C annealing grower.

The parent grew graphs by greedy vertex addition. This version changes the search itself.
A graph is treated as a state with max degree d and n vertices. The C engine adds one vertex
on a random side, connects it to d opposite-side vertices, and then runs simulated annealing
on the number of vertex pairs at distance more than D. The moves are degree-preserving or
degree-bounded edge changes (add, steal an edge from a full endpoint, or a 2-switch), so the
bipartition and max degree are always kept. A grown graph is kept only when the penalty
reaches zero, which means it is a valid graph. Otherwise the engine restores the last valid
graph. Starts are arc-extended PG(2,q) incidence graphs for D = 3, W(q) for D >= 4, and
K_{d,d} as a safe fallback. Python re-checks everything with lib.is_valid.
"""
import itertools
import random
import time

import lib

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 1024
#define MAXW (MAXN / 64)
#define MAXD 64
#define LOGMAX 16

static int N, Dd, Rad, W;
static int side[MAXN];
static int deg[MAXN];
static int adj[MAXN][MAXD];
static uint64_t bufA[MAXN][MAXW], bufB[MAXN][MAXW];
static int Av[MAXN], Bv[MAXN], nA, nB;

static int bestN;
static int bestSide[MAXN], bestDeg[MAXN];
static int bestAdj[MAXN][MAXD];

typedef struct { int type, u, v; } Op;
static Op logv[LOGMAX];
static int nlog;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int isadj(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void del_from(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adj[a][k] == b) {
            adj[a][k] = adj[a][--deg[a]];
            return;
        }
    }
}

static void del_edge(int a, int b) {
    del_from(a, b);
    del_from(b, a);
}

static void L_add(int a, int b) {
    add_edge(a, b);
    logv[nlog++] = (Op){0, a, b};
}

static void L_del(int a, int b) {
    del_edge(a, b);
    logv[nlog++] = (Op){1, a, b};
}

static void undo(void) {
    for (int i = nlog - 1; i >= 0; i--) {
        Op o = logv[i];
        if (o.type == 0) del_edge(o.u, o.v);
        else add_edge(o.u, o.v);
    }
    nlog = 0;
}

/* a must be on side 0, b on side 1, and a, b non-adjacent.
   Adds the edge (a, b), freeing capacity by stealing an edge from a full endpoint if needed.
   Returns 0 if no change was made. */
static int connect_pair(int a, int b) {
    if (deg[a] < Dd && deg[b] < Dd) {
        L_add(a, b);
        return 1;
    }
    if (deg[a] < Dd && deg[b] >= Dd) {
        int c = adj[b][rndint(deg[b])];
        L_del(c, b);
        L_add(a, b);
        return 1;
    }
    if (deg[a] >= Dd && deg[b] < Dd) {
        int f = adj[a][rndint(deg[a])];
        L_del(a, f);
        L_add(a, b);
        return 1;
    }
    int c = adj[b][rndint(deg[b])];
    int f = adj[a][rndint(deg[a])];
    if (c == a || f == b) return 0;
    if (isadj(c, f)) return 0;
    L_del(c, b);
    L_del(a, f);
    L_add(a, b);
    L_add(c, f);
    return 1;
}

static int connect_any(int x, int y) {
    return side[x] == 0 ? connect_pair(x, y) : connect_pair(y, x);
}

/* Number of unordered vertex pairs at distance more than Rad. */
static int bad_count(void) {
    W = (N + 63) / 64;
    uint64_t (*F)[MAXW] = bufA;
    uint64_t (*G)[MAXW] = bufB;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < W; i++) F[v][i] = 0;
        F[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < Rad; r++) {
        for (int v = 0; v < N; v++) {
            for (int i = 0; i < W; i++) G[v][i] = F[v][i];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int i = 0; i < W; i++) G[v][i] |= F[u][i];
            }
        }
        uint64_t (*t)[MAXW] = F;
        F = G;
        G = t;
    }
    long miss = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int i = 0; i < W; i++) c += popc(F[v][i]);
        miss += N - c;
    }
    return (int)(miss / 2);
}

static void rebuild_lists(void) {
    nA = nB = 0;
    for (int v = 0; v < N; v++) {
        if (side[v] == 0) Av[nA++] = v;
        else Bv[nB++] = v;
    }
}

/* Simulated annealing on the bad-pair count. Returns the final count (0 means valid). */
static int anneal(double slice, int cur) {
    if (nA == 0 || nB == 0) return cur;
    double t0 = now();
    const double T0 = 1.5, T1 = 0.12;
    double T = T0;
    long it = 0;
    while (cur > 0) {
        if ((it & 15) == 0) {
            double el = now() - t0;
            if (el >= slice) break;
            T = T0 * pow(T1 / T0, el / slice);
        }
        it++;
        int a = Av[rndint(nA)];
        int b = Bv[rndint(nB)];
        if (isadj(a, b)) continue;
        nlog = 0;
        if (!connect_pair(a, b)) {
            nlog = 0;
            continue;
        }
        int nb = bad_count();
        int delta = nb - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = nb;
        else undo();
        nlog = 0;
    }
    return cur;
}

static void save_best(void) {
    bestN = N;
    memcpy(bestSide, side, sizeof(int) * N);
    memcpy(bestDeg, deg, sizeof(int) * N);
    memcpy(bestAdj, adj, sizeof(int) * MAXD * N);
}

static void load_best(void) {
    N = bestN;
    memcpy(side, bestSide, sizeof(int) * N);
    memcpy(deg, bestDeg, sizeof(int) * N);
    memcpy(adj, bestAdj, sizeof(int) * MAXD * N);
    rebuild_lists();
}

static void output(void) {
    int M = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) M++;
    printf("%d %d\n", N, M);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) printf("%d %d\n", v, adj[v][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    Dd = d > MAXD ? MAXD : d;
    Rad = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 99991ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 4 || Rad < 1 || Dd < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= Dd || deg[v] >= Dd || isadj(u, v)) continue;
        add_edge(u, v);
    }

    for (int v = 0; v < N; v++) side[v] = -1;
    static int q[MAXN];
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    q[t++] = v;
                }
            }
        }
    }

    double t_end = now() + budget;
    rebuild_lists();
    int cur = bad_count();
    if (cur > 0) {
        double s0 = budget * 0.25;
        if (s0 < 0.5) s0 = 0.5;
        cur = anneal(s0, cur);
    }

    if (cur == 0) {
        save_best();
        double slice = budget * 0.10;
        if (slice < 1.0) slice = 1.0;
        if (slice > 8.0) slice = 8.0;
        int fails = 0;
        while (now() < t_end && N < MAXN - 2 && fails < 40) {
            double rem = t_end - now();
            double sl = slice < rem ? slice : rem;
            if (sl < 0.3) break;

            int cA = 0, cB = 0;
            for (int v = 0; v < N; v++) {
                if (side[v] == 0) cA++;
                else cB++;
            }
            int X;
            if (fails > 0) X = rndint(2);
            else if (cA < cB) X = 0;
            else if (cB < cA) X = 1;
            else X = rndint(2);

            int x = N++;
            side[x] = X;
            deg[x] = 0;
            rebuild_lists();
            int *opp = (X == 0) ? Bv : Av;
            int no = (X == 0) ? nB : nA;
            int got = 0;
            for (int tr = 0; tr < 40 * Dd && got < Dd && no > 0; tr++) {
                int y = opp[rndint(no)];
                if (isadj(x, y)) continue;
                nlog = 0;
                if (connect_any(x, y)) got++;
                nlog = 0;
            }
            rebuild_lists();
            cur = bad_count();
            cur = anneal(sl, cur);
            if (cur == 0) {
                save_best();
                fails = 0;
            } else {
                load_best();
                cur = 0;
                fails++;
                slice *= 1.3;
                if (slice > budget) slice = budget;
            }
        }
    }
    output();
    return 0;
}
"""


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
# Build driver.
# ----------------------------------------------------------------------------

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

    # Already at the Moore bound: nothing to gain from searching.
    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = (hard_end - time.monotonic()) - 1.0
    if budget >= 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed * 31 + 7, f"{budget:.2f}"],
                             stdin_graph=best, timeout=budget + 6.0)
            n1, e1 = lib.parse_graph_text(text)
            if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                best = (n1, e1)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
