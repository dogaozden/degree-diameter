import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated-annealing repair with grow-on-success.
#
# The bipartition is fixed (BFS colouring of the input). Every edge joins the two
# colour classes. State cost = number of unordered vertex pairs at distance > D,
# computed with radius-D bitset balls. Moves pick a random bad pair (u, v), then
# add an edge (x, y) with x in {u, v} and y on the opposite colour. If x or y is
# saturated, a random incident edge is removed first. Accepted moves follow the
# Metropolis rule with a geometric cooling schedule. When cost reaches 0 the
# current graph is valid, so it is snapshotted and one vertex is appended with
# degree 0 on the smaller colour class. The engine prints the largest snapshot.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1200
#define MAXD 40
#define MAXW (MAXN / 64 + 1)
#define SNAPMAX (MAXN * MAXD / 2)

static int n, d, D;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t bufA[MAXN][MAXW];
static uint64_t bufB[MAXN][MAXW];
static uint64_t (*R)[MAXW] = bufA;
static uint64_t (*S)[MAXW] = bufB;
static uint64_t rs = 88172645463325252ULL;
static int snapN = -1, snapM = 0;
static int snapU[SNAPMAX], snapV[SNAPMAX];

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static double urand(void) {
    return (double)(rnd() & 0xFFFFFFu) / 16777216.0;
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void drop_from(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void remove_edge(int u, int v) {
    drop_from(u, v);
    drop_from(v, u);
}

/* Returns number of unordered pairs at distance > D; leaves balls in R. */
static long long compute_cost(void) {
    int Wd = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < Wd; w++) R[v][w] = 0;
        R[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < Wd; w++) S[v][w] = R[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < Wd; w++) S[v][w] |= R[u][w];
            }
        }
        uint64_t (*tmp)[MAXW] = R;
        R = S;
        S = tmp;
    }
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < Wd; w++) c += popc64(R[v][w]);
        tot += n - c;
    }
    return tot / 2;
}

/* Uniformly pick a bad pair using the current balls in R. */
static int pick_bad(int *pu, int *pv) {
    for (int t = 0; t < 60; t++) {
        int a = (int)(rnd() % (uint32_t)n);
        int cnt = 0, pick = -1;
        for (int b = 0; b < n; b++) {
            if (b == a) continue;
            if (!((R[a][b >> 6] >> (b & 63)) & 1ULL)) {
                cnt++;
                if (rnd() % (uint32_t)cnt == 0) pick = b;
            }
        }
        if (pick >= 0) {
            *pu = a;
            *pv = pick;
            return 1;
        }
    }
    return 0;
}

static void snapshot(void) {
    int m = 0;
    for (int u = 0; u < n; u++) {
        for (int i = 0; i < deg[u]; i++) {
            if (adj[u][i] > u && m < SNAPMAX) {
                snapU[m] = u;
                snapV[m] = adj[u][i];
                m++;
            }
        }
    }
    snapN = n;
    snapM = m;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 5; i++) rnd();

    if (d < 2 || d > MAXD || D < 2 || budget <= 0.0) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2) { printf("0 0\n"); return 0; }
    if (N0 < 1 || N0 >= MAXN - 64) { printf("0 0\n"); return 0; }
    n = N0;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    static int queue[MAXN];
    for (int s = 0; s < n; s++) col[s] = -1;
    int bip = 1;
    for (int s = 0; s < n && bip; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt && bip) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    queue[qt++] = v;
                } else if (col[v] == col[u]) {
                    bip = 0;
                    break;
                }
            }
        }
    }
    if (!bip) { printf("0 0\n"); return 0; }

    clock_t t0 = clock();
    long long cur = compute_cost();
    if (cur == 0) snapshot();

    long long iters = 0;
    double frac = 0.0;
    const double T0 = 2.0, T1 = 0.2;

    while (1) {
        if ((iters & 127) == 0) {
            frac = (double)(clock() - t0) / CLOCKS_PER_SEC / budget;
            if (frac >= 1.0) break;
        }
        iters++;

        if (cur == 0) {
            snapshot();
            if (n >= MAXN - 2) break;
            int c0 = 0, c1 = 0;
            for (int v = 0; v < n; v++) { if (col[v]) c1++; else c0++; }
            int w = n;
            n++;
            col[w] = (c0 > c1) ? 1 : 0;
            deg[w] = 0;
            cur = compute_cost();
            continue;
        }

        double temp = T0 * pow(T1 / T0, frac);
        int u, v;
        if (!pick_bad(&u, &v)) break;

        int x = (rnd() & 1u) ? u : v;
        int other = (x == u) ? v : u;
        int y;
        if (col[u] != col[v] && (rnd() & 1u)) {
            y = other;
        } else {
            int tries = 0;
            do {
                y = (int)(rnd() % (uint32_t)n);
                tries++;
            } while ((col[y] == col[x] || y == x) && tries < 1000);
            if (col[y] == col[x] || y == x) continue;
        }
        if (has_edge(x, y)) continue;

        int ra[2], rb[2], nr = 0;
        if (deg[x] >= d) {
            int z = adj[x][rnd() % (uint32_t)deg[x]];
            remove_edge(x, z);
            ra[nr] = x; rb[nr] = z; nr++;
        }
        if (deg[y] >= d) {
            int z = adj[y][rnd() % (uint32_t)deg[y]];
            remove_edge(y, z);
            ra[nr] = y; rb[nr] = z; nr++;
        }
        add_edge(x, y);

        long long c2 = compute_cost();
        long long delta = c2 - cur;
        int acc = 0;
        if (delta <= 0) acc = 1;
        else if (urand() < exp(-(double)delta / temp)) acc = 1;

        if (acc) {
            cur = c2;
        } else {
            remove_edge(x, y);
            for (int i = 0; i < nr; i++) add_edge(ra[i], rb[i]);
            compute_cost();   /* restore balls for the reverted state */
        }
    }

    if (snapN < 1) { printf("0 0\n"); return 0; }
    printf("%d %d\n", snapN, snapM);
    for (int i = 0; i < snapM; i++) printf("%d %d\n", snapU[i], snapV[i]);
    return 0;
}
"""


def _c_repair(graph, d, D, seed, budget):
    """Run the C annealing repair from graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 1.0 or not (1 <= d <= 40):
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 6.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Starting constructions.
#
# Arc-extended projective plane incidence graphs (diameter 3). Start from
# PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex has degree
# q+1, so spare s = d - q - 1. A-vertices attach to chosen points (each line
# takes at most s of them); B-vertices attach to chosen lines (each point takes
# at most s of them). The sides are independent.
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
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice so that every target is hit <= s times."""
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
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
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


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4), used for D >= 4.
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
# Driver.
#   1. Safe fallback K_{d,d} (valid for D >= 2).
#   2. Best structured start: arc-extended PG graphs (D = 3) or W(q) (D >= 4).
#   3. C annealing repair with grow-on-success, using most of the time budget.
#   4. Every candidate is checked with lib.is_valid before it is kept.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2

    def elapsed():
        return time.monotonic() - start

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        arcs = _arc_extensions(d, start + 0.10 * time_limit,
                               random.Random(seed * 7919 + d))
        for g in sorted(arcs, key=lambda t: -t[0]):
            consider(g)
    elif D >= 4:
        consider(_best_gq(d))

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = min(0.80 * time_limit - elapsed() - 1.0, time_limit - elapsed() - 8.0)
    if budget > 2.0:
        consider(_c_repair(best, d, D, seed, budget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
