import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1: arc-extended projective plane incidence graphs (diameter 3, valid).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1, so spare s = d - q - 1. New A-vertices (one per point in SA)
# join all q+1 lines through that point; new B-vertices (one per line in SB)
# join all q+1 points on that line. Loads must stay <= s. Diameter stays 3.
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
    """Randomized greedy choice of elements so every target is hit by <= s chosen elements."""
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
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
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
# Stage 0: generalized quadrangle W(q) (diameter 4, valid for D >= 4).
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
# Stage 2 (new, bold): C local search on the full bipartite graph.
#
# Instead of voltage lifts, the engine works on the graph directly:
#  - grow: add one vertex on a random side, joined to spare opposite vertices;
#  - repair: simulated annealing with degree-preserving edge swaps and greedy
#    edge additions, minimizing the number of vertex pairs at distance > D;
#  - keep the largest graph that reaches cost 0 (valid), else keep the start.
# The start graph is always returned if nothing better is found.
# ----------------------------------------------------------------------------

MAXD_PY = 40

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXD 40
#define MAXW (MAXN / 64)
#define MAXE (MAXN * MAXD / 2 + 8)

static int n, d, D, nw;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int side[MAXN];
static uint64_t bufA[MAXN][MAXW];
static uint64_t bufB[MAXN][MAXW];
static int ex[MAXE], ey[MAXE];
static int bestn = 0, beste = 0;
static int bex[MAXE], bey[MAXE];
static int bside[MAXN];
static uint64_t rs = 88172645463325252ULL;
static double limit_s = 1.0;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void del_arc(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adj[a][k] == b) {
            adj[a][k] = adj[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void del_edge(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
}

/* Number of ordered vertex pairs (v, w) with dist(v, w) > D (0 means valid). */
static long long cost(void) {
    uint64_t (*R)[MAXW] = bufA;
    uint64_t (*Q)[MAXW] = bufB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < nw; w++) R[v][w] = 0;
        R[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < D; it++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < nw; w++) Q[v][w] = R[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int w = 0; w < nw; w++) Q[v][w] |= R[u][w];
            }
        }
        uint64_t (*t)[MAXW] = R;
        R = Q;
        Q = t;
    }
    long long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += pc64(R[v][w]);
        total += n - c;
    }
    return total;
}

static long long anneal(long long cur, int iters) {
    for (int it = 0; it < iters && cur != 0; it++) {
        if ((it & 31) == 0 && elapsed() >= limit_s) break;
        double T = 0.5 * (1.0 - (double)it / (double)iters) + 0.05;
        if (rnd01() < 0.2) {
            /* greedy edge addition: never increases the cost */
            int a = -1, b = -1;
            for (int tr = 0; tr < 30; tr++) {
                int x = rndint(n);
                if (deg[x] >= d) continue;
                int y = rndint(n);
                if (side[y] == side[x] || deg[y] >= d || has_edge(x, y)) continue;
                a = x;
                b = y;
                break;
            }
            if (a < 0) continue;
            add_edge(a, b);
            cur = cost();
        } else {
            /* degree-preserving swap: (a,b),(c,e) -> (a,e),(c,b) */
            int a = rndint(n);
            if (side[a] != 0 || deg[a] == 0) continue;
            int b = adj[a][rndint(deg[a])];
            int c = rndint(n);
            if (side[c] != 0 || deg[c] == 0 || c == a) continue;
            int e = adj[c][rndint(deg[c])];
            if (b == e || has_edge(a, e) || has_edge(c, b)) continue;
            del_edge(a, b);
            del_edge(c, e);
            add_edge(a, e);
            add_edge(c, b);
            long long nc = cost();
            long long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cur = nc;
            } else {
                del_edge(a, e);
                del_edge(c, b);
                add_edge(a, b);
                add_edge(c, e);
            }
        }
    }
    return cur;
}

static void grow(void) {
    int c = rndint(2);
    int v = n;
    n++;
    nw = (n + 63) >> 6;
    side[v] = c;
    deg[v] = 0;
    static int cand[MAXN];
    int nc = 0;
    for (int y = 0; y < v; y++)
        if (side[y] != c && deg[y] < d) cand[nc++] = y;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    for (int i = 0; i < nc && deg[v] < d; i++) add_edge(v, cand[i]);
}

static void save_best(void) {
    bestn = n;
    beste = 0;
    for (int v = 0; v < n; v++) {
        bside[v] = side[v];
        for (int k = 0; k < deg[v]; k++) {
            int u = adj[v][k];
            if (u > v && beste < MAXE) {
                bex[beste] = v;
                bey[beste] = u;
                beste++;
            }
        }
    }
}

static void restore_best(void) {
    for (int v = 0; v < MAXN; v++) deg[v] = 0;
    n = bestn;
    nw = (n + 63) >> 6;
    for (int v = 0; v < n; v++) side[v] = bside[v];
    for (int i = 0; i < beste; i++) add_edge(bex[i], bey[i]);
}

static int color_graph(void) {
    static int q[MAXN];
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int u = q[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int w = adj[u][k];
                if (side[w] < 0) {
                    side[w] = 1 - side[u];
                    q[qt++] = w;
                } else if (side[w] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 0;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    limit_s = atof(argv[4]) * 0.9;
    if (d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || n0 > MAXN || m0 < 0 || m0 > MAXE) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &ex[i], &ey[i]) != 2) {
            printf("0 0\n");
            return 0;
        }
    }
    n = n0;
    nw = (n + 63) >> 6;
    for (int v = 0; v < MAXN; v++) deg[v] = 0;
    for (int i = 0; i < m0; i++) {
        int u = ex[i], v = ey[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || has_edge(u, v) ||
            deg[u] >= d || deg[v] >= d) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }
    if (!color_graph()) {
        printf("0 0\n");
        return 0;
    }

    long long cur = cost();
    if (cur == 0) save_best();

    while (elapsed() < limit_s) {
        if (bestn == 0) {
            cur = anneal(cur, 20000);
            if (cur == 0) save_best();
            continue;
        }
        restore_best();
        if (n >= MAXN) break;
        grow();
        cur = cost();
        cur = anneal(cur, 6000);
        if (cur == 0) save_best();
    }

    if (bestn > 0) {
        printf("%d %d\n", bestn, beste);
        for (int i = 0; i < beste; i++) printf("%d %d\n", bex[i], bey[i]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Stage 1: arc-extended PG graphs (valid for D >= 3).
    deadline0 = t0 + 0.3 * time_limit
    if D >= 3:
        cands = _arc_extensions(d, deadline0, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

    # Stage 0: generalized quadrangle (valid for D >= 4).
    if D >= 4 and time.monotonic() < deadline0:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Stage 2: C local search growing the best valid graph.
    remaining = time_limit - (time.monotonic() - t0)
    if d <= MAXD_PY and best_n <= 1000 and remaining > 3.0:
        if d <= 4:
            budget = 2.0
        else:
            budget = min(remaining * 0.8 - 1.0, time_limit * 0.85)
        if budget >= 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=best, timeout=budget + 4.0)
                n2, e2 = lib.parse_graph_text(out)
                if n2 > best_n and lib.is_valid(n2, e2, d, D):
                    best = (n2, e2)
                    best_n = n2
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
