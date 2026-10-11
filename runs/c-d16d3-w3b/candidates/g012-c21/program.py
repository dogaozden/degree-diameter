import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# NEW: simulated-annealing "grow" engine (C).
#
# Start from a valid graph G. Repeat: add one vertex w of a random colour and
# join it to random spare vertices of the opposite colour. Then anneal over
# edge moves (remove a random edge, add a random spare cross edge, or add a
# spare cross edge outright) with cost = number of vertex pairs at distance
# greater than D. Bipartiteness and the degree cap are kept by construction.
# If the cost reaches 0 the state is saved as the new best; otherwise it is
# rolled back to the last valid state. This searches for graphs with MORE
# vertices than the arc construction, which is saturated for its family.
# Distances are computed with bitset balls (D rounds), which is cheap for n ~ 400.
# ----------------------------------------------------------------------------

C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXD 40
#define MAXW (MAXN / 64)
#define ITERS 4000
#define MAXFAIL 40

static int n, d, D;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static int sdeg[MAXN];
static int sadj[MAXN][MAXD];
static int scol[MAXN];
static int sn;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd64() % 1000000ULL) / 1000000.0; }

static int popc(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void rem_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (adj[u][i] == v) { adj[u][i] = adj[u][--deg[u]]; break; }
    for (int i = 0; i < deg[v]; i++)
        if (adj[v][i] == u) { adj[v][i] = adj[v][--deg[v]]; break; }
}

/* Number of unordered pairs at distance > D (unreachable counts as bad). */
static int bad_pairs(void) {
    int W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) reach[v][w] = 0;
        reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = reach[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= reach[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) reach[v][w] = nxt[v][w];
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(reach[v][w]);
        total += n - c;
    }
    return (int)(total / 2);
}

static void add_vertex(int c) {
    static int cand[MAXN];
    int w = n++;
    col[w] = c;
    deg[w] = 0;
    int nc = 0;
    for (int x = 0; x < w; x++)
        if (col[x] != c && deg[x] < d) cand[nc++] = x;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    for (int i = 0; i < nc && deg[w] < d; i++) {
        int x = cand[i];
        if (deg[x] < d) add_edge(w, x);
    }
}

/* Simulated annealing on edge moves. Returns the final bad-pair count. */
static int anneal(int iters, double T0) {
    int cur = bad_pairs();
    for (int it = 0; it < iters && cur > 0; it++) {
        double T = T0 * (1.0 - (double)it / iters) + 0.02;

        /* Pure addition move: join a random spare cross pair if one exists. */
        if (rndi(8) == 0) {
            int a = -1, b = -1;
            for (int t = 0; t < 100; t++) {
                int x = rndi(n), y = rndi(n);
                if (x == y || col[x] == col[y]) continue;
                if (deg[x] >= d || deg[y] >= d || has_edge(x, y)) continue;
                a = x; b = y; break;
            }
            if (a >= 0) {
                add_edge(a, b);
                int c2 = bad_pairs();
                if (c2 <= cur || rnd01() < exp(-(c2 - cur) / T)) cur = c2;
                else rem_edge(a, b);
            }
            continue;
        }

        /* Swap move: remove a random edge, add a random spare cross edge. */
        int u = -1, v = -1;
        for (int t = 0; t < 100; t++) {
            int p = rndi(n);
            if (deg[p] == 0) continue;
            u = p; v = adj[p][rndi(deg[p])];
            break;
        }
        if (u < 0) continue;
        rem_edge(u, v);
        int a = -1, b = -1;
        for (int t = 0; t < 200; t++) {
            int x = rndi(n), y = rndi(n);
            if (x == y || col[x] == col[y]) continue;
            if (deg[x] >= d || deg[y] >= d || has_edge(x, y)) continue;
            a = x; b = y; break;
        }
        if (a < 0) { add_edge(u, v); continue; }
        add_edge(a, b);
        int c2 = bad_pairs();
        if (c2 <= cur || rnd01() < exp(-(c2 - cur) / T)) {
            cur = c2;
        } else {
            rem_edge(a, b);
            add_edge(u, v);
        }
    }
    return cur;
}

static void save_state(void) {
    sn = n;
    memcpy(sdeg, deg, sizeof(deg));
    memcpy(sadj, adj, sizeof(adj));
    memcpy(scol, col, sizeof(col));
}

static void restore_state(void) {
    n = sn;
    memcpy(deg, sdeg, sizeof(deg));
    memcpy(adj, sadj, sizeof(adj));
    memcpy(col, scol, sizeof(col));
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2) { printf("0 0\n"); return 0; }
    if (N0 < 1 || N0 > MAXN / 2) { printf("0 0\n"); return 0; }
    n = N0;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    /* 2-colour by BFS. */
    static int queue[MAXN];
    for (int s = 0; s < n; s++) col[s] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) { col[v] = 1 - col[u]; queue[qt++] = v; }
            }
        }
    }

    save_state();  /* the input is the initial best state */
    clock_t t0 = clock();
    int fails = 0;
    while (fails < MAXFAIL && n < MAXN - 1) {
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        add_vertex(rndi(2));
        int res = anneal(ITERS, 1.2);
        if (res == 0) {
            save_state();
            fails = 0;
        } else {
            restore_state();
            fails++;
        }
    }
    restore_state();  /* the last saved state is the best valid one */

    int m2 = 0;
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) m2++;
    printf("%d %d\n", n, m2);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) printf("%d %d\n", u, adj[u][i]);
    return 0;
}
"""


def _c_grow(graph, d, D, seed, budget):
    """Run the C annealing grow engine; return (n, edges) or None on failure."""
    if graph is None or budget < 1.0 or d > 40:
        return None
    try:
        out = lib.run_c(C_GROW, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 5.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with d >= q+1 it has spare s = d - q - 1.
# A-side: a set SA of points, each joined to a new vertex adjacent to the q+1
#         lines through it. Each line holds <= s points of SA.
# B-side: a set SB of lines, symmetric.
# ----------------------------------------------------------------------------

_LS_ITERS = 30000


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
    """Randomized greedy load-constrained set."""
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


def _local_search(m, s, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the load-constrained set problem."""
    if s < 1:
        return list(S)
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= s:
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc."""
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
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for q in qs:
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

        SA = _local_search(m, s, point_lines, SA, rng, deadline, _LS_ITERS)
        SB = _local_search(m, s, line_points, SB, rng, deadline, _LS_ITERS)

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
#   D = 3: arc-extended PG graphs (about 25% of the time), then the C
#          annealing grow engine from the best arc graph (rest of the budget).
#   D >= 4: GQ baseline. Haar fallback K_{d,d} otherwise.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    def el():
        return time.monotonic() - start

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        cands = _arc_extensions(d, start + 0.25 * time_limit,
                                random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for g in cands[:3]:
            consider(g)

        budget = 0.85 * time_limit - el()
        if budget >= 1.0:
            consider(_c_grow(best, d, D, seed, budget))
    elif D >= 4:
        consider(_best_gq(d))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
