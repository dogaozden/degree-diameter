import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: greedy insertion, then "forced insertion + simulated annealing repair".
#
# Greedy insertion (diameter D): a new vertex w joined to a cover set N of
# opposite-colour vertices reaches every old x within D whenever x lies in the
# (D-1)-ball of some u in N. Validity is kept.
#
# NEW in this version: when greedy insertion fails, the engine
#   1. saves the valid state,
#   2. forces a new vertex in: it picks d opposite-colour vertices by max ball
#      coverage and deletes one edge at each saturated pick (so degrees stay <= d),
#   3. anneals on the cost = number of unordered vertex pairs at distance > D,
#      using degree-preserving swaps, endpoint transfers into spare-degree
#      vertices, and additions between spare-degree vertices,
#   4. accepts only a cost-0 state (valid graph with one more vertex), otherwise
#      restores the saved state.
# Colour classes are preserved by every move, so the graph stays bipartite.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXD 32
#define MAXW (MAXN / 64)
#define ITERS 3000
#define T_START 1.5
#define T_END 0.05
#define MAXFAILS 60

static int d, D, n, W;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static int snap_n;
static int snap_deg[MAXN];
static int snap_adj[MAXN][MAXD];
static int best_n;
static int best_deg[MAXN];
static int best_adj[MAXN][MAXD];

static struct { int kind, a, b, c, e; } mv;
static clock_t t_start;
static double budget_s;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static double rnd01(void) { return rnd() / 4294967296.0; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static double elapsed(void) {
    return (double)(clock() - t_start) / CLOCKS_PER_SEC;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (adj[u][i] == v) { adj[u][i] = adj[u][--deg[u]]; break; }
    for (int i = 0; i < deg[v]; i++)
        if (adj[v][i] == u) { adj[v][i] = adj[v][--deg[v]]; break; }
}

static void compute_balls(int R) {
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) reach[v][w] = 0;
        reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
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
}

/* Number of unordered pairs at distance > D (cost; zero means valid). */
static long long bad_pairs(void) {
    W = (n + 63) >> 6;
    compute_balls(D);
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(reach[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static int covers(const uint64_t *cov, int nn) {
    for (int w = 0; w < (nn + 63) / 64; w++) {
        int bits = nn - 64 * w;
        if (bits > 64) bits = 64;
        uint64_t mask = (bits == 64) ? ~0ULL : ((1ULL << bits) - 1);
        if ((cov[w] & mask) != mask) return 0;
    }
    return 1;
}

static int gain(int u, const uint64_t *cov) {
    int g = 0;
    for (int w = 0; w < W; w++) g += popc(reach[u][w] & ~cov[w]);
    return g;
}

/* Needs reach = balls of radius D-1 for the current n. */
static int greedy_insert(int side) {
    static int cand[MAXN];
    static char used[MAXN];
    static int chosen[MAXD];
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (col[u] == 1 - side && deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    uint64_t cov[MAXW];
    memset(cov, 0, sizeof cov);
    int nch = 0;
    while (nch < d && !covers(cov, n)) {
        int best = -1;
        long long bk = 0;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (used[u]) continue;
            int g = gain(u, cov);
            if (g == 0) continue;
            long long key = (long long)g * 64 + (long long)(rnd() & 63u);
            if (key > bk) { bk = key; best = u; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) cov[w] |= reach[best][w];
    }
    for (int i = 0; i < nch; i++) used[chosen[i]] = 0;
    if (!covers(cov, n)) return 0;
    int w = n;
    n++;
    W = (n + 63) >> 6;
    col[w] = side;
    deg[w] = 0;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], w);
    return 1;
}

/* Forced insertion: a new vertex joined to the d best-covering opposite
   vertices, deleting one edge at each saturated chosen vertex. Cost may rise;
   the annealer repairs it. Needs reach = radius D-1 balls for current n. */
static void forced_insert(int side) {
    static char used[MAXN];
    static int chosen[MAXD];
    uint64_t cov[MAXW];
    memset(cov, 0, sizeof cov);
    int nch = 0;
    while (nch < d) {
        int best = -1;
        long long bk = 0;
        for (int u = 0; u < n; u++) {
            if (col[u] != 1 - side || used[u]) continue;
            int g = gain(u, cov);
            if (g == 0) continue;
            long long key = (long long)g * 64 + (long long)(rnd() & 63u);
            if (key > bk) { bk = key; best = u; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) cov[w] |= reach[best][w];
    }
    for (int i = 0; i < nch; i++) used[chosen[i]] = 0;
    for (int i = 0; i < nch; i++) {
        int u = chosen[i];
        if (deg[u] >= d) {
            int z = adj[u][rnd() % (uint32_t)deg[u]];
            del_edge(u, z);
        }
    }
    int w = n;
    n++;
    W = (n + 63) >> 6;
    col[w] = side;
    deg[w] = 0;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], w);
}

/* Moves. Each records what it changed so undo() can reverse it. */
static int try_add(void) {
    static int L0[MAXN], L1[MAXN];
    int n0 = 0, n1 = 0;
    for (int u = 0; u < n; u++) {
        if (deg[u] >= d) continue;
        if (col[u] == 0) L0[n0++] = u; else L1[n1++] = u;
    }
    if (n0 == 0 || n1 == 0) return 0;
    for (int t = 0; t < 8; t++) {
        int x = L0[rnd() % (uint32_t)n0];
        int y = L1[rnd() % (uint32_t)n1];
        if (!has_edge(x, y)) {
            add_edge(x, y);
            mv.kind = 4; mv.a = x; mv.b = y;
            return 1;
        }
    }
    return 0;
}

/* Degree-preserving swap: (a,b),(c,e) -> (a,e),(c,b), with col[a]==col[c]. */
static int try_swap(void) {
    int a = (int)(rnd() % (uint32_t)n);
    if (deg[a] == 0) return 0;
    int b = adj[a][rnd() % (uint32_t)deg[a]];
    int c = (int)(rnd() % (uint32_t)n);
    if (c == a || col[c] != col[a] || deg[c] == 0) return 0;
    int e = adj[c][rnd() % (uint32_t)deg[c]];
    if (e == b || has_edge(a, e) || has_edge(c, b)) return 0;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    mv.kind = 1; mv.a = a; mv.b = b; mv.c = c; mv.e = e;
    return 1;
}

/* Endpoint transfer: edge (x,y) becomes (c,y), c a spare-degree vertex with
   col[c]==col[x]. Moves spare degree around without changing the edge count. */
static int try_transfer(void) {
    int a = (int)(rnd() % (uint32_t)n);
    if (deg[a] == 0) return 0;
    int b = adj[a][rnd() % (uint32_t)deg[a]];
    int side = (int)(rnd() & 1u);
    int x = side ? b : a;
    int y = side ? a : b;
    static int C[MAXN];
    int nc = 0;
    for (int c = 0; c < n; c++)
        if (c != x && col[c] == col[x] && deg[c] < d && !has_edge(c, y)) C[nc++] = c;
    if (nc == 0) return 0;
    int c = C[rnd() % (uint32_t)nc];
    del_edge(x, y);
    add_edge(c, y);
    mv.kind = 2; mv.a = x; mv.b = y; mv.c = c;
    return 1;
}

static void undo(void) {
    switch (mv.kind) {
    case 1:
        del_edge(mv.a, mv.e);
        del_edge(mv.c, mv.b);
        add_edge(mv.a, mv.b);
        add_edge(mv.c, mv.e);
        break;
    case 2:
        del_edge(mv.c, mv.b);
        add_edge(mv.a, mv.b);
        break;
    case 4:
        del_edge(mv.a, mv.b);
        break;
    default:
        break;
    }
}

/* Anneal on the bad-pair cost. Returns 1 if a cost-0 (valid) state is reached. */
static int anneal(void) {
    long long cur = bad_pairs();
    for (int it = 0; it < ITERS && cur > 0; it++) {
        if ((it & 63) == 0 && elapsed() > budget_s) break;
        double T = T_START * pow(T_END / T_START, (double)it / (double)ITERS);
        int r = (int)(rnd() % 10u);
        int ok;
        if (r < 2) ok = try_add();
        else if (r < 6) ok = try_swap();
        else ok = try_transfer();
        if (!ok) continue;
        long long c2 = bad_pairs();
        long long delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = c2;
        else undo();
    }
    return cur == 0;
}

static void save_state(void) {
    snap_n = n;
    memcpy(snap_deg, deg, sizeof deg);
    memcpy(snap_adj, adj, sizeof adj);
}

static void load_state(void) {
    n = snap_n;
    memcpy(deg, snap_deg, sizeof deg);
    memcpy(adj, snap_adj, sizeof adj);
    W = (n + 63) >> 6;
}

static void save_best(void) {
    best_n = n;
    memcpy(best_deg, deg, sizeof deg);
    memcpy(best_adj, adj, sizeof adj);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    budget_s = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2 || N0 < 1 || N0 > MAXN - 2) { printf("0 0\n"); return 0; }
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
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (col[adj[u][i]] == col[u]) { printf("0 0\n"); return 0; }

    W = (n + 63) >> 6;
    save_best();
    t_start = clock();

    int fails = 0;
    while (fails < MAXFAILS && n < MAXN - 2 && elapsed() < budget_s) {
        W = (n + 63) >> 6;
        compute_balls(D - 1);
        int s0 = (int)(rnd() & 1u);
        if (greedy_insert(s0) || greedy_insert(1 - s0)) {
            fails = 0;
            if (n > best_n) save_best();
            continue;
        }
        save_state();
        forced_insert((int)(rnd() & 1u));
        if (anneal()) {
            fails = 0;
            if (n > best_n) save_best();
        } else {
            load_state();
            fails++;
        }
    }

    int m2 = 0;
    for (int u = 0; u < best_n; u++)
        for (int i = 0; i < best_deg[u]; i++)
            if (best_adj[u][i] > u) m2++;
    printf("%d %d\n", best_n, m2);
    for (int u = 0; u < best_n; u++)
        for (int i = 0; i < best_deg[u]; i++)
            if (best_adj[u][i] > u) printf("%d %d\n", u, best_adj[u][i]);
    return 0;
}
"""


def _c_grow(graph, d, D, seed, budget):
    """Run the C repair/insertion engine on graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 0.5 or d > 32:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 8.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). With d >= q+1, every old vertex
# has spare s = d - q - 1. Add a vertex per chosen point (joined to its q+1
# lines) and per chosen line (joined to its q+1 points), respecting spare
# capacity. Diameter stays 3 for any choice.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 4).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Driver. Time plan (fractions of time_limit):
#   0.00-0.25  arc-extended PG graphs with local search (D = 3)
#   0.25-0.85  C repair engine: greedy insertion + forced-insert annealing
#   D >= 4:    GQ baseline and annealed voltage lifts until 0.60, then the C engine
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

    if D >= 3:
        cands = _arc_extensions(d, start + 0.25 * time_limit,
                                random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for g in cands[:3]:
            consider(g)

    if D >= 4 and el() < 0.45 * time_limit:
        consider(_best_gq(d))

    if D >= 4:
        anneal_end = start + 0.60 * time_limit
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < anneal_end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, anneal_end, iters=400)
            if res is not None:
                consider(res)

    rem = 0.85 * time_limit - el() - 1.0
    if rem >= 1.0:
        consider(_c_grow(best, d, D, seed, rem))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
