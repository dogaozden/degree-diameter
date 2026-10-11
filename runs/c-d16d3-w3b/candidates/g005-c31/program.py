import itertools
import math
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1600
#define MAXDEG 128
#define MAXE (MAXN * MAXDEG / 2 + 16)
#define MAXW ((MAXN + 63) / 64)

static int D = 3, DEG = 3;
static int N = 0;
static unsigned char adj[MAXN][MAXN];
static int nb[MAXN][MAXDEG];
static int deg[MAXN];
static int side[MAXN];
static int sideList[2][MAXN];
static int sideCnt[2];
static uint64_t bufA[MAXN * MAXW], bufB[MAXN * MAXW];
static uint64_t rs = 88172645463325252ULL;
static int bestN = 0, bestM = 0;
static int bestU[MAXE], bestV[MAXE];
static double LIMIT = 1.0;
static long ITERS = 120000;
static const double T0 = 2.0, T1 = 0.2;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int rndint(int n) { return n <= 0 ? 0 : (int)(rnd64() % (uint64_t)n); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int a, int b) {
    adj[a][b] = adj[b][a] = 1;
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void rem_from(int v, int u) {
    for (int i = 0; i < deg[v]; i++) {
        if (nb[v][i] == u) {
            nb[v][i] = nb[v][--deg[v]];
            return;
        }
    }
}

static void del_edge(int a, int b) {
    adj[a][b] = adj[b][a] = 0;
    rem_from(a, b);
    rem_from(b, a);
}

static void rebuild_side_lists(void) {
    sideCnt[0] = sideCnt[1] = 0;
    for (int v = 0; v < N; v++) sideList[side[v]][sideCnt[side[v]]++] = v;
}

static void add_vertex(int s) {
    int v = N++;
    side[v] = s;
    deg[v] = 0;
    sideList[s][sideCnt[s]++] = v;
}

static int color_graph(void) {
    static int stack[MAXN];
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int top = 0;
        stack[top++] = s;
        while (top > 0) {
            int u = stack[--top];
            for (int i = 0; i < deg[u]; i++) {
                int w = nb[u][i];
                if (side[w] < 0) {
                    side[w] = 1 - side[u];
                    stack[top++] = w;
                } else if (side[w] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Number of ordered (vertex, far vertex) pairs at distance > D. Zero means valid. */
static long cost_fn(void) {
    int W = (N + 63) >> 6;
    uint64_t *cur = bufA, *nxt = bufB;
    for (int v = 0; v < N; v++) {
        uint64_t *c = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c[w] = 0;
        c[v >> 6] = 1ULL << (v & 63);
    }
    for (int step = 0; step < D; step++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) o[w] = c[w];
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s = cur + (size_t)nb[v][i] * W;
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *c = cur + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += popc(c[w]);
        bad += N - cnt;
    }
    return bad;
}

static int pick_def(int s, int bias) {
    if (sideCnt[s] == 0) return -1;
    if (bias >= 0 && side[bias] == s && deg[bias] < DEG && rnd01() < 0.3) return bias;
    for (int t = 0; t < 40; t++) {
        int c = sideList[s][rndint(sideCnt[s])];
        if (deg[c] < DEG) return c;
    }
    return -1;
}

/* Adding a cross edge never increases distances, so it is always accepted. */
static int try_add_move(void) {
    int x = N - 1;
    int a = pick_def(0, x), b = pick_def(1, x);
    if (a < 0 || b < 0 || adj[a][b]) return 0;
    add_edge(a, b);
    return 1;
}

/* Move one endpoint of a random edge to another vertex on the same side. Degrees are preserved
   at both ends except the new endpoint gains one and the old loses one. */
static void try_transfer(double T, long *cost) {
    int v = -1;
    for (int t = 0; t < 100; t++) {
        int c = rndint(N);
        if (deg[c] > 0) {
            v = c;
            break;
        }
    }
    if (v < 0) return;
    int u = nb[v][rndint(deg[v])];
    int p, q;
    if (rnd64() & 1) {
        p = v;
        q = u;
    } else {
        p = u;
        q = v;
    }
    int s = side[p];
    int x = N - 1;
    int pp = -1;
    if (side[x] == s && x != p && deg[x] < DEG && !adj[q][x] && rnd01() < 0.3) {
        pp = x;
    } else {
        for (int t = 0; t < 60; t++) {
            int c = sideList[s][rndint(sideCnt[s])];
            if (c != p && deg[c] < DEG && !adj[q][c]) {
                pp = c;
                break;
            }
        }
    }
    if (pp < 0) return;
    del_edge(p, q);
    add_edge(pp, q);
    long c2 = cost_fn();
    long delta = c2 - *cost;
    if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
        *cost = c2;
        return;
    }
    del_edge(pp, q);
    add_edge(p, q);
}

static long anneal(long cost) {
    for (long it = 0; it < ITERS && cost > 0; it++) {
        if ((it & 127) == 0 && now() >= LIMIT) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)ITERS);
        if (rnd01() < 0.25) {
            if (try_add_move()) cost = cost_fn();
        } else {
            try_transfer(T, &cost);
        }
    }
    return cost;
}

static void save_best(void) {
    bestN = N;
    bestM = 0;
    for (int u = 0; u < N; u++)
        for (int v = u + 1; v < N; v++)
            if (adj[u][v] && bestM < MAXE) {
                bestU[bestM] = u;
                bestV[bestM] = v;
                bestM++;
            }
}

static void restore_best(void) {
    memset(adj, 0, sizeof(adj));
    for (int v = 0; v < MAXN; v++) deg[v] = 0;
    N = bestN;
    for (int e = 0; e < bestM; e++) add_edge(bestU[e], bestV[e]);
    rebuild_side_lists();
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    LIMIT = atof(argv[4]);
    DEG = d;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN - 200 || m < 0 || d < 1 || d > MAXDEG || D < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || adj[u][v] || deg[u] >= DEG || deg[v] >= DEG) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }
    if (!color_graph()) {
        printf("0 0\n");
        return 0;
    }
    rebuild_side_lists();
    if (cost_fn() != 0) {
        printf("0 0\n");
        return 0;
    }
    save_best();

    while (now() < LIMIT && N < MAXN - 2) {
        add_vertex(rndint(2));
        long c = cost_fn();
        c = anneal(c);
        if (c == 0) save_best();
        else restore_best();
    }

    printf("%d %d\n", bestN, bestM);
    for (int e = 0; e < bestM; e++) printf("%d %d\n", bestU[e], bestV[e]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare capacity
# s = d - q - 1. Choose a point set S such that every line contains at most s
# points of S and every point lies on at most s lines indexed by S. For each
# P in S add a new A-vertex joined to all q+1 lines through P; for each j in S
# add a new B-vertex joined to all q+1 points on line j. Diameter stays 3.
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


def _arc_graph(m, edges, point_lines, S, line_points):
    """Build the extended graph: old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):  # S is also a set of line indices (same vectors)
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
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
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
        n_c, e_c = _arc_graph(m, edges, point_lines, S, line_points)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Spare-capacity fill (diameter 3).
#
# A new vertex x on one side of a bipartite graph is at distance 2 from every
# vertex of its own side only if its neighbourhood T (on the other side) covers
# that whole side. We greedily pick T among opposite-side vertices with spare
# degree and accept x only if the whole graph still passes lib.is_valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """2-colouring of a bipartite graph given by adjacency lists."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _fill(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover the opposite side; return (n, edges)."""
    edges = list(edges)
    fails = 0
    while time.monotonic() < deadline and fails < 400:
        adj = [[] for _ in range(n)]
        for u, v in edges:
            adj[u].append(v)
            adj[v].append(u)
        deg = [len(a) for a in adj]
        col = _bipartition(n, adj)
        c = rng.randrange(2)
        uncovered = {v for v in range(n) if col[v] == 1 - c}
        cand = [v for v in range(n) if col[v] == c and deg[v] < d]
        chosen = []
        chosen_set = set()
        while uncovered and len(chosen) < d:
            best_v = None
            best_key = None
            for v in cand:
                if v in chosen_set:
                    continue
                g = 0
                for u in adj[v]:
                    if u in uncovered:
                        g += 1
                if g == 0:
                    continue
                key = (g, rng.random())
                if best_key is None or key > best_key:
                    best_key = key
                    best_v = v
            if best_v is None:
                break
            chosen.append(best_v)
            chosen_set.add(best_v)
            for u in adj[best_v]:
                uncovered.discard(u)
        if uncovered:
            fails += 1
            continue
        new_edges = edges + [(v, n) for v in chosen]
        if lib.is_valid(n + 1, new_edges, d, D):
            edges = new_edges
            n += 1
            fails = 0
        else:
            fails += 1
    return n, edges


# ----------------------------------------------------------------------------
# Cross-edge saturation.
#
# Adding an edge between the two colour classes of a bipartite graph keeps it
# bipartite and can only shrink distances, so diameter stays valid. It only
# needs both endpoints to have spare degree.
# ----------------------------------------------------------------------------

def _cross_saturate(n, edges, d, n_new, rng):
    """Add random cross edges (touching a vertex >= n_new) while degree allows; return new edge list."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    col = _bipartition(n, adj)
    have = set()
    for u, v in edges:
        have.add((u, v) if col[u] == 0 else (v, u))
    L = [v for v in range(n) if col[v] == 0 and deg[v] < d]
    R = [v for v in range(n) if col[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in L for b in R
             if (a, b) not in have and (a >= n_new or b >= n_new)]
    rng.shuffle(pairs)
    out = list(edges)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            out.append((a, b))
            deg[a] += 1
            deg[b] += 1
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
# C repair search: keep a valid graph and try to attach one more vertex,
# rewiring edges by annealing on the number of pairs farther than D apart.
# ----------------------------------------------------------------------------

def _c_repair(d, D, graph, budget, seed):
    """Run the C engine on a valid graph for `budget` CPU seconds; return (n, edges)."""
    n, edges = graph
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"], stdin_graph=(n, edges),
                     timeout=budget + 4.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.88 * time_limit  # all work, including the C stage, finishes before this
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Arc-extended projective plane graphs. Diameter 3, so valid for all D >= 3.
    if D >= 3:
        cands = _arc_extensions(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    if D >= 3 and best_n > 2:
        n_arc = best_n

        # Stage 1: plain greedy fill.
        n_f, e_f = _fill(best_n, best[1], d, D, start + 0.10 * time_limit,
                         random.Random(seed * 104729 + d))
        consider(n_f, e_f)

        # Stage 2: repeated cross-saturation followed by fill, each trial checked exactly.
        trial_rng = random.Random(seed * 31337 + d)
        chain_deadline = start + 0.20 * time_limit
        while time.monotonic() < chain_deadline:
            n_b, e_b = best
            e_sat = _cross_saturate(n_b, e_b, d, n_arc, trial_rng)
            if len(e_sat) == len(e_b):
                break
            n_s, e_s = _fill(n_b, e_sat, d, D, chain_deadline, trial_rng)
            consider(n_s, e_s)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Voltage-lift search for D >= 4.
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while D >= 4 and time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
        if res is not None:
            consider(res[0], res[1])

    # C repair stage: try to exceed the current best by attaching extra vertices.
    if best_n < lib.moore_bound(d, D):
        budget = end - time.monotonic() - 2.0
        if budget >= 2.0:
            try:
                n_c, e_c = _c_repair(d, D, best, budget, seed)
                consider(n_c, e_c)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
