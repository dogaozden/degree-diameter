import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated-annealing augmentation of a valid bipartite graph.
#
# Starting from a valid graph (max degree d, diameter <= D), the engine adds one
# vertex at a time and anneals the edges to make the enlarged graph valid again.
# Cost = number of unordered vertex pairs at distance > D (bitset BFS to depth D).
# Moves keep bipartiteness (edges always join opposite colours) and degree <= d:
#   swap  : (a,b),(c,e) -> (a,e),(c,b) with col a = col c
#   shift : (a,b) -> (x,b) with col x = col a and spare degree at x
#   add   : join two non-adjacent spare vertices of opposite colour (never hurts)
# On success the state is saved and another vertex is attempted; on failure the
# engine restores the last valid graph and tries again with a fresh vertex.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static int d, D, cap, N;
static int *col, *deg, *adjl;
static unsigned char *A;
static u64 *R0, *R1;
static int Wmax;
static int bestN = 0, bestM = 0;
static int *bu, *bv;
static u64 rs = 88172645463325252ULL;

static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int u, int v) {
    A[(size_t)u * cap + v] = 1;
    A[(size_t)v * cap + u] = 1;
    adjl[u * d + deg[u]++] = v;
    adjl[v * d + deg[v]++] = u;
}

static void del_one(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adjl[u * d + i] == v) {
            adjl[u * d + i] = adjl[u * d + deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void remove_edge(int u, int v) {
    A[(size_t)u * cap + v] = 0;
    A[(size_t)v * cap + u] = 0;
    del_one(u, v);
    del_one(v, u);
}

static long long bad_pairs(void) {
    int W = (N + 63) / 64;
    u64 *cur = R0, *nxt = R1;
    memset(cur, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < N; v++) {
            u64 *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(u64) * W);
            for (int i = 0; i < deg[v]; i++) {
                u64 *s = cur + (size_t)adjl[v * d + i] * W;
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long miss = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        u64 *p = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += popc(p[w]);
        miss += N - c;
    }
    return miss / 2;
}

static void save_best(void) {
    int m = 0;
    for (int u = 0; u < N; u++)
        for (int i = 0; i < deg[u]; i++) {
            int v = adjl[u * d + i];
            if (u < v) { bu[m] = u; bv[m] = v; m++; }
        }
    bestN = N;
    bestM = m;
}

static void restore_best(void) {
    memset(A, 0, (size_t)cap * cap);
    memset(deg, 0, sizeof(int) * cap);
    N = bestN;
    for (int i = 0; i < bestM; i++) add_edge(bu[i], bv[i]);
}

static void grow_vertex(void) {
    int x = N;
    N++;
    col[x] = rndi(2);
    deg[x] = 0;
    int st = rndi(N);
    for (int k = 0; k < N && deg[x] < d; k++) {
        int y = (st + k) % N;
        if (y == x || col[y] == col[x] || deg[y] >= d) continue;
        if (A[(size_t)x * cap + y]) continue;
        add_edge(x, y);
    }
}

static int try_add(void) {
    for (int t = 0; t < 30; t++) {
        int x = rndi(N), y = rndi(N);
        if (x == y || col[x] == col[y] || deg[x] >= d || deg[y] >= d) continue;
        if (A[(size_t)x * cap + y]) continue;
        add_edge(x, y);
        return 1;
    }
    return 0;
}

static int try_swap(int *pa, int *pb, int *pc, int *pe) {
    int a = rndi(N);
    if (deg[a] == 0) return 0;
    int b = adjl[a * d + rndi(deg[a])];
    int c = rndi(N);
    if (c == a || col[c] != col[a] || deg[c] == 0) return 0;
    int e = adjl[c * d + rndi(deg[c])];
    if (A[(size_t)a * cap + e] || A[(size_t)c * cap + b]) return 0;
    *pa = a; *pb = b; *pc = c; *pe = e;
    return 1;
}

static int try_shift(int *pa, int *pb, int *px) {
    int a = rndi(N);
    if (deg[a] == 0) return 0;
    int b = adjl[a * d + rndi(deg[a])];
    int x = rndi(N);
    if (x == a || col[x] != col[a] || deg[x] >= d) return 0;
    if (A[(size_t)x * cap + b]) return 0;
    *pa = a; *pb = b; *px = x;
    return 1;
}

static int anneal(long long iters, double deadline) {
    long long cost = bad_pairs();
    double T0 = 3.0, T1 = 0.2;
    for (long long it = 0; it < iters && cost > 0; it++) {
        if ((it & 255) == 0 && now() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int r = rndi(100);
        if (r < 15) {
            if (try_add()) cost = bad_pairs();
        } else if (r < 60) {
            int a, b, c, e;
            if (!try_swap(&a, &b, &c, &e)) continue;
            remove_edge(a, b);
            remove_edge(c, e);
            add_edge(a, e);
            add_edge(c, b);
            long long c2 = bad_pairs();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                remove_edge(a, e);
                remove_edge(c, b);
                add_edge(a, b);
                add_edge(c, e);
            }
        } else {
            int a, b, x;
            if (!try_shift(&a, &b, &x)) continue;
            remove_edge(a, b);
            add_edge(x, b);
            long long c2 = bad_pairs();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                remove_edge(x, b);
                add_edge(a, b);
            }
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (u64)(atoll(argv[3]) + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double deadline = now() + atof(argv[4]);

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n < 2 || m < 0 || d < 1 || D < 1) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(m + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m + 1));
    int ok = 1;
    for (int k = 0; k < m && ok; k++) {
        if (scanf("%d %d", &eu[k], &ev[k]) != 2) ok = 0;
        else if (eu[k] < 0 || ev[k] < 0 || eu[k] >= n || ev[k] >= n || eu[k] == ev[k]) ok = 0;
    }
    if (!ok) { printf("0 0\n"); return 0; }

    cap = n + 600;
    Wmax = (cap + 63) / 64;
    col = malloc(sizeof(int) * (size_t)cap);
    deg = calloc((size_t)cap, sizeof(int));
    adjl = calloc((size_t)cap * d, sizeof(int));
    A = calloc((size_t)cap * cap, 1);
    R0 = malloc(sizeof(u64) * (size_t)cap * Wmax);
    R1 = malloc(sizeof(u64) * (size_t)cap * Wmax);
    bu = malloc(sizeof(int) * (size_t)cap * d);
    bv = malloc(sizeof(int) * (size_t)cap * d);

    for (int i = 0; i < cap; i++) col[i] = -1;
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int k = 0; k < m; k++) {
            int u = eu[k], v = ev[k];
            if (col[u] < 0 && col[v] < 0) { col[u] = 0; col[v] = 1; changed = 1; }
            else if (col[u] < 0) { col[u] = 1 - col[v]; changed = 1; }
            else if (col[v] < 0) { col[v] = 1 - col[u]; changed = 1; }
        }
    }
    for (int i = 0; i < n; i++) if (col[i] < 0) col[i] = 0;
    for (int k = 0; k < m; k++) if (col[eu[k]] == col[ev[k]]) ok = 0;

    if (ok) {
        N = n;
        for (int k = 0; k < m && ok; k++) {
            int u = eu[k], v = ev[k];
            if (A[(size_t)u * cap + v] || deg[u] >= d || deg[v] >= d) ok = 0;
            else add_edge(u, v);
        }
    }
    if (!ok) { printf("0 0\n"); return 0; }

    if (bad_pairs() == 0) save_best();
    else if (anneal(20000, deadline)) save_best();

    while (bestN > 0 && now() < deadline) {
        restore_best();
        grow_vertex();
        if (anneal(20000, deadline)) save_best();
    }

    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bu[i], bv[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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
    arc_deadline = start + 0.15 * time_limit
    if D >= 3:
        cands = _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    if D >= 3 and best_n > 2:
        n_arc = best_n

        # Stage 1: plain greedy fill.
        n_f, e_f = _fill(best_n, best[1], d, D, start + 0.15 * time_limit,
                         random.Random(seed * 104729 + d))
        consider(n_f, e_f)

        # Stage 2: repeated cross-saturation followed by fill, each checked exactly.
        trial_rng = random.Random(seed * 31337 + d)
        chain_deadline = start + 0.25 * time_limit
        while time.monotonic() < chain_deadline:
            n_b, e_b = best
            e_sat = _cross_saturate(n_b, e_b, d, n_arc, trial_rng)
            if len(e_sat) == len(e_b):
                break
            n_s, e_s = _fill(n_b, e_sat, d, D, chain_deadline, trial_rng)
            consider(n_s, e_s)

    if D >= 4 and time.monotonic() < start + 0.25 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Voltage-lift annealing only helps for D >= 4 (the record constructions there).
    if D >= 4:
        lift_deadline = start + 0.4 * time_limit
        ks = [1, 2, 2, 3, 4]
        while time.monotonic() < lift_deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, lift_deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # Main search: C annealing augmentation from the best valid graph.
    end = start + 0.85 * time_limit
    budget = end - time.monotonic() - 2.0  # reserve time for compiling the C engine
    if budget >= 3.0 and best_n < lib.moore_bound(d, D):
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 4.0)
            n_c, e_c = lib.parse_graph_text(text)
            consider(n_c, e_c)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
