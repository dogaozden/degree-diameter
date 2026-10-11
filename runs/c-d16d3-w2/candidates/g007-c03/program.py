import itertools
import math
import random
import time

import lib


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
# Spare-capacity fill (diameter 3). Each added vertex is checked by lib.is_valid.
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
# C engine: growth + repair local search for bipartite graphs with max degree d
# and diameter D. Starts from a valid graph, repeatedly adds a vertex (neighbours
# chosen greedily to cover the same side), then repairs the diameter defect with
# simulated annealing over degree-preserving 2-switches, spare-capacity edge
# additions and remove-then-add swaps. Cost = number of vertex pairs at distance
# > D. Keeps a snapshot of the last valid graph; always outputs a valid graph
# (or "0 0" if the input is unusable, which the Python side rejects).
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static int DMAX = 3;
static int DIAM = 3;
static int N = 0;
static int NCAP = 0;
static int WCAP = 1;
static int *deg_ = NULL;
static int *adj_ = NULL;
static int *col_ = NULL;
static u64 *bufA = NULL, *bufB = NULL;
static int *snap_deg = NULL, *snap_adj = NULL;
static int snap_n = 0;
static int *L0 = NULL, *L1 = NULL, nL0 = 0, nL1 = 0;
static int *DF0 = NULL, *DF1 = NULL;
static char *cov = NULL;
static u64 rs = 88172645463325252ULL;
static double tbudget = 1.0;
static double tstart = 0.0;

static u64 rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (u64)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int out_of_time(void) {
    return ((double)clock() / CLOCKS_PER_SEC) - tstart > tbudget;
}

static int popc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    const int *p = adj_ + (size_t)a * DMAX;
    for (int k = 0; k < deg_[a]; k++)
        if (p[k] == b) return 1;
    return 0;
}

static void rem_dir(int a, int b) {
    int *p = adj_ + (size_t)a * DMAX;
    for (int k = 0; k < deg_[a]; k++) {
        if (p[k] == b) {
            p[k] = p[deg_[a] - 1];
            deg_[a]--;
            return;
        }
    }
}

static void add_edge(int a, int b) {
    adj_[(size_t)a * DMAX + deg_[a]++] = b;
    adj_[(size_t)b * DMAX + deg_[b]++] = a;
}

static void del_edge(int a, int b) {
    rem_dir(a, b);
    rem_dir(b, a);
}

/* number of unordered pairs at distance > DIAM */
static long long cost_eval(void) {
    int W = (N + 63) / 64;
    u64 *cur = bufA, *nxt = bufB;
    for (int v = 0; v < N; v++) {
        u64 *r = cur + (size_t)v * WCAP;
        for (int w = 0; w < W; w++) r[w] = 0;
        r[v >> 6] |= (u64)1 << (v & 63);
    }
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < N; v++) {
            u64 *r = nxt + (size_t)v * WCAP;
            const u64 *c = cur + (size_t)v * WCAP;
            for (int w = 0; w < W; w++) r[w] = c[w];
            const int *p = adj_ + (size_t)v * DMAX;
            for (int k = 0; k < deg_[v]; k++) {
                const u64 *cu = cur + (size_t)p[k] * WCAP;
                for (int w = 0; w < W; w++) r[w] |= cu[w];
            }
        }
        u64 *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        const u64 *r = cur + (size_t)v * WCAP;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += popc64(r[w]);
        bad += N - cnt;
    }
    return bad / 2;
}

static void rebuild_lists(void) {
    nL0 = nL1 = 0;
    for (int v = 0; v < N; v++) {
        if (col_[v] == 0) L0[nL0++] = v;
        else L1[nL1++] = v;
    }
}

static void save_snap(void) {
    snap_n = N;
    for (int v = 0; v < N; v++) {
        snap_deg[v] = deg_[v];
        memcpy(snap_adj + (size_t)v * DMAX, adj_ + (size_t)v * DMAX, sizeof(int) * DMAX);
    }
}

static void restore_snap(void) {
    N = snap_n;
    for (int v = 0; v < N; v++) {
        deg_[v] = snap_deg[v];
        memcpy(adj_ + (size_t)v * DMAX, snap_adj + (size_t)v * DMAX, sizeof(int) * DMAX);
    }
    rebuild_lists();
}

/* add one vertex on a random side, joined greedily to opposite-side vertices
   so that its neighbours cover as many same-side vertices as possible */
static int grow_vertex(void) {
    if (N >= NCAP) return 0;
    int x = N;
    int c = rndint(2);
    N = x + 1;
    col_[x] = c;
    deg_[x] = 0;
    for (int v = 0; v <= x; v++) cov[v] = 0;
    cov[x] = 1;
    int chosen = 0;
    while (chosen < DMAX) {
        int best = -1, bestg = 0, ties = 0;
        for (int t = 0; t < x; t++) {
            if (col_[t] == c || deg_[t] >= DMAX) continue;
            const int *p = adj_ + (size_t)t * DMAX;
            int g = 0;
            for (int k = 0; k < deg_[t]; k++)
                if (!cov[p[k]]) g++;
            if (g > bestg) {
                bestg = g;
                best = t;
                ties = 1;
            } else if (g == bestg && g > 0) {
                ties++;
                if (rndint(ties) == 0) best = t;
            }
        }
        if (best < 0) break;
        add_edge(x, best);
        const int *p = adj_ + (size_t)best * DMAX;
        for (int k = 0; k < deg_[best]; k++) cov[p[k]] = 1;
        chosen++;
    }
    if (chosen == 0) {
        deg_[x] = 0;
        N = x;
        return 0;
    }
    return 1;
}

static long long anneal(long long cost, long iters, double T0, double T1) {
    for (long it = 0; it < iters && cost > 0; it++) {
        if ((it & 63) == 0 && out_of_time()) break;
        double T = T0 + (T1 - T0) * ((double)it / (double)iters);
        int r = rndint(100);
        if (r < 50) {
            /* degree-preserving 2-switch between the two sides */
            if (nL0 < 2) continue;
            int a = L0[rndint(nL0)], c = L0[rndint(nL0)];
            if (a == c || deg_[a] == 0 || deg_[c] == 0) continue;
            int b = adj_[(size_t)a * DMAX + rndint(deg_[a])];
            int e = adj_[(size_t)c * DMAX + rndint(deg_[c])];
            if (b == e || has_edge(a, e) || has_edge(c, b)) continue;
            del_edge(a, b);
            del_edge(c, e);
            add_edge(a, e);
            add_edge(c, b);
            long long nc = cost_eval();
            long long delta = nc - cost;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                del_edge(a, e);
                del_edge(c, b);
                add_edge(a, b);
                add_edge(c, e);
            }
        } else if (r < 80) {
            /* add an edge between two spare-capacity vertices */
            int n0 = 0, n1 = 0;
            for (int i = 0; i < nL0; i++)
                if (deg_[L0[i]] < DMAX) DF0[n0++] = L0[i];
            for (int i = 0; i < nL1; i++)
                if (deg_[L1[i]] < DMAX) DF1[n1++] = L1[i];
            if (!n0 || !n1) continue;
            int x = DF0[rndint(n0)], y = DF1[rndint(n1)];
            if (has_edge(x, y)) continue;
            add_edge(x, y);
            long long nc = cost_eval();
            long long delta = nc - cost;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                del_edge(x, y);
            }
        } else {
            /* remove a random edge, then add a random spare-capacity non-edge */
            if (nL0 < 1) continue;
            int a = L0[rndint(nL0)];
            if (deg_[a] == 0) continue;
            int b = adj_[(size_t)a * DMAX + rndint(deg_[a])];
            del_edge(a, b);
            int n0 = 0, n1 = 0;
            for (int i = 0; i < nL0; i++)
                if (deg_[L0[i]] < DMAX) DF0[n0++] = L0[i];
            for (int i = 0; i < nL1; i++)
                if (deg_[L1[i]] < DMAX) DF1[n1++] = L1[i];
            int x = -1, y = -1;
            if (n0 && n1) {
                for (int tries = 0; tries < 8; tries++) {
                    int xx = DF0[rndint(n0)], yy = DF1[rndint(n1)];
                    if (!has_edge(xx, yy) && !(xx == a && yy == b)) {
                        x = xx;
                        y = yy;
                        break;
                    }
                }
            }
            if (x < 0) {
                add_edge(a, b);
                continue;
            }
            add_edge(x, y);
            long long nc = cost_eval();
            long long delta = nc - cost;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                del_edge(x, y);
                add_edge(a, b);
            }
        }
    }
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);

    rs ^= (seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    tstart = (double)clock() / CLOCKS_PER_SEC;
    tbudget = tl;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    if (n0 < 0 || m0 < 0 || n0 > 100000 || m0 > 5000000) {
        printf("0 0\n");
        return 0;
    }
    int *eu = (int *)malloc(sizeof(int) * (size_t)(m0 + 1));
    int *ev = (int *)malloc(sizeof(int) * (size_t)(m0 + 1));
    int ok = 1;
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) {
            ok = 0;
            m0 = i;
            break;
        }
    }
    if (!ok || n0 < 2 || d < 3 || D < 2) {
        printf("0 0\n");
        return 0;
    }

    DMAX = d;
    DIAM = D;

    /* capacity: bipartite Moore bound, capped */
    double M = 0.0, term = 1.0;
    for (int i = 0; i < D; i++) {
        M += term;
        term *= (double)(d - 1);
        if (M > 1e6) break;
    }
    M *= 2.0;
    long long cap = (long long)(M > 20000.0 ? 20000.0 : M);
    if (cap > (long long)n0 + 1500) cap = (long long)n0 + 1500;
    if (cap < n0) cap = n0;
    NCAP = (int)cap;

    WCAP = (NCAP + 63) / 64;
    if (WCAP < 1) WCAP = 1;
    deg_ = (int *)calloc((size_t)NCAP, sizeof(int));
    adj_ = (int *)calloc((size_t)NCAP * DMAX, sizeof(int));
    col_ = (int *)calloc((size_t)NCAP, sizeof(int));
    bufA = (u64 *)calloc((size_t)NCAP * WCAP, sizeof(u64));
    bufB = (u64 *)calloc((size_t)NCAP * WCAP, sizeof(u64));
    snap_deg = (int *)calloc((size_t)NCAP, sizeof(int));
    snap_adj = (int *)calloc((size_t)NCAP * DMAX, sizeof(int));
    L0 = (int *)calloc((size_t)NCAP, sizeof(int));
    L1 = (int *)calloc((size_t)NCAP, sizeof(int));
    DF0 = (int *)calloc((size_t)NCAP, sizeof(int));
    DF1 = (int *)calloc((size_t)NCAP, sizeof(int));
    cov = (char *)calloc((size_t)NCAP, sizeof(char));

    /* load graph, validating simple + max degree */
    N = n0;
    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) {
            printf("0 0\n");
            return 0;
        }
        if (has_edge(u, v) || deg_[u] >= DMAX || deg_[v] >= DMAX) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    /* bipartiteness check and 2-colouring */
    for (int v = 0; v < N; v++) col_[v] = -1;
    int *queue = (int *)malloc(sizeof(int) * (size_t)N);
    for (int s = 0; s < N; s++) {
        if (col_[s] >= 0) continue;
        col_[s] = 0;
        int head = 0, tail = 0;
        queue[tail++] = s;
        while (head < tail) {
            int u = queue[head++];
            for (int k = 0; k < deg_[u]; k++) {
                int v = adj_[(size_t)u * DMAX + k];
                if (col_[v] < 0) {
                    col_[v] = 1 - col_[u];
                    queue[tail++] = v;
                } else if (col_[v] == col_[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    free(queue);

    rebuild_lists();
    long long cost = cost_eval();
    if (cost > 0) cost = anneal(cost, 20000, 2.0, 0.1);
    if (cost > 0) {
        printf("0 0\n");
        return 0;
    }
    save_snap();

    /* growth loop: each success is snapshotted, each failure restores */
    int fails = 0;
    const long ITERS = 20000;
    while (!out_of_time()) {
        if (N >= NCAP) break;
        if (!grow_vertex()) {
            if (++fails > 200) break;
            continue;
        }
        rebuild_lists();
        cost = cost_eval();
        cost = anneal(cost, ITERS, 2.0, 0.1);
        if (cost == 0) {
            save_snap();
            fails = 0;
        } else {
            restore_snap();
            if (++fails > 60) break;
        }
    }

    restore_snap();
    long long mcount = 0;
    for (int v = 0; v < N; v++) mcount += deg_[v];
    mcount /= 2;
    printf("%d %lld\n", N, mcount);
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < deg_[v]; k++) {
            int u = adj_[(size_t)v * DMAX + k];
            if (u > v) printf("%d %d\n", v, u);
        }
    }
    return 0;
}
'''


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

    # Python constructions: arc-extended projective planes, then spare-degree fill.
    py_deadline = start + 0.3 * time_limit
    if D >= 3:
        cands = _arc_extensions(d, py_deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    if D >= 3 and best_n > 2 and time.monotonic() < py_deadline:
        n_f, e_f = _fill(best_n, best[1], d, D, py_deadline,
                         random.Random(seed * 104729 + d))
        consider(n_f, e_f)

    if D >= 4 and time.monotonic() < py_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Voltage-lift annealing only for D >= 4 (it did not help for D = 3).
    if D >= 4:
        ann_deadline = start + 0.4 * time_limit
        ks = [1, 2, 2, 3, 4]
        while time.monotonic() < ann_deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, ann_deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # C growth + repair search, started from the best valid graph so far.
    elapsed = time.monotonic() - start
    budget = 0.9 * time_limit - elapsed - 3.0
    if d >= 3 and best_n >= 2 and budget >= 3.0:
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
