import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C refinement engine (new in this version).
#
# Input: a valid bipartite graph with max degree d and diameter D.
# Moves, all of which keep the graph valid:
#   * rewire: remove edge (x,y) and add (x,z), z on y's side with spare degree.
#     This is a plateau walk that moves spare degree around. Accepted only if
#     the diameter stays <= D, checked by all-pairs BFS.
#   * insert: add a new vertex v on side s, joined to up to d opposite-side
#     vertices with spare degree. Validity needs every vertex t within distance
#     D-1 of some chosen neighbour (so dist(v,t) <= D). Found by randomized greedy
#     set cover. Distances update in O(n^2) via the new vertex.
# Stops at the time budget, or after a long stretch with no insertion.
# Prints the current graph, which is always valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 2048
#define MAXDEG 128
#define INF 250
#define STALE_LIMIT 20000

static int N, DMAX, DIAM;
static int adj[MAXN][MAXDEG];
static int deg[MAXN];
static unsigned char side[MAXN];
static unsigned char dist[MAXN][MAXN];
static unsigned char backup[MAXN][MAXN];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rbelow(int k) { return (int)(rnd() % (uint64_t)k); }

static double now_sec(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int has_edge(int x, int y) {
    for (int i = 0; i < deg[x]; i++)
        if (adj[x][i] == y) return 1;
    return 0;
}

static void del_arc(int x, int y) {
    for (int i = 0; i < deg[x]; i++)
        if (adj[x][i] == y) {
            adj[x][i] = adj[x][--deg[x]];
            return;
        }
}

static void add_edge(int x, int y) {
    adj[x][deg[x]++] = y;
    adj[y][deg[y]++] = x;
}

static void remove_edge(int x, int y) {
    del_arc(x, y);
    del_arc(y, x);
}

static void bfs_from(int src) {
    static int q[MAXN];
    unsigned char *row = dist[src];
    for (int i = 0; i < N; i++) row[i] = INF;
    row[src] = 0;
    int h = 0, t = 0;
    q[t++] = src;
    while (h < t) {
        int u = q[h++];
        int du = row[u];
        if (du >= DIAM) continue;
        for (int i = 0; i < deg[u]; i++) {
            int w = adj[u][i];
            if (row[w] == INF) {
                row[w] = (unsigned char)(du + 1);
                q[t++] = w;
            }
        }
    }
}

static void compute_all(void) {
    for (int i = 0; i < N; i++) bfs_from(i);
}

static int diam_ok(void) {
    for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++)
            if (dist[i][j] > DIAM) return 0;
    return 1;
}

static int try_rewire(void) {
    if (N < 3) return 0;
    int x = rbelow(N);
    if (deg[x] == 0) return 0;
    int y = adj[x][rbelow(deg[x])];
    static int spare[MAXN];
    int ns = 0;
    for (int c = 0; c < N; c++)
        if (side[c] == side[y] && c != y && deg[c] < DMAX && !has_edge(x, c))
            spare[ns++] = c;
    if (ns == 0) return 0;
    int z = spare[rbelow(ns)];
    for (int i = 0; i < N; i++) memcpy(backup[i], dist[i], (size_t)N);
    remove_edge(x, y);
    add_edge(x, z);
    compute_all();
    if (diam_ok()) return 1;
    remove_edge(x, z);
    add_edge(x, y);
    for (int i = 0; i < N; i++) memcpy(dist[i], backup[i], (size_t)N);
    return 0;
}

static int try_insert(int restarts) {
    if (N + 1 >= MAXN) return 0;
    int s = rbelow(2);
    static int cand[MAXN];
    static unsigned char cov[MAXN], used[MAXN];
    static int chosen[MAXDEG], dv[MAXN];
    int nc = 0;
    for (int x = 0; x < N; x++)
        if (side[x] != (unsigned char)s && deg[x] < DMAX) cand[nc++] = x;
    if (nc == 0) return 0;
    int R = DIAM - 1;
    int ok = 0, k = 0;
    for (int r = 0; r < restarts && !ok; r++) {
        memset(cov, 0, (size_t)N);
        memset(used, 0, (size_t)N);
        int uncovered = N;
        k = 0;
        while (uncovered > 0 && k < DMAX) {
            int bestc = -1, bestg = 0, bestsc = -1;
            for (int i = 0; i < nc; i++) {
                int c = cand[i];
                if (used[c]) continue;
                const unsigned char *row = dist[c];
                int g = 0;
                for (int t = 0; t < N; t++)
                    if (!cov[t] && row[t] <= R) g++;
                int sc = g * 8 + rbelow(r > 0 ? 12 : 8);
                if (sc > bestsc) {
                    bestsc = sc;
                    bestc = c;
                    bestg = g;
                }
            }
            if (bestc < 0 || bestg <= 0) break;
            used[bestc] = 1;
            chosen[k++] = bestc;
            const unsigned char *row = dist[bestc];
            for (int t = 0; t < N; t++)
                if (!cov[t] && row[t] <= R) {
                    cov[t] = 1;
                    uncovered--;
                }
        }
        if (uncovered == 0) ok = 1;
    }
    if (!ok) return 0;

    int v = N;
    for (int x = 0; x < N; x++) dv[x] = INF;
    for (int i = 0; i < k; i++) {
        const unsigned char *row = dist[chosen[i]];
        for (int x = 0; x < N; x++) {
            int c = row[x] + 1;
            if (c < dv[x]) dv[x] = c;
        }
    }
    for (int x = 0; x < N; x++)
        if (dv[x] > DIAM) dv[x] = INF;

    side[v] = (unsigned char)s;
    deg[v] = 0;
    for (int i = 0; i < k; i++) add_edge(v, chosen[i]);
    N++;
    dist[v][v] = 0;
    for (int x = 0; x < v; x++) {
        dist[v][x] = (unsigned char)dv[x];
        dist[x][v] = (unsigned char)dv[x];
    }
    for (int x = 0; x < v; x++) {
        if (dv[x] >= INF) continue;
        for (int y = 0; y < v; y++) {
            if (dv[y] >= INF) continue;
            int c = dv[x] + dv[y];
            if (c <= DIAM && c < dist[x][y]) dist[x][y] = (unsigned char)c;
        }
    }
    return 1;
}

static void output_graph(void) {
    int m = 0;
    for (int x = 0; x < N; x++)
        for (int i = 0; i < deg[x]; i++)
            if (adj[x][i] > x) m++;
    printf("%d %d\n", N, m);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < deg[x]; i++)
            if (adj[x][i] > x) printf("%d %d\n", x, adj[x][i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    double t0 = now_sec();
    double deadline = t0 + budget;
    DMAX = d < 1 ? 1 : (d > MAXDEG ? MAXDEG : d);
    DIAM = D;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXN || m < 0) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v) {
            printf("0 0\n");
            return 0;
        }
        if (has_edge(u, v) || deg[u] >= DMAX || deg[v] >= DMAX) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    /* Bipartition check. */
    for (int i = 0; i < N; i++) side[i] = 255;
    static int q[MAXN];
    for (int s0 = 0; s0 < N; s0++) {
        if (side[s0] != 255) continue;
        side[s0] = 0;
        int h = 0, t = 0;
        q[t++] = s0;
        while (h < t) {
            int u = q[h++];
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[u][i];
                if (side[w] == 255) {
                    side[w] = (unsigned char)(1 - side[u]);
                    q[t++] = w;
                } else if (side[w] == side[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    compute_all();
    if (!diam_ok()) {
        printf("0 0\n");
        return 0;
    }

    long long stale = 0;
    while (now_sec() < deadline && stale < STALE_LIMIT) {
        try_rewire();
        if (try_insert(8))
            stale = 0;
        else
            stale++;
    }
    output_graph();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare s = d - q - 1. A-side: a set SA of points, each
# getting a new vertex joined to its q+1 lines (each line holds <= s of SA).
# B-side: a set SB of lines, symmetric. Order = 2(q^2+q+1) + |SA| + |SB|.
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
    """True if every target t is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements x so that every target is hit by <= s chosen elements."""
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
    """Plateau/improvement local search for the same load-constrained set problem."""
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
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
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
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n_c, e_c))
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
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 5).
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
    t_begin = time.monotonic()
    T = float(time_limit)
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

    # Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        cands = _arc_extensions(d, t_begin + 0.3 * T, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

    # Generalized quadrangle (diameter 4).
    if D >= 4 and time.monotonic() < t_begin + 0.35 * T:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed voltage lifts only where they can matter (D >= 5).
    if D >= 5:
        ks = [1, 2, 2, 3, 4]
        anneal_deadline = t_begin + 0.35 * T
        while time.monotonic() < anneal_deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, anneal_deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # C refinement: rewire plateau walk plus vertex insertion, from the best graph.
    # Reserve about 18% of the limit for the final checks and process overhead.
    budget = t_begin + 0.82 * T - time.monotonic() - 1.0
    if budget >= 2.0 and best_n >= 2:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best, timeout=budget + 8.0)
            n_c, e_c = lib.parse_graph_text(out)
            consider(n_c, e_c)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
