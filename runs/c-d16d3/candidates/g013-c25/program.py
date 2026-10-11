import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C local search (new in this version).
#
# The engine starts from a valid graph and runs simulated annealing over edge
# rewires and vertex insertions. The cost is the number of vertex pairs at
# distance > D, so cost 0 means valid. Every move keeps the graph bipartite:
# edges only join opposite colours. Degrees never exceed d. The best valid
# graph seen (largest order) is printed. If none beats the start, the start
# is printed back, and Python validates the result either way.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXD 64

static int N, DD, DMAX;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];

static int bN = 0;
static int have_best = 0;
static int bdeg[MAXN];
static int badj[MAXN][MAXD];
static int bcol[MAXN];

static int dist_[MAXN];
static int qu[MAXN];

static unsigned long long rs = 88172645463325252ULL;

static unsigned long long rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int k) {
    return (int)(rnd() % (unsigned long long)k);
}

static double runif(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static int has_edge(int u, int v) {
    for (int k = 0; k < deg[u]; k++)
        if (adj[u][k] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_arc(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adj[u][k] == v) {
            adj[u][k] = adj[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void del_edge(int u, int v) {
    del_arc(u, v);
    del_arc(v, u);
}

/* Number of unordered pairs at distance > DD (unreachable counts). */
static long long bad_pairs(void) {
    long long bad = 0;
    for (int s = 0; s < N; s++) {
        for (int i = 0; i < N; i++) dist_[i] = -1;
        int h = 0, t = 0;
        qu[t++] = s;
        dist_[s] = 0;
        while (h < t) {
            int u = qu[h++];
            if (dist_[u] >= DD) continue;
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (dist_[v] < 0) {
                    dist_[v] = dist_[u] + 1;
                    qu[t++] = v;
                }
            }
        }
        for (int v = s + 1; v < N; v++)
            if (dist_[v] < 0) bad++;
    }
    return bad;
}

static void save_best(void) {
    memcpy(badj, adj, sizeof(adj));
    memcpy(bdeg, deg, sizeof(deg));
    memcpy(bcol, col, sizeof(col));
    bN = N;
    have_best = 1;
}

static void restore_best(void) {
    memcpy(adj, badj, sizeof(adj));
    memcpy(deg, bdeg, sizeof(deg));
    memcpy(col, bcol, sizeof(col));
    N = bN;
}

static int accept(long long delta, double T) {
    if (delta <= 0) return 1;
    return runif() < exp(-(double)delta / T);
}

static void print_graph(void) {
    long long m = 0;
    for (int u = 0; u < N; u++)
        for (int k = 0; k < deg[u]; k++)
            if (adj[u][k] > u) m++;
    printf("%d %lld\n", N, m);
    for (int u = 0; u < N; u++)
        for (int k = 0; k < deg[u]; k++)
            if (adj[u][k] > u) printf("%d %d\n", u, adj[u][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed budget\n");
        return 1;
    }
    int d = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    DMAX = d < MAXD ? d : MAXD;
    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    if (n0 <= 0 || n0 > MAXN - 200) {
        printf("1 0\n");
        return 0;
    }

    N = n0;
    for (int i = 0; i < N; i++) deg[i] = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (has_edge(u, v) || deg[u] >= DMAX || deg[v] >= DMAX) continue;
        add_edge(u, v);
    }

    /* Bipartition by BFS. */
    for (int i = 0; i < N; i++) col[i] = -1;
    int bip = 1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        qu[t++] = s;
        while (h < t) {
            int u = qu[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    qu[t++] = v;
                } else if (col[v] == col[u]) {
                    bip = 0;
                }
            }
        }
    }
    if (!bip) {
        print_graph();
        return 0;
    }

    long long cur = bad_pairs();
    if (cur == 0) save_best();

    clock_t t0 = clock();
    double T = 1.0;
    long long it = 0;
    long long since_restore = 0;

    while (1) {
        if ((it & 31) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= budget) break;
            double frac = el / budget;
            T = 0.02 + 0.8 * (1.0 - frac);
        }
        it++;

        if (have_best && cur > 0 && since_restore > 4000) {
            restore_best();
            cur = 0;
            since_restore = 0;
        }
        since_restore++;

        if (runif() < 0.75 || N >= MAXN - 2) {
            /* Rewire: move one endpoint of an edge (a,b) to a new c on b's side. */
            int a = rint_(N);
            if (deg[a] == 0) continue;
            int b = adj[a][rint_(deg[a])];
            int c = -1;
            for (int tr = 0; tr < 60; tr++) {
                int x = rint_(N);
                if (x == a || x == b || col[x] == col[a] || deg[x] >= DMAX || has_edge(a, x))
                    continue;
                c = x;
                break;
            }
            if (c < 0) continue;
            del_edge(a, b);
            add_edge(a, c);
            long long nc = bad_pairs();
            if (accept(nc - cur, T)) {
                cur = nc;
            } else {
                del_edge(a, c);
                add_edge(a, b);
                continue;
            }
        } else {
            /* Insert a new vertex joined to up to DMAX opposite-side vertices with slack. */
            int x = N;
            col[x] = rint_(2);
            deg[x] = 0;
            N++;
            int cnt = 0;
            for (int tr = 0; tr < 600 && cnt < DMAX; tr++) {
                int y = rint_(x);
                if (col[y] == col[x] || deg[y] >= DMAX || has_edge(x, y)) continue;
                add_edge(x, y);
                cnt++;
            }
            long long nc = bad_pairs();
            if (cnt > 0 && accept(nc - cur, T)) {
                cur = nc;
            } else {
                while (deg[x] > 0) {
                    int y = adj[x][deg[x] - 1];
                    del_arc(y, x);
                    deg[x]--;
                }
                N--;
                continue;
            }
        }

        if (cur == 0 && N > bN) save_best();
    }

    if (have_best) restore_best();
    print_graph();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# A-side: a set SA of points. Each SA point P gets a new vertex joined to all
#         q+1 lines through P. Constraint: every line holds <= s points of SA.
# B-side: a set SB of lines. Each j in SB gets a new vertex joined to all
#         q+1 points on j. Constraint: every point lies on <= s lines of SB.
#
# Order is 2(q^2+q+1) + |SA| + |SB|.
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
# Simulated annealing over bi-Cayley voltage lifts (used for D != 3).
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
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
# C search driver.
# ----------------------------------------------------------------------------

def _c_search(d, D, start_graph, seed, budget):
    """Run the C annealer from start_graph; return a validated (n, edges) or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                        stdin_graph=start_graph, timeout=budget + 15.0)
        n, e = lib.parse_graph_text(out)
        if lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        return None
    return None


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

    # Arc-extended projective plane graphs (diameter 3, valid for D >= 3).
    if D >= 3:
        cands = _arc_extensions(d, start + 0.15 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    if D >= 4 and time.monotonic() < start + 0.4 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Bold change for D = 3: C annealing from the best construction, trying to
    # add vertices while keeping the diameter. Skipped when the start already
    # meets the Moore bound (nothing larger can exist).
    if D == 3 and d >= 3 and best_n < lib.moore_bound(d, D):
        elapsed = time.monotonic() - start
        budget = 0.8 * time_limit - elapsed - 3.0
        if budget > 2.0:
            res = _c_search(d, D, best, seed, budget)
            if res is not None:
                consider(res[0], res[1])

    # Voltage-lift annealing for the other diameters.
    if D != 3:
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        deadline = start + 0.7 * time_limit
        while time.monotonic() < deadline:
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

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
