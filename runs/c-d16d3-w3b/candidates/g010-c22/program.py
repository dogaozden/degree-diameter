import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New idea: pair-cover annealing for D = 3 (C engine below).
#
# In a bipartite graph, two vertices on the same side are at even distance, so
# for D = 3 they must share a neighbour. For a vertex pair on opposite sides,
# x and M, a non-adjacent pair is at distance 3 whenever x has a neighbour L and
# L, M share a neighbour Y, since x-L-Y-M is then a path. So a bipartite graph
# has diameter <= 3 exactly when every two same-side vertices have a common
# neighbour (and no isolated vertices).
#
# The C engine keeps cnt[x][y] = number of common neighbours of same-side
# pairs and U = number of same-side pairs with cnt = 0. Adding or removing an
# edge updates O(d) counters, so local moves are cheap. It adds one vertex to
# the best valid graph, covers it greedily, then anneals degree-preserving
# 2-switches to drive U to 0. Each success gives a larger valid graph.
# ----------------------------------------------------------------------------

C_PAIR = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 640
#define MAXD 32
#define MAXE (MAXN * MAXD / 2)

static int n0, n, d;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static unsigned short cnt[MAXN][MAXN];
static long U;
static double gT = 1.0;
static int best_n, best_m;
static int be_u[MAXE], be_v[MAXE];
static uint64_t rs = 88172645463325252ULL;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static double rnd01(void) {
    return (double)(rnd() & 0xFFFFFFu) / 16777216.0;
}

static double now(void) {
    return (double)clock() / CLOCKS_PER_SEC;
}

static int is_adj(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adj[a][i] == b) return 1;
    return 0;
}

static void inc_pair(int x, int y) {
    if (cnt[x][y] == 0) U--;
    cnt[x][y]++;
    cnt[y][x]++;
}

static void dec_pair(int x, int y) {
    cnt[x][y]--;
    cnt[y][x]--;
    if (cnt[x][y] == 0) U++;
}

static void list_del(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a][i] == b) {
            adj[a][i] = adj[a][--deg[a]];
            return;
        }
    }
}

/* Adds edge a-b (must be absent). Pairs (a,y) for y in N(b) and (b,m) for m in N(a)
   gain a common neighbour. */
static void add_edge(int a, int b) {
    for (int i = 0; i < deg[b]; i++) inc_pair(a, adj[b][i]);
    for (int i = 0; i < deg[a]; i++) inc_pair(b, adj[a][i]);
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void remove_edge(int a, int b) {
    list_del(a, b);
    list_del(b, a);
    for (int i = 0; i < deg[b]; i++) dec_pair(a, adj[b][i]);
    for (int i = 0; i < deg[a]; i++) dec_pair(b, adj[a][i]);
}

static void rebuild(int nn, int m) {
    n = nn;
    for (int x = 0; x < n; x++) {
        deg[x] = 0;
        for (int y = 0; y < n; y++) cnt[x][y] = 0;
    }
    U = 0;
    for (int x = 0; x < n; x++)
        for (int y = x + 1; y < n; y++)
            if (col[x] == col[y]) U++;
    for (int i = 0; i < m; i++) {
        int a = be_u[i], b = be_v[i];
        if (a >= n || b >= n || deg[a] >= d || deg[b] >= d || is_adj(a, b)) continue;
        add_edge(a, b);
    }
}

static void move_switch(void) {
    int a = (int)(rnd() % (uint32_t)n);
    if (deg[a] == 0) return;
    int b = adj[a][rnd() % (uint32_t)deg[a]];
    int c = -1;
    for (int t = 0; t < 30; t++) {
        int x = (int)(rnd() % (uint32_t)n);
        if (x != a && col[x] == col[a] && deg[x] > 0) { c = x; break; }
    }
    if (c < 0) return;
    int e = adj[c][rnd() % (uint32_t)deg[c]];
    if (e == b || is_adj(a, e) || is_adj(c, b)) return;
    long U0 = U;
    remove_edge(a, b);
    remove_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    long delta = U - U0;
    if (delta <= 0 || rnd01() < exp(-(double)delta / gT)) return;
    remove_edge(a, e);
    remove_edge(c, b);
    add_edge(a, b);
    add_edge(c, e);
}

static void move_add(void) {
    int a = (int)(rnd() % (uint32_t)n);
    if (deg[a] >= d) return;
    int b = (int)(rnd() % (uint32_t)n);
    if (b == a || col[b] == col[a] || deg[b] >= d || is_adj(a, b)) return;
    add_edge(a, b);
}

static void move_remove(void) {
    int a = (int)(rnd() % (uint32_t)n);
    if (deg[a] == 0) return;
    int b = adj[a][rnd() % (uint32_t)deg[a]];
    long U0 = U;
    remove_edge(a, b);
    long delta = U - U0;
    if (delta <= 0 || rnd01() < exp(-(double)delta / gT)) return;
    add_edge(a, b);
}

/* Greedy set cover for the new vertex z: repeatedly attach the opposite-side
   vertex that covers the most still-uncovered same-side pairs. */
static void cover_greedy(int z) {
    while (deg[z] < d) {
        int bestb = -1, bg = -1, ties = 0;
        for (int b = 0; b < n; b++) {
            if (b == z || col[b] == col[z] || deg[b] >= d) continue;
            if (is_adj(z, b)) continue;
            int g = 0;
            for (int i = 0; i < deg[b]; i++)
                if (cnt[z][adj[b][i]] == 0) g++;
            if (g > bg) {
                bg = g;
                bestb = b;
                ties = 1;
            } else if (g == bg) {
                ties++;
                if (rnd() % (uint32_t)ties == 0) bestb = b;
            }
        }
        if (bestb < 0) break;
        add_edge(z, bestb);
    }
}

static int run_stage(double se) {
    col[best_n] = (int)(rnd() & 1u);
    rebuild(best_n + 1, best_m);
    cover_greedy(best_n);
    for (int t = 0; t < 100 * n; t++) move_add();
    if (U == 0) return 1;
    double t0 = now();
    double dur = se - t0;
    if (dur <= 0) return 0;
    const double T0 = 1.5, T1 = 0.08;
    gT = T0;
    long it = 0;
    while (U > 0) {
        if ((it & 255) == 0) {
            double t = now();
            if (t >= se) break;
            gT = T0 * pow(T1 / T0, (t - t0) / dur);
        }
        it++;
        int r = (int)(rnd() % 100u);
        if (r < 75) move_switch();
        else if (r < 93) move_add();
        else move_remove();
    }
    return U == 0;
}

static void snapshot(void) {
    int m = 0;
    for (int x = 0; x < n; x++)
        for (int i = 0; i < deg[x]; i++) {
            int y = adj[x][i];
            if (y > x && m < MAXE) {
                be_u[m] = x;
                be_v[m] = y;
                m++;
            }
        }
    best_m = m;
    best_n = n;
}

static int color_graph(void) {
    static int q[MAXN];
    for (int s = 0; s < n0; s++) col[s] = -1;
    for (int s = 0; s < n0; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    q[t++] = v;
                } else if (col[v] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 4) return 1;
    d = atoi(argv[1]);
    unsigned long seed = strtoul(argv[2], NULL, 10);
    double budget = atof(argv[3]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    if (d < 1 || d > MAXD) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2 || N0 < 1 || N0 >= MAXN - 2) {
        printf("0 0\n");
        return 0;
    }
    n0 = N0;
    n = N0;
    for (int x = 0; x < n; x++) deg[x] = 0;
    int me = 0;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N0 || v >= N0 || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || is_adj(u, v)) continue;
        if (me >= MAXE) continue;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
        be_u[me] = u;
        be_v[me] = v;
        me++;
    }

    best_n = N0;
    best_m = me;
    if (!color_graph()) {
        printf("%d %d\n", best_n, best_m);
        for (int i = 0; i < best_m; i++) printf("%d %d\n", be_u[i], be_v[i]);
        return 0;
    }

    double tend = budget;
    double stage_len = budget * 0.12;
    if (stage_len < 1.0) stage_len = 1.0;
    while (best_n + 1 < MAXN - 2) {
        double t = now();
        if (t > tend - 0.5) break;
        double se = t + stage_len;
        if (se > tend) se = tend;
        if (run_stage(se)) snapshot();
    }

    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", be_u[i], be_v[i]);
    return 0;
}
"""


def _c_pair(graph, d, seed, budget):
    """Run the pair-cover annealer on graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 1.0 or d > 32:
        return None
    try:
        out = lib.run_c(C_PAIR, [d, seed, round(budget, 2)],
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
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# A-side: a set SA of points. Each SA point P gets a new vertex joined to the
#         q+1 lines through P. Each line holds <= s points of SA.
# B-side: a set SB of lines. Each j in SB gets a new vertex joined to the q+1
#         points on j. Each point lies on <= s lines of SB.
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
    """True if every target is hit by <= s elements of S, where element x hits nbr[x]."""
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
#   D = 3: arc-extended PG graphs until 0.20, then pair-cover annealing (C)
#          on the best graph until 0.88 (skipped when no degree slack is left).
#   D >= 4: GQ baseline, then annealed group voltage lifts until 0.85.
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
        cands = _arc_extensions(d, start + 0.20 * time_limit,
                                random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for g in cands[:4]:
            consider(g)

    if D == 3:
        remaining = 0.88 * time_limit - el() - 1.0
        spare = best_n * d - 2 * len(best[1])
        if remaining >= 1.0 and spare >= 2:
            consider(_c_pair(best, d, seed, remaining))

    if D >= 4:
        if el() < 0.50 * time_limit:
            consider(_best_gq(d))
        anneal_end = start + 0.85 * time_limit
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

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
