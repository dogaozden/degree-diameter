import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with d >= q+1 it has spare s = d - q - 1. Add one A-vertex per point of a
# set SA (joined to the q+1 lines through it, each line used by <= s of them)
# and one B-vertex per line of a set SB (joined to the q+1 points on it).
# Order is 2(q^2+q+1) + |SA| + |SB|. Diameter stays 3.
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


def _local_side(m, s, nbr, S0, rng, deadline, iters=6000):
    """Plateau local search on a feasible set S0 (insert, or swap out one blocker)."""
    if s < 1:
        return list(S0)
    inS = [False] * m
    load = [0] * m
    S = list(S0)
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            load[t] += 1
    best = list(S)
    for it in range(iters):
        if it % 256 == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        over = {t for t in nbr[x] if load[t] >= s}
        if not over:
            S.append(x)
            inS[x] = True
            for t in nbr[x]:
                load[t] += 1
            if len(S) > len(best):
                best = list(S)
            continue
        cand = [y for y in S if any(t in over for t in nbr[y])]
        if not cand:
            continue
        y = rng.choice(cand)
        for t in nbr[y]:
            load[t] -= 1
        if all(load[t] < s for t in nbr[x]):
            S.remove(y)
            inS[y] = False
            S.append(x)
            inS[x] = True
            for t in nbr[x]:
                load[t] += 1
        else:
            for t in nbr[y]:
                load[t] += 1
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

        SA = _local_side(m, s, point_lines, SA, rng, deadline)
        SB = _local_side(m, s, line_points, SB, rng, deadline)

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# New search for D = 3: C simulated annealing over bipartite graphs.
#
# The C engine keeps a bipartite graph with max degree d and a cost equal to
# the number of vertex pairs at distance > D. It alternates between
#   - adding a fresh (A, B) vertex pair when the graph is valid,
#   - repairing with edge moves (add, double edge swap, rewire to spare slot,
#     remove), accepted by the Metropolis rule on the cost.
# Whenever a valid graph is found it is saved; if repair stalls, it restarts
# from the best saved graph plus a new pair. Output is always the best valid
# graph, or "0 0" when none was found (the Python side then keeps its fallback).
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NM 1100
#define DMAX 64
#define PATIENCE 1200

static int d, D, n;
static int deg[NM];
static int nb[NM][DMAX];
static unsigned char am[NM][NM];
static int side[NM];

static int bestn = 0;
static int bestside[NM];
static unsigned char bestam[NM][NM];

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_sec(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int stampv[NM];
static int stampc = 0;
static int qu[NM];

/* Number of (unordered) pairs at distance > D, unreachable pairs included. */
static long cost(void) {
    long bad = 0;
    for (int s = 0; s < n; s++) {
        int cs = ++stampc;
        int head = 0, tail = 0;
        qu[tail++] = s;
        stampv[s] = cs;
        for (int dist = 0; dist < D && head < tail; dist++) {
            int end = tail;
            while (head < end) {
                int u = qu[head++];
                for (int k = 0; k < deg[u]; k++) {
                    int v = nb[u][k];
                    if (stampv[v] != cs) { stampv[v] = cs; qu[tail++] = v; }
                }
            }
        }
        bad += n - tail;
    }
    return bad / 2;
}

static void rem_half(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (nb[u][k] == v) { nb[u][k] = nb[u][--deg[u]]; return; }
    }
}

static void add_edge(int u, int v) {
    am[u][v] = 1; am[v][u] = 1;
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
}

static void del_edge(int u, int v) {
    am[u][v] = 0; am[v][u] = 0;
    rem_half(u, v);
    rem_half(v, u);
}

typedef struct { int nr, na; int ru[2], rv[2], au[2], av[2]; } Move;

static void apply_move(const Move *m) {
    for (int i = 0; i < m->nr; i++) del_edge(m->ru[i], m->rv[i]);
    for (int i = 0; i < m->na; i++) add_edge(m->au[i], m->av[i]);
}

static void undo_move(const Move *m) {
    for (int i = 0; i < m->na; i++) del_edge(m->au[i], m->av[i]);
    for (int i = 0; i < m->nr; i++) add_edge(m->ru[i], m->rv[i]);
}

static int rand_edge(int *x, int *y) {
    for (int t = 0; t < 60; t++) {
        int u = rndi(n);
        if (deg[u] > 0) { *x = u; *y = nb[u][rndi(deg[u])]; return 1; }
    }
    return 0;
}

static int propose(Move *m) {
    m->nr = 0; m->na = 0;
    double r = rndu();
    if (r < 0.25) {
        /* add an edge between two spare-degree vertices on opposite sides */
        for (int t = 0; t < 30; t++) {
            int u = rndi(n), v = rndi(n);
            if (side[u] == side[v] || deg[u] >= d || deg[v] >= d || am[u][v]) continue;
            m->na = 1; m->au[0] = u; m->av[0] = v;
            return 1;
        }
        return 0;
    }
    if (r < 0.60) {
        /* double edge swap: (x1,y1),(x2,y2) -> (x1,y2),(x2,y1); degrees preserved */
        int x1, y1, x2, y2;
        if (!rand_edge(&x1, &y1) || !rand_edge(&x2, &y2)) return 0;
        if (side[x2] != side[x1]) { int t = x2; x2 = y2; y2 = t; }
        if (x1 == x2 || y1 == y2 || am[x1][y2] || am[x2][y1]) return 0;
        m->nr = 2; m->ru[0] = x1; m->rv[0] = y1; m->ru[1] = x2; m->rv[1] = y2;
        m->na = 2; m->au[0] = x1; m->av[0] = y2; m->au[1] = x2; m->av[1] = y1;
        return 1;
    }
    if (r < 0.95) {
        /* rewire one endpoint of an edge to a vertex with spare degree */
        int x, y;
        if (!rand_edge(&x, &y)) return 0;
        int z = rndi(n);
        m->nr = 1; m->ru[0] = x; m->rv[0] = y;
        if (rndu() < 0.5) {
            if (side[z] != side[y] || z == x || deg[z] >= d || am[x][z]) return 0;
            m->na = 1; m->au[0] = x; m->av[0] = z;
        } else {
            if (side[z] != side[x] || z == y || deg[z] >= d || am[z][y]) return 0;
            m->na = 1; m->au[0] = z; m->av[0] = y;
        }
        return 1;
    }
    {
        /* remove an edge (diversification) */
        int x, y;
        if (!rand_edge(&x, &y)) return 0;
        m->nr = 1; m->ru[0] = x; m->rv[0] = y; m->na = 0;
        return 1;
    }
}

static void grow(void) {
    int a = n, b = n + 1;
    for (int i = 0; i < n + 2; i++) {
        am[a][i] = 0; am[i][a] = 0;
        am[b][i] = 0; am[i][b] = 0;
    }
    side[a] = 0; side[b] = 1;
    deg[a] = 0; deg[b] = 0;
    n += 2;
}

static void save_best(void) {
    bestn = n;
    for (int i = 0; i < n; i++) {
        bestside[i] = side[i];
        memcpy(bestam[i], am[i], (size_t)n);
    }
}

static void restore_best(void) {
    n = bestn;
    for (int i = 0; i < n; i++) {
        side[i] = bestside[i];
        memcpy(am[i], bestam[i], (size_t)n);
        deg[i] = 0;
    }
    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++)
            if (am[i][j]) nb[i][deg[i]++] = j;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    if (d < 2 || d >= DMAX || D < 1) { printf("0 0\n"); return 0; }

    int nin = 0, min_ = 0;
    if (scanf("%d %d", &nin, &min_) != 2) { nin = 0; min_ = 0; }
    if (nin < 0 || nin > NM - 4 || min_ < 0) { printf("0 0\n"); return 0; }
    n = nin;
    int bad = 0;
    for (int i = 0; i < min_; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { bad = 1; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || am[u][v] || deg[u] >= d || deg[v] >= d) {
            bad = 1; break;
        }
        add_edge(u, v);
    }
    if (bad) { printf("0 0\n"); return 0; }
    if (n == 0) {
        n = 2;
        add_edge(0, 1);
    }

    /* bipartition by BFS */
    for (int i = 0; i < n; i++) side[i] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, tail = 0;
        qu[tail++] = s;
        while (head < tail) {
            int u = qu[head++];
            for (int k = 0; k < deg[u]; k++) {
                int v = nb[u][k];
                if (side[v] < 0) { side[v] = 1 - side[u]; qu[tail++] = v; }
                else if (side[v] == side[u]) { printf("0 0\n"); return 0; }
            }
        }
    }

    long cur = cost();
    if (cur == 0) save_best();

    double tstart = now_sec();
    int since_grow = 0;
    long it = 0;
    while (1) {
        if ((it & 15) == 0 && now_sec() - tstart > budget) break;
        it++;
        if (cur == 0) {
            if (n > bestn) save_best();
            if (n + 2 > NM - 2) break;
            grow();
            cur = cost();
            since_grow = 0;
            continue;
        }
        since_grow++;
        if (bestn > 0 && since_grow > PATIENCE) {
            restore_best();
            if (n + 2 > NM - 2) break;
            grow();
            cur = cost();
            since_grow = 0;
            continue;
        }
        Move mv;
        if (!propose(&mv)) continue;
        apply_move(&mv);
        long nc = cost();
        long delta = nc - cur;
        double T = (((it / 3000) % 3) == 2) ? 1.0 : 0.4;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            undo_move(&mv);
        }
    }

    if (bestn <= 0) { printf("0 0\n"); return 0; }
    long m = 0;
    for (int u = 0; u < bestn; u++)
        for (int v = u + 1; v < bestn; v++)
            if (bestam[u][v]) m++;
    printf("%d %ld\n", bestn, m);
    for (int u = 0; u < bestn; u++)
        for (int v = u + 1; v < bestn; v++)
            if (bestam[u][v]) printf("%d %d\n", u, v);
    return 0;
}
'''


def _c_search(d, D, seed, start_graph, budget):
    """Run the C local search from start_graph for about `budget` seconds; return (n, edges)."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"], stdin_graph=start_graph,
                     timeout=budget + 20.0)
    return lib.parse_graph_text(text)


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
# Simulated annealing over bi-Cayley voltage lifts (for D >= 4 and as a
# general fallback search).
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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
        cands = _arc_extensions(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    # New for D = 3: C annealing that adds vertex pairs and repairs by edge moves,
    # starting from the best construction. Any failure keeps the fallback.
    if D == 3 and d >= 3 and best_n < lib.moore_bound(d, D):
        remaining = deadline - time.monotonic() - 2.0
        if remaining > 3.0:
            try:
                n_c, e_c = _c_search(d, D, seed, best, remaining)
                consider(n_c, e_c)
            except Exception:
                pass

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed group voltage lifts (remaining time).
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
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
