import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
# A-side: a set SA of points, each getting a new vertex joined to its q+1 lines,
#         with every line holding <= s points of SA (an s-arc).
# B-side: symmetric with a set SB of lines.
# This family is capped by the maximum s-arc size. For q = 13, s = 2 it gives
# 394 for d = 16, which equals the record, so it cannot beat it.
#
# NEW in this version: a C engine grows the best graph by adding vertices whose
# neighbourhoods are arbitrary (not pencils of points or lines). It keeps the
# bipartition, respects degree <= d, and minimises the number of vertex pairs at
# distance > D by simulated annealing over edge additions, deletions and
# degree-preserving 2-switches. Every accepted state is valid, so the best state
# is always a valid graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 1100
#define WMAX 18
#define DMAX 32

typedef struct {
    int n;
    int deg[NMAX];
    int adj[NMAX][DMAX];
    int side[NMAX];
} Graph;

typedef struct { int type, a, b, c, e; } Move;

static int DIAM = 3, DEGCAP = 16;
static double TLIMIT = 1.0;
static uint64_t RA[NMAX][WMAX], RB[NMAX][WMAX];
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static Graph G_best, G_state, G_work, G_try;
static int queue_[NMAX];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered vertex pairs at distance > DIAM. */
static long long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) >> 6;
    uint64_t (*cur)[WMAX] = RA, (*nxt)[WMAX] = RB;
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * (size_t)W);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < n; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < g->deg[v]; k++) {
                const uint64_t *src = cur[g->adj[v][k]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        uint64_t (*tmp)[WMAX] = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long miss = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        miss += n - c;
    }
    return miss / 2;
}

static int has_edge(const Graph *g, int a, int b) {
    for (int k = 0; k < g->deg[a]; k++)
        if (g->adj[a][k] == b) return 1;
    return 0;
}

static void arc_del(Graph *g, int a, int b) {
    for (int k = 0; k < g->deg[a]; k++) {
        if (g->adj[a][k] == b) {
            g->adj[a][k] = g->adj[a][--g->deg[a]];
            return;
        }
    }
}

static void edge_add(Graph *g, int a, int b) {
    g->adj[a][g->deg[a]++] = b;
    g->adj[b][g->deg[b]++] = a;
}

static void edge_del(Graph *g, int a, int b) {
    arc_del(g, a, b);
    arc_del(g, b, a);
}

/* type 0: add (a,b); type 1: delete (a,b);
   type 2: switch, delete (a,b),(c,e) and add (a,e),(c,b). */
static void apply_move(Graph *g, const Move *m) {
    if (m->type == 0) {
        edge_add(g, m->a, m->b);
    } else if (m->type == 1) {
        edge_del(g, m->a, m->b);
    } else {
        edge_del(g, m->a, m->b);
        edge_del(g, m->c, m->e);
        edge_add(g, m->a, m->e);
        edge_add(g, m->c, m->b);
    }
}

static void undo_move(Graph *g, const Move *m) {
    if (m->type == 0) {
        edge_del(g, m->a, m->b);
    } else if (m->type == 1) {
        edge_add(g, m->a, m->b);
    } else {
        edge_del(g, m->a, m->e);
        edge_del(g, m->c, m->b);
        edge_add(g, m->a, m->b);
        edge_add(g, m->c, m->e);
    }
}

static int propose(const Graph *g, int focus, int walkmode, Move *m) {
    int n = g->n;
    double r = walkmode ? 1.0 : rnd01();
    if (r < 0.40) {
        int u;
        if (focus >= 0 && rnd01() < 0.6) u = focus;
        else u = rndint(n);
        if (g->deg[u] >= DEGCAP) return 0;
        for (int tries = 0; tries < 40; tries++) {
            int v = rndint(n);
            if (v == u || g->side[v] == g->side[u] || g->deg[v] >= DEGCAP) continue;
            if (has_edge(g, u, v)) continue;
            m->type = 0; m->a = u; m->b = v;
            return 1;
        }
        return 0;
    }
    if (r < 0.50) {
        int a = rndint(n);
        if (g->deg[a] == 0) return 0;
        int b = g->adj[a][rndint(g->deg[a])];
        m->type = 1; m->a = a; m->b = b;
        return 1;
    }
    int a = rndint(n);
    if (g->deg[a] == 0) return 0;
    int b = g->adj[a][rndint(g->deg[a])];
    int c = rndint(n);
    if (c == a || g->side[c] != g->side[a] || g->deg[c] == 0) return 0;
    int e = g->adj[c][rndint(g->deg[c])];
    if (b == e) return 0;
    if (has_edge(g, a, e) || has_edge(g, c, b)) return 0;
    m->type = 2; m->a = a; m->b = b; m->c = c; m->e = e;
    return 1;
}

/* Simulated annealing on bad-pair count. Returns 1 if the graph becomes valid. */
static int anneal(Graph *g, int focus, long long iters, double T0) {
    long long cost = bad_pairs(g);
    for (long long it = 0; it < iters && cost > 0; it++) {
        if ((it & 127) == 0 && elapsed() > TLIMIT) break;
        double T = T0 * (1.0 - (double)it / (double)iters) + 0.02;
        Move m;
        if (!propose(g, focus, 0, &m)) continue;
        apply_move(g, &m);
        long long c2 = bad_pairs(g);
        long long delta = c2 - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cost = c2;
        else undo_move(g, &m);
    }
    return cost == 0;
}

/* Random walk among valid graphs of the same order (degree-preserving switches). */
static void walk(Graph *g, int steps) {
    for (int s = 0; s < steps; s++) {
        Move m;
        if (!propose(g, -1, 1, &m)) continue;
        apply_move(g, &m);
        if (bad_pairs(g) != 0) undo_move(g, &m);
    }
}

static void write_graph(const Graph *g) {
    long long m = 0;
    for (int v = 0; v < g->n; v++)
        for (int k = 0; k < g->deg[v]; k++)
            if (g->adj[v][k] > v) m++;
    printf("%d %lld\n", g->n, m);
    for (int v = 0; v < g->n; v++)
        for (int k = 0; k < g->deg[v]; k++)
            if (g->adj[v][k] > v) printf("%d %d\n", v, g->adj[v][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    TLIMIT = atof(argv[4]);
    DEGCAP = d;
    rs ^= (uint64_t)seed * 0x2545F4914F6CDD1DULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || n0 > NMAX - 200 || m0 < 0 ||
        d < 1 || d > DMAX || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    Graph *g = &G_best;
    memset(g, 0, sizeof(Graph));
    g->n = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v || has_edge(g, u, v) ||
            g->deg[u] >= d || g->deg[v] >= d) {
            printf("0 0\n");
            return 0;
        }
        edge_add(g, u, v);
    }

    /* Bipartition by BFS; reject non-bipartite input. */
    for (int v = 0; v < n0; v++) g->side[v] = -1;
    for (int s = 0; s < n0; s++) {
        if (g->side[s] >= 0) continue;
        g->side[s] = 0;
        int h = 0, t = 0;
        queue_[t++] = s;
        while (h < t) {
            int u = queue_[h++];
            for (int k = 0; k < g->deg[u]; k++) {
                int v = g->adj[u][k];
                if (g->side[v] < 0) {
                    g->side[v] = 1 - g->side[u];
                    queue_[t++] = v;
                } else if (g->side[v] == g->side[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    if (bad_pairs(g) != 0) {
        printf("0 0\n");
        return 0;
    }

    G_state = G_best;
    while (elapsed() < TLIMIT) {
        G_work = G_state;
        walk(&G_work, 20 + rndint(40));
        int x = G_work.n;
        if (x >= NMAX - 1) break;
        G_try = G_work;
        G_try.n = x + 1;
        G_try.deg[x] = 0;
        G_try.side[x] = rndint(2);
        if (anneal(&G_try, x, 6000, 1.5)) {
            G_state = G_try;
            if (G_try.n > G_best.n) G_best = G_try;
        } else {
            G_state = G_work;
        }
    }
    write_graph(&G_best);
    return 0;
}
"""


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

    # Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        cands = _arc_extensions(d, start + 0.2 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    # Diameter-4 and larger D: generalized quadrangle and voltage lifts.
    if D >= 4:
        if time.monotonic() < start + 0.3 * time_limit:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        deadline = start + 0.4 * time_limit
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

    # Vertex-growth search in C from the best graph found so far.
    avail = time_limit - (time.monotonic() - start) - 6.0
    if avail >= 2.0 and best_n >= 2:
        try:
            txt = lib.run_c(C_SOURCE, [d, D, seed, round(avail, 2)],
                            stdin_graph=best, timeout=avail + 4.0)
            n2, e2 = lib.parse_graph_text(txt)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
