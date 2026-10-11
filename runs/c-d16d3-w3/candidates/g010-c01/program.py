"""Search program for bipartite graphs with max degree d and diameter D.

Construction families:
  1. Arc-extended projective plane graphs (diameter 3): the incidence graph of PG(2, q)
     plus one new vertex per point of an arc A and per line of an arc B.
  2. For D = 3 with a base of order 100..900: a C simulated annealer (C_SOURCE) adds two
     vertices (one per side) and rewires edges, minimising the number of pairs at distance
     greater than 3. It returns only graphs with zero bad pairs. Each success is re-checked
     with lib.is_valid and used as the next start, so the order grows by 2 per success.
  3. For D >= 4 (and small D = 3 bases): generalized quadrangle W(q) and annealed bi-Cayley
     voltage lifts over semidirect products, as in the previous version.

Every candidate is checked with lib.is_valid before it can replace the current best, so the
output is always valid. The fallback is K_{d,d}, which has diameter 2.
"""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bipartite graph augmentation by simulated annealing on bad pairs.
#
# Input (stdin): "n m" then m edges of a valid bipartite graph (max degree <= d).
# Args: d D seed time_limit ea eb
#   ea new side-0 vertices and eb new side-1 vertices are appended (ids n .. n+ea+eb-1).
# Moves: add an edge between two non-saturated vertices of opposite sides, or swap an
# existing edge for a random admissible one. Cost = ordered pairs at distance > D.
# On cost 0 it prints the graph and exits. Otherwise it prints the input graph unchanged.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXW 16
#define MAXDEG 64

static int n, d, D, W;
static int nside[2];
static int sv[2][MAXN];
static int side[MAXN];
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static unsigned char adjm[MAXN][MAXN];
static uint64_t bufA[MAXN * MAXW];
static uint64_t bufB[MAXN * MAXW];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long eval_cost(void) {
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) o[w] = c[w];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *c2 = cur + (size_t)adj[v][k] * W;
                for (int w = 0; w < W; w++) o[w] |= c2[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += popc(cur[(size_t)v * W + w]);
        bad += n - cnt;
    }
    return bad;
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
    adjm[a][b] = 1;
    adjm[b][a] = 1;
}

static void del_one(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adj[a][k] == b) {
            adj[a][k] = adj[a][--deg[a]];
            return;
        }
    }
}

static void remove_edge(int a, int b) {
    del_one(a, b);
    del_one(b, a);
    adjm[a][b] = 0;
    adjm[b][a] = 0;
}

static int pick_free(int s) {
    if (nside[s] == 0) return -1;
    for (int t = 0; t < 64; t++) {
        int v = sv[s][rndint(nside[s])];
        if (deg[v] < d) return v;
    }
    return -1;
}

static void print_graph(void) {
    long m2 = 0;
    for (int v = 0; v < n; v++) m2 += deg[v];
    printf("%d %ld\n", n, m2 / 2);
    for (int v = 0; v < n; v++)
        for (int k = 0; k < deg[v]; k++)
            if (v < adj[v][k]) printf("%d %d\n", v, adj[v][k]);
}

static void print_input(int nin, int m, const int *iu, const int *iv) {
    printf("%d %d\n", nin, m);
    for (int i = 0; i < m; i++) printf("%d %d\n", iu[i], iv[i]);
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: prog d D seed time ea eb\n");
        return 1;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    int ea = atoi(argv[5]);
    int eb = atoi(argv[6]);

    int nin = 0, m = 0;
    if (scanf("%d %d", &nin, &m) != 2) {
        printf("0 0\n");
        return 0;
    }
    if (nin <= 0 || nin > MAXN || m < 0 || d < 1 || d > MAXDEG || ea < 0 || eb < 0 ||
        nin + ea + eb > MAXN) {
        printf("0 0\n");
        return 0;
    }
    int *iu = malloc(sizeof(int) * (size_t)(m + 1));
    int *iv = malloc(sizeof(int) * (size_t)(m + 1));
    int mm = 0;
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &iu[i], &iv[i]) != 2) break;
        mm++;
    }
    m = mm;

    for (int v = 0; v < MAXN; v++) deg[v] = 0;
    int ok = 1;
    for (int i = 0; i < m && ok; i++) {
        int a = iu[i], b = iv[i];
        if (a < 0 || b < 0 || a >= nin || b >= nin || a == b || adjm[a][b] ||
            deg[a] >= d || deg[b] >= d)
            ok = 0;
        else
            add_edge(a, b);
    }
    if (!ok) {
        print_input(nin, m, iu, iv);
        return 0;
    }

    /* Bipartition of the input by BFS 2-colouring. */
    int *q = malloc(sizeof(int) * (size_t)nin);
    for (int v = 0; v < nin; v++) side[v] = -1;
    for (int s0 = 0; s0 < nin && ok; s0++) {
        if (side[s0] >= 0) continue;
        side[s0] = 0;
        int head = 0, tail = 0;
        q[tail++] = s0;
        while (head < tail && ok) {
            int u = q[head++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    q[tail++] = v;
                } else if (side[v] == side[u]) {
                    ok = 0;
                }
            }
        }
    }
    free(q);
    if (!ok) {
        print_input(nin, m, iu, iv);
        return 0;
    }

    /* Append the new vertices: ea on side 0, eb on side 1. */
    n = nin + ea + eb;
    for (int v = nin; v < nin + ea; v++) side[v] = 0;
    for (int v = nin + ea; v < n; v++) side[v] = 1;
    W = (n + 63) / 64;
    nside[0] = nside[1] = 0;
    for (int v = 0; v < n; v++) sv[side[v]][nside[side[v]]++] = v;
    if (nside[0] == 0 || nside[1] == 0) {
        print_input(nin, m, iu, iv);
        return 0;
    }

    long cur = eval_cost();
    if (cur == 0) {
        print_graph();
        return 0;
    }

    clock_t c0 = clock();
    long it = 0;
    double T = 1.0;
    for (;;) {
        if ((it & 15) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= tl) break;
            double frac = el / tl;
            T = 2.0 * pow(0.02, frac);
        }
        it++;
        if (rnd01() < 0.5) {
            int x = pick_free(0), y = pick_free(1);
            if (x < 0 || y < 0 || adjm[x][y]) continue;
            add_edge(x, y);
            long c2 = eval_cost();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                remove_edge(x, y);
                continue;
            }
        } else {
            int a = -1, b = -1;
            for (int t = 0; t < 100 && a < 0; t++) {
                int v = sv[0][rndint(nside[0])];
                if (deg[v] > 0) {
                    a = v;
                    b = adj[v][rndint(deg[v])];
                }
            }
            if (a < 0) continue;
            remove_edge(a, b);
            int x = pick_free(0), y = pick_free(1);
            if (x < 0 || y < 0 || adjm[x][y]) {
                add_edge(a, b);
                continue;
            }
            add_edge(x, y);
            long c2 = eval_cost();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                remove_edge(x, y);
                add_edge(a, b);
                continue;
            }
        }
        if (cur == 0) {
            print_graph();
            return 0;
        }
    }
    print_input(nin, m, iu, iv);
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
# B-side: a set SB of lines. Each j in SB gets a new vertex joined to all q+1
#         points on j. Constraint: every point lies on <= s lines of SB.
# Order is 2(q^2+q+1) + |SA| + |SB|. Diameter stays 3 for any SA, SB.
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
    """Plateau local search on a feasible set S0. Returns the largest feasible set seen."""
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
# C-driven augmentation for diameter 3 (new in this version).
# ----------------------------------------------------------------------------

def _c_grow(d, D, graph, seed, deadline):
    """Repeatedly ask the C annealer to add one vertex per side. Returns the largest valid graph reached."""
    cur_n, cur_e = graph
    fails = 0
    k = 0
    while fails < 2:
        left = deadline - time.monotonic()
        if left < 4.0:
            break
        slice_s = max(3.0, 0.5 * left)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed * 1009 + k, round(slice_s, 2), 1, 1],
                            stdin_graph=(cur_n, cur_e), timeout=slice_s + 4.0)
            nn, ee = lib.parse_graph_text(out)
        except (RuntimeError, ValueError):
            break
        k += 1
        if nn > cur_n and lib.is_valid(nn, ee, d, D):
            cur_n, cur_e = nn, ee
            fails = 0
        else:
            fails += 1
    return cur_n, cur_e


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
# Simulated annealing over bi-Cayley voltage lifts (kept for D >= 4 and small D = 3).
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

    # Arc-extended projective plane graphs: diameter 3, so valid for all D >= 3.
    if D >= 3:
        cands = _arc_extensions(d, start + 0.25 * time_limit,
                                random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    # Diameter 3 with a sizeable base: grow it with the C annealer.
    if D == 3 and 100 <= best_n <= 900:
        grown_n, grown_e = _c_grow(d, D, best, seed, start + 0.88 * time_limit)
        consider(grown_n, grown_e)

    elif time.monotonic() < start + 0.7 * time_limit:
        # Generalized quadrangle baseline (D >= 4).
        if D >= 4:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])

        # Annealed group voltage lifts for the remaining budget.
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
