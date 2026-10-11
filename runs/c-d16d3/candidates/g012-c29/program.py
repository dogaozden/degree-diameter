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
#
# A-side: a set SA of points. Each SA point P gets a new vertex joined to all
#         q+1 lines through P. Constraint: every line holds <= s points of SA.
# B-side: a set SB of lines. Each j in SB gets a new vertex joined to all
#         q+1 points on j. Constraint: every point lies on <= s lines of SB.
#
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
# Simulated annealing over bi-Cayley voltage lifts (used only for D >= 4).
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
# C engine: bit-parallel diameter-repair annealing with vertex insertion.
#
# State: a bipartite graph with max degree d, kept valid-bipartite at all times.
# Cost = number of unordered pairs at distance > D (computed by bitset BFS).
# Moves: degree-preserving 2-switch, add an edge between two spare vertices,
# move one edge endpoint onto a spare vertex, remove an edge.
# Whenever cost hits 0 the graph is snapshotted and a new isolated vertex is
# inserted on the smaller side, so the order grows while the search repairs it.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1200
#define MAXW ((MAXN + 63) / 64)
#define MAXD 64
#define MAXM (MAXN * MAXD / 2)

static int d_ = 0, D_ = 0, n_ = 0;
static int side_[MAXN];
static int deg_[MAXN];
static int adj_[MAXN][MAXD];
static int sl_[2][MAXN];
static int sc_[2];
static int sp_[2][MAXN];
static int snap_ok_ = 0, snap_n_ = 0;
static int snap_deg_[MAXN];
static int snap_adj_[MAXN][MAXD];
static uint64_t bsA_[MAXN][MAXW];
static uint64_t bsB_[MAXN][MAXW];
static int eu_[MAXM], ev_[MAXM];
static int color_[MAXN], stk_[MAXN];
static uint64_t rng_s = 88172645463325252ULL;

typedef struct { int add, a, b; } Op;
static Op ops_[16];
static int nops_ = 0;

static uint64_t rnd64(void) {
    rng_s ^= rng_s << 13;
    rng_s ^= rng_s >> 7;
    rng_s ^= rng_s << 17;
    return rng_s;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_sec(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int has_edge(int a, int b) {
    for (int k = 0; k < deg_[a]; k++)
        if (adj_[a][k] == b) return 1;
    return 0;
}

static void arc_add(int a, int b) { adj_[a][deg_[a]++] = b; }

static void arc_del(int a, int b) {
    for (int k = 0; k < deg_[a]; k++) {
        if (adj_[a][k] == b) {
            adj_[a][k] = adj_[a][deg_[a] - 1];
            deg_[a]--;
            return;
        }
    }
}

static void edge_add(int a, int b) { arc_add(a, b); arc_add(b, a); }
static void edge_del(int a, int b) { arc_del(a, b); arc_del(b, a); }

static void op_add(int a, int b) {
    ops_[nops_].add = 1; ops_[nops_].a = a; ops_[nops_].b = b; nops_++;
    edge_add(a, b);
}

static void op_del(int a, int b) {
    ops_[nops_].add = 0; ops_[nops_].a = a; ops_[nops_].b = b; nops_++;
    edge_del(a, b);
}

static void undo_ops(void) {
    for (int i = nops_ - 1; i >= 0; i--) {
        if (ops_[i].add) edge_del(ops_[i].a, ops_[i].b);
        else edge_add(ops_[i].a, ops_[i].b);
    }
    nops_ = 0;
}

/* Number of unordered pairs at distance > D_ (bitset BFS on closed neighbourhoods). */
static long long eval_cost(void) {
    int n = n_;
    int W = (n + 63) >> 6;
    uint64_t (*cur)[MAXW] = bsA_;
    uint64_t (*nxt)[MAXW] = bsB_;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
        for (int k = 0; k < deg_[v]; k++) {
            int u = adj_[v][k];
            cur[v][u >> 6] |= 1ULL << (u & 63);
        }
    }
    for (int r = 1; r < D_; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < deg_[v]; k++) {
                int u = adj_[v][k];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*tmp)[MAXW] = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(cur[v][w]);
        tot += n - c;
    }
    return tot / 2;
}

static int pick_side(int s) {
    for (int t = 0; t < 20; t++) {
        int v = sl_[s][rndint(sc_[s])];
        if (deg_[v] > 0) return v;
    }
    return -1;
}

static int collect_spare(int s) {
    int c = 0;
    for (int i = 0; i < sc_[s]; i++) {
        int v = sl_[s][i];
        if (deg_[v] < d_) sp_[s][c++] = v;
    }
    return c;
}

/* Degree-preserving 2-switch: (a,b),(c,e) -> (a,e),(c,b) with a,c on the same side. */
static int move_2switch(void) {
    int s = rndint(2);
    int a = pick_side(s);
    if (a < 0) return 0;
    int b = adj_[a][rndint(deg_[a])];
    int c = pick_side(s);
    if (c < 0 || c == a) return 0;
    int e = adj_[c][rndint(deg_[c])];
    if (e == b) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    op_del(a, b);
    op_del(c, e);
    op_add(a, e);
    op_add(c, b);
    return 1;
}

/* Add an edge between two spare vertices on opposite sides. */
static int move_add(void) {
    int n0 = collect_spare(0);
    int n1 = collect_spare(1);
    if (n0 == 0 || n1 == 0) return 0;
    for (int t = 0; t < 30; t++) {
        int a = sp_[0][rndint(n0)];
        int b = sp_[1][rndint(n1)];
        if (!has_edge(a, b)) {
            op_add(a, b);
            return 1;
        }
    }
    return 0;
}

/* Move one endpoint of an edge onto a spare vertex of the opposite side. */
static int move_endpoint(void) {
    int s = rndint(2);
    int a = pick_side(s);
    if (a < 0) return 0;
    int b = adj_[a][rndint(deg_[a])];
    int t = 1 - s;
    int ns = collect_spare(t);
    if (ns == 0) return 0;
    for (int tr = 0; tr < 20; tr++) {
        int c = sp_[t][rndint(ns)];
        if (c != b && !has_edge(a, c)) {
            op_del(a, b);
            op_add(a, c);
            return 1;
        }
    }
    return 0;
}

static int move_remove(void) {
    int s = rndint(2);
    int a = pick_side(s);
    if (a < 0) return 0;
    int b = adj_[a][rndint(deg_[a])];
    op_del(a, b);
    return 1;
}

static void grow(void) {
    int s;
    if (sc_[0] < sc_[1]) s = 0;
    else if (sc_[1] < sc_[0]) s = 1;
    else s = rndint(2);
    int v = n_++;
    side_[v] = s;
    deg_[v] = 0;
    sl_[s][sc_[s]++] = v;
}

static void take_snapshot(void) {
    snap_n_ = n_;
    for (int v = 0; v < n_; v++) {
        snap_deg_[v] = deg_[v];
        for (int k = 0; k < deg_[v]; k++) snap_adj_[v][k] = adj_[v][k];
    }
}

static void print_snapshot(void) {
    long long m2 = 0;
    for (int v = 0; v < snap_n_; v++) m2 += snap_deg_[v];
    printf("%d %lld\n", snap_n_, m2 / 2);
    for (int v = 0; v < snap_n_; v++) {
        for (int k = 0; k < snap_deg_[v]; k++) {
            int u = snap_adj_[v][k];
            if (v < u) printf("%d %d\n", v, u);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rng_s = (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rng_s == 0) rng_s = 1;
    double budget = atof(argv[4]);
    if (d_ < 2 || d_ > MAXD || D_ < 1) { printf("0 0\n"); return 0; }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n == 0) {
        n = 2; m = 1; eu_[0] = 0; ev_[0] = 1;
    } else {
        if (n < 0 || m < 0 || n > MAXN - 200 || m > MAXM) { printf("0 0\n"); return 0; }
        for (int i = 0; i < m; i++) {
            if (scanf("%d %d", &eu_[i], &ev_[i]) != 2) { printf("0 0\n"); return 0; }
        }
    }

    n_ = n;
    for (int v = 0; v < n_; v++) deg_[v] = 0;
    for (int i = 0; i < m; i++) {
        int a = eu_[i], b = ev_[i];
        if (a < 0 || a >= n_ || b < 0 || b >= n_ || a == b) { printf("0 0\n"); return 0; }
        if (has_edge(a, b) || deg_[a] >= d_ || deg_[b] >= d_) { printf("0 0\n"); return 0; }
        edge_add(a, b);
    }

    /* Bipartition by BFS; reject non-bipartite input. */
    for (int v = 0; v < n_; v++) color_[v] = -1;
    for (int s0 = 0; s0 < n_; s0++) {
        if (color_[s0] >= 0) continue;
        color_[s0] = 0;
        int sp = 0;
        stk_[sp++] = s0;
        while (sp > 0) {
            int u = stk_[--sp];
            for (int k = 0; k < deg_[u]; k++) {
                int w = adj_[u][k];
                if (color_[w] < 0) {
                    color_[w] = 1 - color_[u];
                    stk_[sp++] = w;
                } else if (color_[w] == color_[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    sc_[0] = sc_[1] = 0;
    for (int v = 0; v < n_; v++) {
        int s = color_[v];
        side_[v] = s;
        sl_[s][sc_[s]++] = v;
    }
    if (sc_[0] == 0 || sc_[1] == 0) { printf("0 0\n"); return 0; }

    long long cost = eval_cost();
    if (cost == 0) {
        take_snapshot();
        snap_ok_ = 1;
    }

    const long long CYC = 40000;
    const double T0 = 3.0, T1 = 0.3;
    long long phase = 0;
    long long iter = 0;
    double t_begin = now_sec();

    while (1) {
        if ((iter & 31) == 0 && now_sec() - t_begin >= budget) break;
        iter++;
        phase++;
        if (phase >= CYC) phase = 0;
        double T = T0 * pow(T1 / T0, (double)phase / (double)CYC);

        int r = rndint(100);
        int ok;
        nops_ = 0;
        if (r < 55) ok = move_2switch();
        else if (r < 80) ok = move_add();
        else if (r < 98) ok = move_endpoint();
        else ok = move_remove();
        if (!ok) { nops_ = 0; continue; }

        long long nc = eval_cost();
        long long delta = nc - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cost = nc;
            nops_ = 0;
        } else {
            undo_ops();
        }

        if (cost == 0) {
            if (n_ >= MAXN - 1) break;
            take_snapshot();
            snap_ok_ = 1;
            grow();
            cost = eval_cost();
        }
    }

    if (snap_ok_) print_snapshot();
    else printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if best_n >= moore:
        return best

    # Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.2 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)
    if best_n >= moore:
        return best

    if D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Voltage-lift annealing for D >= 4 (unchanged from the parent).
    if D >= 4:
        anneal_end = t0 + 0.4 * time_limit
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
                consider(res[0], res[1])

    # C repair/insertion search starting from the best graph found so far.
    if D >= 3 and best_n < moore and d <= 64 and best_n <= 1000:
        elapsed = time.monotonic() - t0
        reserve = max(3.0, 0.12 * time_limit)
        budget = time_limit - elapsed - reserve
        if budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=best, timeout=budget + reserve * 0.5)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except (RuntimeError, ValueError, OSError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
