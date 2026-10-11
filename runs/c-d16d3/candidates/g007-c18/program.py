import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: grows a valid diameter-D bipartite graph one vertex at a time.
#
# Start graph (from stdin) is valid. Repeatedly: restore the last valid graph,
# add one vertex on a random side, attach it to spare-degree opposite-side
# vertices, then simulated-annealing over degree-preserving moves (endpoint
# rewire to a spare vertex, double-edge swap) minimizing the number of vertex
# pairs at distance > D. Distances come from bitset ball expansion. Degrees
# never exceed d, and the sides never mix, so output stays bipartite and simple.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXFAILS 4

static int d_, D_;
static int cap, n;
static int *deg, *adj, *side;
static unsigned char *A;
static uint64_t *R1, *R2;
static int Wmax;
static int *slist[2], scount[2];
static int *tmpX, *tmpY, *cand;
static int *sEu, *sEv, sEm, sn;
static uint64_t rs = 88172645463325252ULL;
static double t_end;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int m) { return (int)(rnd() % (uint64_t)m); }
static double rndd(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void shuffle(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

static int has_edge(int u, int v) { return A[(size_t)u * cap + v]; }

static void add_edge(int u, int v) {
    adj[(size_t)u * d_ + deg[u]++] = v;
    adj[(size_t)v * d_ + deg[v]++] = u;
    A[(size_t)u * cap + v] = 1;
    A[(size_t)v * cap + u] = 1;
}

static void drop_nbr(int u, int v) {
    int *p = adj + (size_t)u * d_;
    for (int k = 0; k < deg[u]; k++) {
        if (p[k] == v) {
            p[k] = p[deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void remove_edge(int u, int v) {
    drop_nbr(u, v);
    drop_nbr(v, u);
    A[(size_t)u * cap + v] = 0;
    A[(size_t)v * cap + u] = 0;
}

static void rebuild_sides(void) {
    scount[0] = scount[1] = 0;
    for (int v = 0; v < n; v++) {
        int s = side[v];
        slist[s][scount[s]++] = v;
    }
}

/* Number of unordered vertex pairs at distance > D_ (unreachable counts too). */
static long long cost_bad(void) {
    int N = n;
    int Wn = (N + 63) >> 6;
    if (N <= 1) return 0;
    memset(R1, 0, sizeof(uint64_t) * (size_t)N * Wn);
    for (int v = 0; v < N; v++) R1[(size_t)v * Wn + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = R2 + (size_t)v * Wn;
            memcpy(dst, R1 + (size_t)v * Wn, sizeof(uint64_t) * Wn);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = R1 + (size_t)adj[(size_t)v * d_ + k] * Wn;
                for (int w = 0; w < Wn; w++) dst[w] |= src[w];
            }
        }
        uint64_t *t = R1;
        R1 = R2;
        R2 = t;
    }
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        const uint64_t *src = R1 + (size_t)v * Wn;
        for (int w = 0; w < Wn; w++) c += popc(src[w]);
        tot += N - c;
    }
    return tot / 2;
}

static int pick_edge(int *pu, int *pv) {
    for (int t = 0; t < 64; t++) {
        int u = rndi(n);
        if (deg[u] == 0) continue;
        *pu = u;
        *pv = adj[(size_t)u * d_ + rndi(deg[u])];
        return 1;
    }
    return 0;
}

/* Keep endpoint a, move endpoint b to a spare vertex w on b's side. ud = {a, b, w}. */
static int move_rewire(int *ud) {
    int a, b;
    if (!pick_edge(&a, &b)) return 0;
    if (rnd() & 1) {
        int t = a;
        a = b;
        b = t;
    }
    int Y = side[b];
    if (scount[Y] == 0) return 0;
    int w = slist[Y][rndi(scount[Y])];
    if (w == b || deg[w] >= d_ || has_edge(a, w)) return 0;
    remove_edge(a, b);
    add_edge(a, w);
    ud[0] = a;
    ud[1] = b;
    ud[2] = w;
    return 1;
}

/* Degree-preserving swap (a,b),(c,e) -> (a,e),(c,b) with a,c on side 0. ud = {a, b, c, e}. */
static int move_swap(int *ud) {
    int a, b, c, e, t;
    if (!pick_edge(&a, &b)) return 0;
    if (side[a] != 0) {
        t = a;
        a = b;
        b = t;
    }
    if (!pick_edge(&c, &e)) return 0;
    if (side[c] != 0) {
        t = c;
        c = e;
        e = t;
    }
    if (a == c || b == e) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    remove_edge(a, b);
    remove_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    ud[0] = a;
    ud[1] = b;
    ud[2] = c;
    ud[3] = e;
    return 1;
}

/* Greedily add every possible edge between spare-degree vertices on opposite sides. */
static void fill_all(void) {
    int nx = 0, ny = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] >= d_) continue;
        if (side[v] == 0) tmpX[nx++] = v;
        else tmpY[ny++] = v;
    }
    shuffle(tmpX, nx);
    shuffle(tmpY, ny);
    for (int i = 0; i < nx; i++) {
        int u = tmpX[i];
        for (int j = 0; j < ny && deg[u] < d_; j++) {
            int v = tmpY[j];
            if (deg[v] < d_ && !has_edge(u, v)) add_edge(u, v);
        }
    }
}

/* Add one vertex on a random side, attached to spare opposite-side vertices. */
static int grow_one(void) {
    if (n >= cap) return 0;
    int s = rndi(2);
    int v = n++;
    side[v] = s;
    deg[v] = 0;
    rebuild_sides();
    int Y = 1 - s, nc = 0;
    for (int i = 0; i < scount[Y]; i++) {
        int u = slist[Y][i];
        if (deg[u] < d_) cand[nc++] = u;
    }
    shuffle(cand, nc);
    for (int i = 0; i < nc && deg[v] < d_; i++) add_edge(v, cand[i]);
    return deg[v] > 0;
}

static void snapshot(void) {
    sn = n;
    sEm = 0;
    for (int v = 0; v < n; v++) {
        for (int k = 0; k < deg[v]; k++) {
            int u = adj[(size_t)v * d_ + k];
            if (v < u) {
                sEu[sEm] = v;
                sEv[sEm] = u;
                sEm++;
            }
        }
    }
}

static void restore(void) {
    n = sn;
    memset(deg, 0, sizeof(int) * cap);
    memset(A, 0, (size_t)cap * cap);
    for (int i = 0; i < sEm; i++) add_edge(sEu[i], sEv[i]);
    rebuild_sides();
}

/* Simulated annealing on cost_bad. Returns 1 when the graph is valid (cost 0). */
static int anneal(long long iters, double T0, double T1, long long period, long long *curp) {
    long long cur = cost_bad();
    int ud[4];
    if (cur == 0) {
        *curp = 0;
        return 1;
    }
    for (long long it = 0; it < iters; it++) {
        if ((it & 127) == 0 && now() > t_end) break;
        if (it % 3000 == 2999) {
            fill_all();
            cur = cost_bad();
            if (cur == 0) break;
        }
        double ph = (double)(it % period) / (double)period;
        double T = T0 * pow(T1 / T0, ph);
        int kind = (rndi(10) < 6) ? 0 : 1;
        int ok = (kind == 0) ? move_rewire(ud) : move_swap(ud);
        if (!ok) continue;
        long long c2 = cost_bad();
        if (c2 <= cur || rndd() < exp(-(double)(c2 - cur) / T)) {
            cur = c2;
            if (cur == 0) break;
        } else if (kind == 0) {
            remove_edge(ud[0], ud[2]);
            add_edge(ud[0], ud[1]);
        } else {
            remove_edge(ud[0], ud[3]);
            remove_edge(ud[2], ud[1]);
            add_edge(ud[0], ud[1]);
            add_edge(ud[2], ud[3]);
        }
    }
    *curp = cur;
    return cur == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t sd = (uint64_t)strtoull(argv[3], NULL, 10);
    rs ^= sd * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    t_end = now() + budget;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 1 || d_ < 1 || D_ < 1 || m0 < 0) {
        printf("1 0\n");
        return 0;
    }
    int *iu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *iv = malloc(sizeof(int) * (size_t)(m0 + 1));
    int mr = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) continue;
        iu[mr] = u;
        iv[mr] = v;
        mr++;
    }

    cap = n0 + (n0 / 2 > 64 ? n0 / 2 : 64);
    Wmax = (cap + 63) / 64;
    deg = calloc(cap, sizeof(int));
    side = calloc(cap, sizeof(int));
    adj = calloc((size_t)cap * d_, sizeof(int));
    A = calloc((size_t)cap * cap, 1);
    R1 = calloc((size_t)cap * Wmax, sizeof(uint64_t));
    R2 = calloc((size_t)cap * Wmax, sizeof(uint64_t));
    slist[0] = malloc(sizeof(int) * cap);
    slist[1] = malloc(sizeof(int) * cap);
    tmpX = malloc(sizeof(int) * cap);
    tmpY = malloc(sizeof(int) * cap);
    cand = malloc(sizeof(int) * cap);
    sEu = malloc(sizeof(int) * ((size_t)cap * d_ + 1));
    sEv = malloc(sizeof(int) * ((size_t)cap * d_ + 1));

    n = n0;
    for (int i = 0; i < mr; i++) {
        int u = iu[i], v = iv[i];
        if (has_edge(u, v)) continue;
        if (deg[u] >= d_ || deg[v] >= d_) continue;
        add_edge(u, v);
    }

    /* Bipartition by BFS (the input is bipartite). */
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        tmpX[qt++] = s;
        while (qh < qt) {
            int v = tmpX[qh++];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[(size_t)v * d_ + k];
                if (side[u] < 0) {
                    side[u] = 1 - side[v];
                    tmpX[qt++] = u;
                }
            }
        }
    }
    rebuild_sides();

    /* Start from the input graph. */
    snapshot();
    fill_all();
    long long cur = 0;
    if (anneal(150000, 0.6, 0.05, 20000, &cur)) snapshot();
    else restore();

    /* Grow one vertex at a time while a valid graph can be found. */
    int fails = 0;
    while (now() < t_end && fails < MAXFAILS && n < cap) {
        restore();
        if (!grow_one()) {
            fails++;
            continue;
        }
        fill_all();
        long long iters = 40000 + 20000LL * fails;
        if (anneal(iters, 0.6, 0.05, 20000, &cur)) {
            snapshot();
            fails = 0;
        } else {
            fails++;
        }
    }

    restore();
    printf("%d %d\n", n, sEm);
    for (int i = 0; i < sEm; i++) printf("%d %d\n", sEu[i], sEv[i]);
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

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Arc-extended projective plane graphs: diameter 3, valid for all D >= 3.
    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.15 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in cands:
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # For D >= 5, a short annealed group-lift search gives a larger start.
    if D >= 5:
        ks = [1, 2, 2, 3, 4]
        lift_deadline = t0 + 0.3 * time_limit
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

    # Main search: C engine grows the best start by adding vertices.
    elapsed = time.monotonic() - t0
    remaining = time_limit - elapsed
    budget = 0.9 * remaining - 4.0
    if budget >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best, timeout=max(2.0, remaining - 2.0))
            n_c, e_c = lib.parse_graph_text(out)
            consider(n_c, e_c)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
