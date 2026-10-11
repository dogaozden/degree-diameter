import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: a C simulated-annealing "vertex growth" engine.
#
# Python builds the best start graph it can (arc-extended projective planes for
# D >= 3, generalized quadrangles for D >= 4) and hands it to a C engine. The
# engine works on a graph with max degree d and keeps it bipartite:
#   * grow: add an A-vertex x and a B-vertex y. Remove a matching of d edges
#     (a_i, b_i), join x to all b_i and y to all a_i. Degrees stay <= d and the
#     order rises by 2.
#   * anneal: degree-preserving double-edge swaps, degree-transfer moves, and
#     edge insertions between deficient vertices. The cost is the number of
#     ordered vertex pairs at distance > D, computed with bitset BFS.
# When the cost reaches 0 the graph is valid and is saved. If annealing stalls,
# the engine restores the best valid graph and grows again with a new matching.
# Python re-checks the output with lib.is_valid and keeps a safe fallback.
# ----------------------------------------------------------------------------


# ---------------------------------------------------------- arc-extended planes

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
    """Plateau local search on a feasible set S0 (insert, or swap out one blocking element)."""
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


# ------------------------------------------------------- generalized quadrangle

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


# ------------------------------------------------------------------ C engine

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

typedef struct { int kind, i, j, a, b, c, e; } undo_t;

static int dgr = 0, diam = 0;
static int nv = 0, ne = 0, cap = 0, capW = 1;
static int *eu = NULL, *ev = NULL;
static int *deg = NULL, *col = NULL;
static unsigned char *adj = NULL;
static u64 *bufA = NULL, *bufB = NULL;
static int *defA = NULL, *defB = NULL;
static int *beu = NULL, *bev = NULL, *bcol = NULL;
static int bn = 0, bm = 0;
static clock_t deadline;
static int stopped = 0;
static u64 rs = 0x9E3779B97F4A7C15ULL;

#define ADJ(a, b) adj[(size_t)(a) * (size_t)cap + (size_t)(b)]

static u64 rnext(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}

static int rnd(int k) { return (int)(rnext() % (u64)k); }

static double rnd01(void) { return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0); }

static int timeout_now(void) {
    if (!stopped && clock() >= deadline) stopped = 1;
    return stopped;
}

static void set_edge(int a, int b, int on) {
    ADJ(a, b) = (unsigned char)on;
    ADJ(b, a) = (unsigned char)on;
}

static int popc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of ordered pairs (v, w) with dist(v, w) > diam. Zero means valid. */
static long long cost_full(void) {
    int n = nv;
    int W = (n + 63) >> 6;
    u64 *cur = bufA, *nxt = bufB;
    size_t sz = (size_t)n * (size_t)W;
    memset(cur, 0, sizeof(u64) * sz);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < diam; it++) {
        memcpy(nxt, cur, sizeof(u64) * sz);
        for (int e = 0; e < ne; e++) {
            size_t a = (size_t)eu[e] * W, b = (size_t)ev[e] * W;
            for (int k = 0; k < W; k++) {
                nxt[a + k] |= cur[b + k];
                nxt[b + k] |= cur[a + k];
            }
        }
        u64 *t = cur; cur = nxt; nxt = t;
    }
    long long c = 0;
    for (int v = 0; v < n; v++) {
        int cnt = 0;
        for (int k = 0; k < W; k++) cnt += popc64(cur[(size_t)v * W + k]);
        c += n - cnt;
    }
    return c;
}

/* Degree-preserving double edge swap: (a,b),(c,e) -> (a,e),(c,b). */
static int move_swap(undo_t *u) {
    if (ne < 2) return 0;
    int i = rnd(ne), j = rnd(ne);
    if (i == j) return 0;
    int a = eu[i], b = ev[i], c = eu[j], e = ev[j];
    if (a == c || b == e) return 0;
    if (ADJ(a, e) || ADJ(c, b)) return 0;
    set_edge(a, b, 0);
    set_edge(c, e, 0);
    set_edge(a, e, 1);
    set_edge(c, b, 1);
    eu[i] = a; ev[i] = e;
    eu[j] = c; ev[j] = b;
    u->kind = 1; u->i = i; u->j = j; u->a = a; u->b = b; u->c = c; u->e = e;
    return 1;
}

/* Move an edge's B-end to a deficient B-vertex: (a,b) -> (a,e). */
static int move_transfer(undo_t *u, int nd) {
    if (ne < 1 || nd < 1) return 0;
    int i = rnd(ne);
    int a = eu[i], b = ev[i];
    int e = defB[rnd(nd)];
    if (e == b || ADJ(a, e)) return 0;
    set_edge(a, b, 0);
    set_edge(a, e, 1);
    ev[i] = e;
    deg[b]--;
    deg[e]++;
    u->kind = 3; u->i = i; u->a = a; u->b = b; u->e = e;
    return 1;
}

/* Insert an edge between a deficient A-vertex and a deficient B-vertex. */
static int move_add(undo_t *u, int na, int nb) {
    if (na < 1 || nb < 1) return 0;
    for (int t = 0; t < 20; t++) {
        int a = defA[rnd(na)], b = defB[rnd(nb)];
        if (!ADJ(a, b)) {
            eu[ne] = a; ev[ne] = b; ne++;
            set_edge(a, b, 1);
            deg[a]++; deg[b]++;
            u->kind = 2; u->a = a; u->b = b;
            return 1;
        }
    }
    return 0;
}

static void undo(const undo_t *u) {
    switch (u->kind) {
    case 1:
        set_edge(u->a, u->e, 0);
        set_edge(u->c, u->b, 0);
        set_edge(u->a, u->b, 1);
        set_edge(u->c, u->e, 1);
        eu[u->i] = u->a; ev[u->i] = u->b;
        eu[u->j] = u->c; ev[u->j] = u->e;
        break;
    case 2:
        ne--;
        set_edge(u->a, u->b, 0);
        deg[u->a]--; deg[u->b]--;
        break;
    case 3:
        set_edge(u->a, u->e, 0);
        set_edge(u->a, u->b, 1);
        ev[u->i] = u->b;
        deg[u->b]++;
        deg[u->e]--;
        break;
    default:
        break;
    }
}

static long long anneal(long long cur, long iters, double T0, double T1) {
    undo_t u;
    for (long it = 0; it < iters; it++) {
        if ((it & 31) == 0 && timeout_now()) return cur;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int na = 0, nb = 0;
        for (int v = 0; v < nv; v++) {
            if (deg[v] < dgr) {
                if (col[v] == 0) defA[na++] = v;
                else defB[nb++] = v;
            }
        }
        double r = rnd01();
        int ok;
        if (r < 0.65) ok = move_swap(&u);
        else if (r < 0.85) ok = move_transfer(&u, nb);
        else ok = move_add(&u, na, nb);
        if (!ok) continue;
        long long c2 = cost_full();
        long long delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = c2;
            if (cur == 0) return 0;
        } else {
            undo(&u);
        }
    }
    return cur;
}

static void save_best(void) {
    bn = nv; bm = ne;
    memcpy(beu, eu, sizeof(int) * (size_t)ne);
    memcpy(bev, ev, sizeof(int) * (size_t)ne);
    memcpy(bcol, col, sizeof(int) * (size_t)nv);
}

static void restore_best(void) {
    nv = bn; ne = bm;
    memcpy(eu, beu, sizeof(int) * (size_t)ne);
    memcpy(ev, bev, sizeof(int) * (size_t)ne);
    memcpy(col, bcol, sizeof(int) * (size_t)nv);
    memset(adj, 0, (size_t)cap * (size_t)cap);
    for (int v = 0; v < nv; v++) deg[v] = 0;
    for (int e = 0; e < ne; e++) {
        set_edge(eu[e], ev[e], 1);
        deg[eu[e]]++;
        deg[ev[e]]++;
    }
}

/* Add two vertices x (side 0) and y (side 1) by rewiring a matching of d edges. */
static int grow(void) {
    if (nv + 2 > cap || ne < dgr) return 0;
    int *perm = malloc(sizeof(int) * (size_t)ne);
    for (int i = 0; i < ne; i++) perm[i] = i;
    for (int i = ne - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
    }
    char *usedA = calloc((size_t)nv, 1);
    char *usedB = calloc((size_t)nv, 1);
    int *sel = malloc(sizeof(int) * (size_t)dgr);
    int k = 0;
    for (int t = 0; t < ne && k < dgr; t++) {
        int idx = perm[t];
        int a = eu[idx], b = ev[idx];
        if (!usedA[a] && !usedB[b]) {
            usedA[a] = 1; usedB[b] = 1;
            sel[k++] = idx;
        }
    }
    free(perm); free(usedA); free(usedB);
    if (k < dgr) { free(sel); return 0; }

    int *As = malloc(sizeof(int) * (size_t)dgr);
    int *Bs = malloc(sizeof(int) * (size_t)dgr);
    for (int t = 0; t < dgr; t++) {
        int idx = sel[t];
        As[t] = eu[idx];
        Bs[t] = ev[idx];
        set_edge(As[t], Bs[t], 0);
    }
    int x = nv, y = nv + 1;
    col[x] = 0; col[y] = 1;
    deg[x] = dgr; deg[y] = dgr;
    for (int t = 0; t < dgr; t++) {
        int idx = sel[t];
        eu[idx] = x; ev[idx] = Bs[t];
        set_edge(x, Bs[t], 1);
    }
    for (int t = 0; t < dgr; t++) {
        eu[ne] = As[t]; ev[ne] = y; ne++;
        set_edge(As[t], y, 1);
    }
    nv += 2;
    free(sel); free(As); free(Bs);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    dgr = atoi(argv[1]);
    diam = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= seed * 0xD1B54A32D192ED03ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    deadline = clock() + (clock_t)(tl * (double)CLOCKS_PER_SEC);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 <= 0 || m0 < 0 || dgr < 1 || diam < 2) {
        printf("0 0\n");
        return 0;
    }
    int *ru = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *rv = malloc(sizeof(int) * (size_t)(m0 + 1));
    int mm = 0;
    for (int i = 0; i < m0; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a < 0 || b < 0 || a >= n0 || b >= n0 || a == b) continue;
        ru[mm] = a; rv[mm] = b; mm++;
    }

    /* Bipartition by BFS over a CSR copy of the input. */
    int *dg0 = calloc((size_t)n0, sizeof(int));
    for (int i = 0; i < mm; i++) { dg0[ru[i]]++; dg0[rv[i]]++; }
    int *off = malloc(sizeof(int) * (size_t)(n0 + 1));
    off[0] = 0;
    for (int v = 0; v < n0; v++) off[v + 1] = off[v] + dg0[v];
    int *fill = malloc(sizeof(int) * (size_t)n0);
    for (int v = 0; v < n0; v++) fill[v] = off[v];
    int *nb = malloc(sizeof(int) * (size_t)(2 * mm + 1));
    for (int i = 0; i < mm; i++) {
        nb[fill[ru[i]]++] = rv[i];
        nb[fill[rv[i]]++] = ru[i];
    }
    int *tc = malloc(sizeof(int) * (size_t)n0);
    int *q = malloc(sizeof(int) * (size_t)n0);
    for (int v = 0; v < n0; v++) tc[v] = -1;
    int bip = 1;
    for (int s = 0; s < n0; s++) {
        if (tc[s] >= 0) continue;
        tc[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            for (int k = off[u]; k < off[u + 1]; k++) {
                int w = nb[k];
                if (tc[w] < 0) {
                    tc[w] = 1 - tc[u];
                    q[tail++] = w;
                } else if (tc[w] == tc[u]) {
                    bip = 0;
                }
            }
        }
    }
    if (!bip) {
        printf("0 0\n");
        return 0;
    }

    cap = n0 + 400;
    capW = (cap + 63) >> 6;
    size_t ecap = (size_t)cap * (size_t)dgr + (size_t)mm + 16;
    eu = malloc(sizeof(int) * ecap);
    ev = malloc(sizeof(int) * ecap);
    beu = malloc(sizeof(int) * ecap);
    bev = malloc(sizeof(int) * ecap);
    deg = calloc((size_t)cap, sizeof(int));
    col = calloc((size_t)cap, sizeof(int));
    bcol = calloc((size_t)cap, sizeof(int));
    defA = malloc(sizeof(int) * (size_t)cap);
    defB = malloc(sizeof(int) * (size_t)cap);
    adj = calloc((size_t)cap * (size_t)cap, 1);
    bufA = malloc(sizeof(u64) * (size_t)cap * (size_t)capW);
    bufB = malloc(sizeof(u64) * (size_t)cap * (size_t)capW);

    nv = n0;
    ne = 0;
    for (int v = 0; v < n0; v++) col[v] = tc[v];
    for (int i = 0; i < mm; i++) {
        int u = ru[i], v = rv[i];
        if (ADJ(u, v)) continue;
        if (deg[u] >= dgr || deg[v] >= dgr) continue;
        set_edge(u, v, 1);
        deg[u]++; deg[v]++;
        if (col[u] == 0) { eu[ne] = u; ev[ne] = v; }
        else { eu[ne] = v; ev[ne] = u; }
        ne++;
    }

    long long cur = cost_full();
    if (cur == 0) save_best();

    int fails = 0;
    const long K = 8000;
    while (!timeout_now()) {
        if (cur == 0) {
            if (nv > bn) save_best();
            if (!grow()) break;
            cur = cost_full();
            fails = 0;
            continue;
        }
        cur = anneal(cur, K, 2.0, 0.05);
        if (cur == 0) continue;
        fails++;
        if (fails >= 4 && bn > 0) {
            restore_best();
            if (!grow()) break;
            cur = cost_full();
            fails = 0;
        }
    }
    if (cur == 0 && nv > bn) save_best();

    printf("%d %d\n", bn, bm);
    for (int e = 0; e < bm; e++) printf("%d %d\n", beu[e], bev[e]);
    return 0;
}
"""


# ------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = [lib.haar_graph(d, range(d))]

    def consider(n, e):
        if n > best[0][0] and lib.is_valid(n, e, d, D):
            best[0] = (n, e)

    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.2 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    start = best[0]
    if D <= 2 or start[0] >= lib.moore_bound(d, D):
        return start

    budget = t0 + 0.88 * time_limit - time.monotonic() - 2.0
    if budget < 2.0:
        return start

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=start, timeout=budget + 8.0)
        n, e = lib.parse_graph_text(text)
        consider(n, e)
    except (RuntimeError, ValueError):
        pass

    result = best[0]
    if not lib.is_valid(result[0], result[1], d, D):
        result = lib.haar_graph(d, range(d))
    return result
