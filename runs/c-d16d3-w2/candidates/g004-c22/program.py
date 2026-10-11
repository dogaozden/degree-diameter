import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with d >= q+1 it has spare s = d - q - 1. Add one new point-side vertex per
# chosen point (joined to the q+1 lines through it) and one new line-side vertex
# per chosen line, with each old line loaded by <= s new point-side vertices and
# each old point loaded by <= s new line-side vertices.
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
# NEW: C engine. Annealed vertex growth on a bipartite graph.
#
# Starting from a valid graph, repeatedly add one vertex on the less-used side,
# connect it to spare-degree vertices of the other side, and anneal with
# degree-preserving 2-switches, spare-slot rewires and free edge additions.
# The cost is the number of vertex pairs at distance > D, computed with bitset
# BFS. A growth step is committed only when the cost reaches zero; otherwise
# the state is restored from the snapshot taken before the step.
# ----------------------------------------------------------------------------

_C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1200
#define MAXD 64
#define MAXW ((MAXN + 63) / 64)
#define MAXE (MAXN * MAXD / 2)

static int N, DEG, DIST;
static int side_[MAXN];
static int deg_[MAXN];
static int adj_[MAXN][MAXD];
static unsigned char am_[MAXN][MAXN];
static uint64_t BA_[MAXN][MAXW], BB_[MAXN][MAXW];
static uint64_t rs_;
static int snap_u[MAXE], snap_v[MAXE];
static int qbuf[MAXN], cand[MAXN];

static uint64_t rnd64(void) {
    rs_ ^= rs_ << 13;
    rs_ ^= rs_ >> 7;
    rs_ ^= rs_ << 17;
    return rs_;
}
static int rint_(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void rem_from(int a, int b) {
    for (int k = 0; k < deg_[a]; k++) {
        if (adj_[a][k] == b) {
            adj_[a][k] = adj_[a][--deg_[a]];
            return;
        }
    }
}
static void mv_add(int a, int b) {
    am_[a][b] = 1;
    am_[b][a] = 1;
    adj_[a][deg_[a]++] = b;
    adj_[b][deg_[b]++] = a;
}
static void mv_del(int a, int b) {
    am_[a][b] = 0;
    am_[b][a] = 0;
    rem_from(a, b);
    rem_from(b, a);
}

/* Number of unordered pairs at distance > DIST (0 means valid). */
static long long eval_cost(void) {
    int W = (N + 63) >> 6;
    uint64_t (*cur)[MAXW] = BA_;
    uint64_t (*nxt)[MAXW] = BB_;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIST; r++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < deg_[v]; k++) {
                int u = adj_[v][k];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        tot += N - c;
    }
    return tot / 2;
}

typedef struct { int type, a, b, c, e; } Move;

/* Propose and apply a random move. Returns 1 if a move was applied. */
static int propose(Move *m) {
    int t = rint_(10);
    if (t < 5) {
        /* degree-preserving 2-switch between two side-0 edges */
        int p = rint_(N);
        if (side_[p] != 0 || deg_[p] == 0) return 0;
        int l1 = adj_[p][rint_(deg_[p])];
        int p2 = rint_(N);
        if (p2 == p || side_[p2] != 0 || deg_[p2] == 0) return 0;
        int l2 = adj_[p2][rint_(deg_[p2])];
        if (l2 == l1 || am_[p][l2] || am_[p2][l1]) return 0;
        mv_del(p, l1);
        mv_del(p2, l2);
        mv_add(p, l2);
        mv_add(p2, l1);
        m->type = 0; m->a = p; m->b = l1; m->c = p2; m->e = l2;
        return 1;
    }
    if (t < 8) {
        /* move one endpoint of an edge onto a spare-degree vertex of the same side */
        int a = rint_(N);
        if (deg_[a] == 0) return 0;
        int b = adj_[a][rint_(deg_[a])];
        int w = -1;
        for (int tr = 0; tr < 60; tr++) {
            int c = rint_(N);
            if (c != b && side_[c] == side_[b] && deg_[c] < DEG && !am_[a][c]) { w = c; break; }
        }
        if (w < 0) return 0;
        mv_del(a, b);
        mv_add(a, w);
        m->type = 1; m->a = a; m->b = b; m->c = w;
        return 1;
    }
    {
        /* free edge addition: can only shorten distances */
        int u = -1;
        for (int tr = 0; tr < 60; tr++) {
            int c = rint_(N);
            if (deg_[c] < DEG) { u = c; break; }
        }
        if (u < 0) return 0;
        int w = -1;
        for (int tr = 0; tr < 60; tr++) {
            int c = rint_(N);
            if (side_[c] != side_[u] && deg_[c] < DEG && !am_[u][c]) { w = c; break; }
        }
        if (w < 0) return 0;
        mv_add(u, w);
        m->type = 2; m->a = u; m->b = w;
        return 1;
    }
}

static void undo(const Move *m) {
    if (m->type == 0) {
        mv_del(m->a, m->e);
        mv_del(m->c, m->b);
        mv_add(m->a, m->b);
        mv_add(m->c, m->e);
    } else if (m->type == 1) {
        mv_del(m->a, m->c);
        mv_add(m->a, m->b);
    } else {
        mv_del(m->a, m->b);
    }
}

static void restore(int snapN, int ne) {
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < deg_[v]; k++) am_[v][adj_[v][k]] = 0;
        deg_[v] = 0;
    }
    N = snapN;
    for (int i = 0; i < ne; i++) mv_add(snap_u[i], snap_v[i]);
}

static void emit(void) {
    int M = 0;
    for (int v = 0; v < N; v++)
        if (side_[v] == 0) M += deg_[v];
    printf("%d %d\n", N, M);
    for (int v = 0; v < N; v++)
        if (side_[v] == 0)
            for (int k = 0; k < deg_[v]; k++)
                printf("%d %d\n", v, adj_[v][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (d < 1 || d >= MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    DEG = d;
    DIST = D;
    rs_ = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs_ == 0) rs_ = 1;
    for (int i = 0; i < 10; i++) rnd64();

    clock_t c0 = clock();
    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 1 || n > MAXN / 2) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (am_[u][v] || deg_[u] >= DEG || deg_[v] >= DEG) continue;
        mv_add(u, v);
    }

    /* bipartition by BFS */
    for (int v = 0; v < N; v++) side_[v] = -1;
    int ok = 1;
    for (int s = 0; s < N; s++) {
        if (side_[s] >= 0) continue;
        side_[s] = 0;
        int qh = 0, qt = 0;
        qbuf[qt++] = s;
        while (qh < qt) {
            int v = qbuf[qh++];
            for (int k = 0; k < deg_[v]; k++) {
                int u = adj_[v][k];
                if (side_[u] < 0) {
                    side_[u] = 1 - side_[v];
                    qbuf[qt++] = u;
                } else if (side_[u] == side_[v]) {
                    ok = 0;
                }
            }
        }
    }
    if (!ok || eval_cost() != 0) {
        printf("0 0\n");
        return 0;
    }

    const int K = 8000;
    long attempts = 0;
    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el > budget || N >= MAXN - 2) break;
        attempts++;

        /* snapshot of the committed state */
        int snapN = N, ne = 0;
        for (int v = 0; v < N; v++) {
            if (side_[v] != 0) continue;
            for (int k = 0; k < deg_[v]; k++) {
                snap_u[ne] = v;
                snap_v[ne] = adj_[v][k];
                ne++;
            }
        }

        /* add one vertex on alternating sides and connect it to spare vertices */
        int ns = (int)(attempts & 1);
        int x = N++;
        side_[x] = ns;
        deg_[x] = 0;
        int nc = 0;
        for (int v = 0; v < x; v++)
            if (side_[v] != ns && deg_[v] < DEG) cand[nc++] = v;
        for (int i = nc - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int tmp = cand[i];
            cand[i] = cand[j];
            cand[j] = tmp;
        }
        for (int i = 0; i < nc && deg_[x] < DEG; i++) mv_add(x, cand[i]);

        long long cur = eval_cost();
        int timed_out = 0;
        for (int it = 0; it < K && cur > 0; it++) {
            if ((it & 255) == 0) {
                double e2 = (double)(clock() - c0) / CLOCKS_PER_SEC;
                if (e2 > budget) { timed_out = 1; break; }
            }
            double T = 1.0 * pow(0.03, (double)it / K);
            Move mv;
            if (!propose(&mv)) continue;
            long long c2 = eval_cost();
            long long delta = c2 - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cur = c2;
            } else {
                undo(&mv);
            }
        }

        if (cur != 0) restore(snapN, ne);
        if (timed_out && cur != 0) break;
    }

    if (eval_cost() != 0) {
        printf("0 0\n");
        return 0;
    }
    emit();
    return 0;
}
'''


def _grow_with_c(best, d, D, seed, budget):
    """Run the C growth engine from the graph `best` for about `budget` seconds. Returns (n, edges) or None."""
    out = lib.run_c(_C_SOURCE, [d, D, seed, round(budget, 2)], stdin_graph=best,
                    timeout=budget + 6.0)
    return lib.parse_graph_text(out)


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
        arc_deadline = start + 0.25 * time_limit
        cands = _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < start + 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # NEW: C-side annealed vertex growth from the best graph found so far.
    # Skipped when the graph already meets the Moore bound (no spare degree to use).
    if D >= 3 and d < 60 and best_n < lib.moore_bound(d, D):
        remaining = time_limit - (time.monotonic() - start)
        c_budget = 0.8 * remaining - 2.0
        if c_budget > 1.0:
            try:
                n2, e2 = _grow_with_c(best, d, D, seed, c_budget)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
