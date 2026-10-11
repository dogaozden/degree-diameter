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
# C engine: simulated annealing over degree-bounded bipartite graphs.
#
# Cost = number of ordered vertex pairs at distance > D (0 means valid).
# Distances are checked with bitset balls of radius D, one round per step.
# Moves keep max degree <= d and bipartiteness:
#   - 2-switch on two edges (degrees preserved),
#   - rewire one endpoint of an edge to a deficient vertex,
#   - add an edge between two deficient vertices on opposite sides (always improves or keeps cost).
# When cost reaches 0 the current graph is saved and grown by one vertex: the new vertex on
# one side is joined to d vertices of the other side, each of which drops one old edge.
# If the search stalls, it restores the best valid graph and reheats.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

typedef uint64_t u64;

static int D_, DEG_, CAP, WM, n, bn = -1;
static int *deg, *adj, *col, *pool, *queue_;
static int *bdeg, *badj, *bcol;
static unsigned char *am;
static u64 *R0, *R1;
static unsigned long long rs = 88172645463325252ULL;

static unsigned long long rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (unsigned long long)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_e(int a, int b) {
    adj[(size_t)a * DEG_ + deg[a]++] = b;
    adj[(size_t)b * DEG_ + deg[b]++] = a;
    am[(size_t)a * CAP + b] = 1;
    am[(size_t)b * CAP + a] = 1;
}

static void rem_from(int a, int b) {
    int *p = adj + (size_t)a * DEG_;
    for (int j = 0; j < deg[a]; j++) {
        if (p[j] == b) {
            p[j] = p[deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void del_e(int a, int b) {
    rem_from(a, b);
    rem_from(b, a);
    am[(size_t)a * CAP + b] = 0;
    am[(size_t)b * CAP + a] = 0;
}

/* Operation log for undoing one move. */
typedef struct { int t, a, b; } Op;
static Op olog[8];
static int on = 0;

static void op_add(int a, int b) {
    add_e(a, b);
    olog[on].t = 0; olog[on].a = a; olog[on].b = b; on++;
}
static void op_del(int a, int b) {
    del_e(a, b);
    olog[on].t = 1; olog[on].a = a; olog[on].b = b; on++;
}
static void undo_all(void) {
    while (on > 0) {
        on--;
        if (olog[on].t == 0) del_e(olog[on].a, olog[on].b);
        else add_e(olog[on].a, olog[on].b);
    }
}

/* Number of ordered pairs at distance > D_ (0 iff valid, given bipartite and connected). */
static long long eval_cost(void) {
    int Wn = (n + 63) / 64;
    u64 *cur = R0, *nxt = R1;
    for (int v = 0; v < n; v++) {
        u64 *row = cur + (size_t)v * WM;
        for (int w = 0; w < Wn; w++) row[w] = 0;
        row[v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < n; v++) {
            u64 *out = nxt + (size_t)v * WM;
            const u64 *in = cur + (size_t)v * WM;
            for (int w = 0; w < Wn; w++) out[w] = in[w];
            for (int k = 0; k < deg[v]; k++) {
                const u64 *src = cur + (size_t)adj[(size_t)v * DEG_ + k] * WM;
                for (int w = 0; w < Wn; w++) out[w] |= src[w];
            }
        }
        u64 *t = cur; cur = nxt; nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        const u64 *row = cur + (size_t)v * WM;
        int c = 0;
        for (int w = 0; w < Wn; w++) c += pc64(row[w]);
        bad += n - c;
    }
    return bad;
}

static void snap_save(void) {
    bn = n;
    memcpy(bdeg, deg, sizeof(int) * (size_t)n);
    memcpy(bcol, col, sizeof(int) * (size_t)n);
    memcpy(badj, adj, sizeof(int) * (size_t)n * DEG_);
}

static void snap_load(void) {
    n = bn;
    memcpy(deg, bdeg, sizeof(int) * (size_t)n);
    memcpy(col, bcol, sizeof(int) * (size_t)n);
    memcpy(adj, badj, sizeof(int) * (size_t)n * DEG_);
    memset(am, 0, (size_t)CAP * CAP);
    for (int v = 0; v < n; v++)
        for (int k = 0; k < deg[v]; k++)
            am[(size_t)v * CAP + adj[(size_t)v * DEG_ + k]] = 1;
}

/* Pick a uniformly random edge, oriented so that a is on side 0 and b on side 1. */
static int pick_edge(int *a, int *b) {
    for (int t = 0; t < 100; t++) {
        int x = rndint(n);
        if (deg[x] == 0) continue;
        int y = adj[(size_t)x * DEG_ + rndint(deg[x])];
        if (col[x] == 0) { *a = x; *b = y; }
        else { *a = y; *b = x; }
        return 1;
    }
    return 0;
}

/* Degree-preserving 2-switch: (a,b),(c,e) -> (a,e),(c,b). */
static int move_switch(void) {
    int a, b, c, e;
    if (!pick_edge(&a, &b) || !pick_edge(&c, &e)) return 0;
    if (a == c || b == e) return 0;
    if (am[(size_t)a * CAP + e] || am[(size_t)c * CAP + b]) return 0;
    op_del(a, b); op_del(c, e);
    op_add(a, e); op_add(c, b);
    return 1;
}

/* Move one endpoint of an edge to a deficient vertex on the same side. */
static int move_rewire(void) {
    int a, b;
    if (!pick_edge(&a, &b)) return 0;
    if (rnd() & 1ULL) {
        for (int t = 0; t < 30; t++) {
            int e = rndint(n);
            if (col[e] != 1 || e == b || deg[e] >= DEG_) continue;
            if (am[(size_t)a * CAP + e]) continue;
            op_del(a, b); op_add(a, e);
            return 1;
        }
    } else {
        for (int t = 0; t < 30; t++) {
            int f = rndint(n);
            if (col[f] != 0 || f == a || deg[f] >= DEG_) continue;
            if (am[(size_t)f * CAP + b]) continue;
            op_del(a, b); op_add(f, b);
            return 1;
        }
    }
    return 0;
}

/* Add an edge between two deficient vertices on opposite sides. */
static int move_fill(void) {
    for (int t = 0; t < 60; t++) {
        int u = rndint(n);
        if (deg[u] >= DEG_) continue;
        for (int s = 0; s < 60; s++) {
            int w = rndint(n);
            if (w == u || col[w] == col[u] || deg[w] >= DEG_) continue;
            if (am[(size_t)u * CAP + w]) continue;
            op_add(u, w);
            return 1;
        }
    }
    return 0;
}

/* Add a new vertex on a random side, joined to up to DEG_ vertices of the other side. */
static void grow(void) {
    int c = rndint(2);
    int cnt = 0;
    for (int v = 0; v < n; v++)
        if (col[v] == c) pool[cnt++] = v;
    int need = DEG_ < cnt ? DEG_ : cnt;
    for (int i = 0; i < need; i++) {
        int j = i + rndint(cnt - i);
        int tmp = pool[i]; pool[i] = pool[j]; pool[j] = tmp;
    }
    int v = n++;
    deg[v] = 0;
    col[v] = 1 - c;
    for (int i = 0; i < need; i++) {
        int y = pool[i];
        if (deg[y] >= DEG_) {
            int z = adj[(size_t)y * DEG_ + rndint(deg[y])];
            del_e(y, z);
        }
        add_e(v, y);
    }
}

static void emit_state(int nn, const int *dg, const int *ad) {
    long m = 0;
    for (int v = 0; v < nn; v++) m += dg[v];
    m /= 2;
    printf("%d %ld\n", nn, m);
    for (int v = 0; v < nn; v++)
        for (int k = 0; k < dg[v]; k++) {
            int u = ad[(size_t)v * DEG_ + k];
            if (v < u) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (unsigned long long)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    double tl = atof(argv[4]);
    DEG_ = d;

    int nin = 0, min_ = 0;
    if (scanf("%d %d", &nin, &min_) != 2) { nin = 0; min_ = 0; }
    if (nin < 0) nin = 0;
    if (min_ < 0) min_ = 0;
    int *eu = malloc(sizeof(int) * (size_t)(min_ + 2));
    int *ev = malloc(sizeof(int) * (size_t)(min_ + 2));
    int m_read = 0;
    for (int i = 0; i < min_; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a < 0 || b < 0 || a >= nin || b >= nin || a == b) continue;
        eu[m_read] = a;
        ev[m_read] = b;
        m_read++;
    }
    if (nin == 0) {
        nin = 2;
        m_read = 1;
        eu[0] = 0;
        ev[0] = 1;
    }

    CAP = nin + 1500;
    WM = (CAP + 63) / 64;
    deg = calloc((size_t)CAP, sizeof(int));
    adj = calloc((size_t)CAP * DEG_, sizeof(int));
    col = malloc(sizeof(int) * (size_t)CAP);
    pool = malloc(sizeof(int) * (size_t)CAP);
    queue_ = malloc(sizeof(int) * (size_t)CAP);
    bdeg = calloc((size_t)CAP, sizeof(int));
    badj = calloc((size_t)CAP * DEG_, sizeof(int));
    bcol = calloc((size_t)CAP, sizeof(int));
    am = calloc((size_t)CAP * CAP, 1);
    R0 = calloc((size_t)CAP * WM, sizeof(u64));
    R1 = calloc((size_t)CAP * WM, sizeof(u64));

    n = nin;
    for (int i = 0; i < n; i++) col[i] = -1;
    for (int i = 0; i < m_read; i++) {
        int a = eu[i], b = ev[i];
        if (deg[a] < DEG_ && deg[b] < DEG_ && !am[(size_t)a * CAP + b]) add_e(a, b);
    }

    int bip = 1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        queue_[t++] = s;
        while (h < t) {
            int u = queue_[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[(size_t)u * DEG_ + k];
                if (col[v] < 0) { col[v] = 1 - col[u]; queue_[t++] = v; }
                else if (col[v] == col[u]) bip = 0;
            }
        }
    }
    if (!bip) {
        emit_state(n, deg, adj);
        return 0;
    }

    long long cur_cost = eval_cost();
    if (cur_cost == 0) snap_save();

    double t0 = now();
    long long stall = 0;
    const long long LIM = 40000;
    while (now() - t0 < tl) {
        if (cur_cost == 0) {
            if (n > bn) snap_save();
            if (n + 2 >= CAP) break;
            grow();
            cur_cost = eval_cost();
            stall = 0;
            continue;
        }
        stall++;
        if (stall > LIM) {
            if (bn >= 0) { snap_load(); cur_cost = eval_cost(); }
            stall = 0;
            continue;
        }
        double frac = (double)stall / (double)LIM;
        double T = 3.0 * (1.0 - frac) + 0.3 * frac;
        on = 0;
        int r = rndint(10);
        int ok;
        if (r < 5) ok = move_switch();
        else if (r < 8) ok = move_rewire();
        else ok = move_fill();
        if (!ok) continue;
        long long nc = eval_cost();
        long long dl = nc - cur_cost;
        if (dl <= 0 || rnd01() < exp(-(double)dl / T)) cur_cost = nc;
        else undo_all();
    }

    if (bn >= 0) emit_state(bn, bdeg, badj);
    else emit_state(n, deg, adj);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _start_graph(d, D, deadline, seed):
    """Best of the algebraic constructions that fit the deadline, or K_{d,d}."""
    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    if D >= 3:
        cands = _arc_extensions(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
                best = (n_c, e_c)
                break
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None and gq[0] > best[0] and lib.is_valid(gq[0], gq[1], d, D):
            best = gq
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _start_graph(d, D, t0 + 0.2 * time_limit, seed)
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    remaining = time_limit - (time.monotonic() - t0)
    budget = max(0.5, 0.85 * remaining - 1.5)
    if best[0] < 40:
        budget = min(budget, 3.0)
    timeout = max(budget + 1.0, 0.95 * remaining)

    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=best, timeout=timeout)
        n2, e2 = lib.parse_graph_text(out)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except (RuntimeError, ValueError):
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
