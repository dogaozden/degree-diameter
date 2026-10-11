import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: simulated annealing on bipartite graphs with a bitset
# distance-D cost (number of ordered-once pairs farther than D apart).
#
# It starts from a valid graph given on stdin, repeatedly adds one vertex
# (joined to free vertices of the opposite side), and repairs the graph
# with edge swaps, edge additions and edge removals until every pair is
# within distance D again. Degrees stay <= d and the bipartition is kept
# by construction. If a restart is needed it reloads the best valid graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 1200
#define MAXDEG 40
#define MAXW ((MAXN + 63) / 64)
#define MAXE (MAXN * MAXDEG / 2)
#define STALE 30000

static int d_, D_;
static int n_;
static int side_[MAXN];
static int deg_[MAXN];
static int adj_[MAXN][MAXDEG];
static uint64_t bufA_[MAXN][MAXW];
static uint64_t bufB_[MAXN][MAXW];
static int bestN_ = 0, bestM_ = 0;
static int bestSide_[MAXN];
static int bestEu_[MAXE], bestEv_[MAXE];
static int inU_[MAXE], inV_[MAXE];
static int mA, mB, mC, mE;
static uint64_t rs_ = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs_ ^= rs_ << 13;
    rs_ ^= rs_ >> 7;
    rs_ ^= rs_ << 17;
    return rs_;
}
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndf(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg_[a]; i++)
        if (adj_[a][i] == b) return 1;
    return 0;
}

static void del_arc(int a, int b) {
    for (int i = 0; i < deg_[a]; i++) {
        if (adj_[a][i] == b) {
            adj_[a][i] = adj_[a][--deg_[a]];
            return;
        }
    }
}

static void add_edge(int a, int b) {
    adj_[a][deg_[a]++] = b;
    adj_[b][deg_[b]++] = a;
}

static void del_edge(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
}

/* Number of ordered pairs (v, w), v != w, at distance > D_ (counted once per v). */
static long long cost_full(void) {
    int n = n_;
    int w = (n + 63) / 64;
    uint64_t (*cur)[MAXW] = bufA_;
    uint64_t (*nx)[MAXW] = bufB_;
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * (size_t)w);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < n; v++) {
            memcpy(nx[v], cur[v], sizeof(uint64_t) * (size_t)w);
            for (int i = 0; i < deg_[v]; i++) {
                int u = adj_[v][i];
                for (int k = 0; k < w; k++) nx[v][k] |= cur[u][k];
            }
        }
        uint64_t (*tmp)[MAXW] = cur;
        cur = nx;
        nx = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int k = 0; k < w; k++) c += pc64(cur[v][k]);
        bad += n - c;
    }
    return bad;
}

static void record_best(void) {
    bestN_ = n_;
    bestM_ = 0;
    for (int v = 0; v < n_; v++) {
        bestSide_[v] = side_[v];
        for (int i = 0; i < deg_[v]; i++) {
            int u = adj_[v][i];
            if (u > v && bestM_ < MAXE) {
                bestEu_[bestM_] = v;
                bestEv_[bestM_] = u;
                bestM_++;
            }
        }
    }
}

static void restore_best(void) {
    n_ = bestN_;
    for (int v = 0; v < n_; v++) {
        deg_[v] = 0;
        side_[v] = bestSide_[v];
    }
    for (int e = 0; e < bestM_; e++) add_edge(bestEu_[e], bestEv_[e]);
}

/* Append one vertex on a random side, joined to up to d_ free vertices of the other side. */
static int grow(void) {
    if (n_ >= MAXN) return 0;
    int s = rndi(2);
    static int cand[MAXN];
    int nc = 0;
    for (int u = 0; u < n_; u++)
        if (side_[u] != s && deg_[u] < d_) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    int v = n_++;
    side_[v] = s;
    deg_[v] = 0;
    int k = nc < d_ ? nc : d_;
    for (int i = 0; i < k; i++) add_edge(v, cand[i]);
    return 1;
}

/* Swap a-b, c-e (same side a,c) into a-e, c-b. Degrees are preserved. */
static int try_swap(void) {
    int a = rndi(n_);
    if (deg_[a] == 0) return 0;
    int b = adj_[a][rndi(deg_[a])];
    int c = -1;
    for (int t = 0; t < 20; t++) {
        int x = rndi(n_);
        if (x != a && side_[x] == side_[a] && deg_[x] > 0) {
            c = x;
            break;
        }
    }
    if (c < 0) return 0;
    int e = adj_[c][rndi(deg_[c])];
    if (e == b) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    mA = a; mB = b; mC = c; mE = e;
    return 1;
}

static int try_add(void) {
    for (int t = 0; t < 20; t++) {
        int a = rndi(n_), c = rndi(n_);
        if (a == c || side_[a] == side_[c]) continue;
        if (deg_[a] >= d_ || deg_[c] >= d_) continue;
        if (has_edge(a, c)) continue;
        add_edge(a, c);
        mA = a; mB = c;
        return 1;
    }
    return 0;
}

static int try_remove(void) {
    for (int t = 0; t < 50; t++) {
        int a = rndi(n_);
        if (deg_[a] > 0) {
            int b = adj_[a][rndi(deg_[a])];
            del_edge(a, b);
            mA = a; mB = b;
            return 1;
        }
    }
    return 0;
}

static void undo(int kind) {
    if (kind == 1) {
        del_edge(mA, mE);
        del_edge(mC, mB);
        add_edge(mA, mB);
        add_edge(mC, mE);
    } else if (kind == 2) {
        del_edge(mA, mB);
    } else {
        add_edge(mA, mB);
    }
}

static int color_sides(void) {
    static int col[MAXN], q[MAXN];
    for (int v = 0; v < n_; v++) col[v] = -1;
    for (int s = 0; s < n_; s++) {
        if (col[s] >= 0) continue;
        int qh = 0, qt = 0;
        col[s] = 0;
        q[qt++] = s;
        while (qh < qt) {
            int v = q[qh++];
            for (int i = 0; i < deg_[v]; i++) {
                int u = adj_[v][i];
                if (col[u] < 0) {
                    col[u] = 1 - col[v];
                    q[qt++] = u;
                } else if (col[u] == col[v]) {
                    return 0;
                }
            }
        }
    }
    for (int v = 0; v < n_; v++) side_[v] = col[v];
    return 1;
}

static void default_graph(void) {
    memset(deg_, 0, sizeof(deg_));
    n_ = 2;
    side_[0] = 0;
    side_[1] = 1;
    add_edge(0, 1);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs_ ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs_ == 0) rs_ = 1;
    double limit = atof(argv[4]);
    if (d_ < 1 || d_ > MAXDEG) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < 10; i++) rnd();
    double t0 = now_s();

    int ok = 1;
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 2 || n0 > MAXN || m0 < 1 || m0 > MAXE) ok = 0;
    for (int i = 0; i < m0 && ok; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { ok = 0; break; }
        inU_[i] = u;
        inV_[i] = v;
    }
    if (ok) {
        memset(deg_, 0, sizeof(deg_));
        n_ = n0;
        for (int i = 0; i < m0 && ok; i++) {
            int u = inU_[i], v = inV_[i];
            if (deg_[u] >= d_ || deg_[v] >= d_ || has_edge(u, v)) { ok = 0; break; }
            add_edge(u, v);
        }
        if (ok && !color_sides()) ok = 0;
    }
    if (!ok) default_graph();

    long long cost = cost_full();
    if (cost == 0 && n_ > bestN_) record_best();

    long long stale = 0;
    const double T = 1.0;
    unsigned long it = 0;
    while (1) {
        if ((it & 63) == 0 && now_s() - t0 > limit) break;
        it++;
        if (cost == 0) {
            if (n_ > bestN_) record_best();
            if (!grow()) break;
            cost = cost_full();
            stale = 0;
            continue;
        }
        if (++stale > STALE) {
            if (bestN_ == 0) break;
            restore_best();
            cost = cost_full();
            stale = 0;
            if (cost != 0) break;
            continue;
        }
        int r = rndi(100);
        int kind;
        if (r < 60) {
            if (!try_swap()) continue;
            kind = 1;
        } else if (r < 95) {
            if (!try_add()) continue;
            kind = 2;
        } else {
            if (!try_remove()) continue;
            kind = 3;
        }
        long long nc = cost_full();
        long long delta = nc - cost;
        if (delta <= 0 || rndf() < exp(-(double)delta / T)) {
            cost = nc;
        } else {
            undo(kind);
        }
    }
    if (cost == 0 && n_ > bestN_) record_best();

    if (bestN_ == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN_, bestM_);
    for (int e = 0; e < bestM_; e++) printf("%d %d\n", bestEu_[e], bestEv_[e]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), Python side.
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1, so with d >= q+1 it has spare s = d - q - 1. New A-vertices
# attach to all lines through a chosen point (each line hit <= s times); new
# B-vertices attach to all points of a chosen line (each point hit <= s times).
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
# Generalized quadrangle W(q) baseline (D = 4).
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
# build(): construct a valid start graph in Python, then let the C annealer
# add vertices and repair the graph. Every candidate is checked by lib.is_valid,
# and the K_{d,d} fallback is always kept.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    rng = random.Random(seed * 7919 + d)
    if D >= 3:
        for n_c, e_c in _arc_extensions(d, t0 + 0.2 * time_limit, rng):
            consider(n_c, e_c)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Bold change: C annealing with vertex insertion and bitset-based repair
    # replaces the Python group-lift search. Keep a safety margin for compile and I/O.
    remaining = time_limit - (time.monotonic() - t0)
    budget = remaining - 8.0
    if D >= 3 and budget >= 3.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=remaining - 2.0)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
