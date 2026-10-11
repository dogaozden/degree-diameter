import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bipartite vertex-insertion annealing for diameter D.
#
# The graph is kept bipartite with a fixed side per vertex, so every edge joins
# side 0 to side 1. A new vertex is inserted on one side and linked to random
# spare-degree vertices of the other side. Simulated annealing then repairs the
# graph under three moves: add an edge between spare vertices, or rewire one
# endpoint of an existing edge to another spare vertex on the same side. The
# cost is the number of unordered vertex pairs at distance > D, computed with
# bitset ball expansion. When the cost reaches 0 the graph is saved and the
# process grows again from that best graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define GROW_CAP 400
#define ITERS 20000
#define T_HI 1.2

static int d_, D_, NCAP, W, N, M;
static int *deg, *adj, *col, *eu, *ev;
static u64 *RA, *RB;
static int bestN, bestM;
static int *bestCol, *bestEu, *bestEv;
static u64 rs;
static double budget, w0;

static double wall(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static double elapsed(void) { return wall() - w0; }
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd() % (u64)n); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    const int *a = adj + (size_t)u * d_;
    for (int i = 0; i < deg[u]; i++) if (a[i] == v) return 1;
    return 0;
}
static void adj_add(int u, int v) { adj[(size_t)u * d_ + deg[u]++] = v; }
static void adj_del(int u, int v) {
    int *a = adj + (size_t)u * d_;
    for (int i = 0; i < deg[u]; i++) {
        if (a[i] == v) { a[i] = a[--deg[u]]; return; }
    }
}

/* Append edge between a and b (opposite sides). */
static void link_edge(int a, int b) {
    int x = a, y = b;
    if (col[a] != 0) { x = b; y = a; }
    adj_add(x, y); adj_add(y, x);
    eu[M] = x; ev[M] = y; M++;
}

/* Number of unordered pairs at distance > D_ (unreachable counts). */
static long long bad_cost(void) {
    int n = N;
    int Wn = (n + 63) >> 6;
    u64 *cur = RA, *nxt = RB;
    for (int v = 0; v < n; v++) {
        u64 *r = cur + (size_t)v * W;
        memset(r, 0, sizeof(u64) * (size_t)Wn);
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < n; v++) {
            u64 *dst = nxt + (size_t)v * W;
            const u64 *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(u64) * (size_t)Wn);
            const int *a = adj + (size_t)v * d_;
            for (int i = 0; i < deg[v]; i++) {
                const u64 *s2 = cur + (size_t)a[i] * W;
                for (int w = 0; w < Wn; w++) dst[w] |= s2[w];
            }
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long s = 0;
    for (int v = 0; v < n; v++) {
        const u64 *r = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < Wn; w++) c += pc64(r[w]);
        s += n - c;
    }
    return s / 2;
}

/* Simulated annealing at fixed N. Returns 1 if cost reached 0. */
static int anneal(long long iters, double T0) {
    long long cost = bad_cost();
    if (cost == 0) return 1;
    for (long long it = 0; it < iters; it++) {
        if ((it & 127) == 0 && elapsed() > budget) return 0;
        double T = T0 * (1.0 - (double)it / (double)iters) + 0.03;
        int r = rndint(100);
        if (r < 12) {
            /* add an edge between two spare vertices on opposite sides */
            int x = rndint(N), y = rndint(N);
            if (col[x] == col[y] || deg[x] >= d_ || deg[y] >= d_) continue;
            if (col[x] != 0) { int t = x; x = y; y = t; }
            if (has_edge(x, y)) continue;
            link_edge(x, y);
            long long c2 = bad_cost();
            long long delta = c2 - cost;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cost = c2;
            else { M--; adj_del(x, y); adj_del(y, x); }
        } else {
            /* rewire one endpoint of a random edge to another spare vertex */
            if (M == 0) continue;
            int e = rndint(M);
            int x = eu[e], y = ev[e];
            int side = rndint(2); /* 0: move y end (side 1), 1: move x end (side 0) */
            int c = -1;
            for (int tries = 0; tries < 40; tries++) {
                int cand = rndint(N);
                if (side == 0) {
                    if (col[cand] != 1 || cand == y || deg[cand] >= d_ || has_edge(x, cand)) continue;
                } else {
                    if (col[cand] != 0 || cand == x || deg[cand] >= d_ || has_edge(cand, y)) continue;
                }
                c = cand; break;
            }
            if (c < 0) continue;
            adj_del(x, y); adj_del(y, x);
            if (side == 0) { adj_add(x, c); adj_add(c, x); ev[e] = c; }
            else           { adj_add(c, y); adj_add(y, c); eu[e] = c; }
            long long c2 = bad_cost();
            long long delta = c2 - cost;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cost = c2;
            else {
                if (side == 0) {
                    adj_del(x, c); adj_del(c, x);
                    adj_add(x, y); adj_add(y, x); ev[e] = y;
                } else {
                    adj_del(c, y); adj_del(y, c);
                    adj_add(x, y); adj_add(y, x); eu[e] = x;
                }
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* Insert a new vertex on the side with more spare capacity opposite to it. */
static int grow(void) {
    if (N >= NCAP) return 0;
    int s0 = 0, s1 = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < d_) { if (col[v] == 0) s0++; else s1++; }
    }
    int c = (s1 >= s0) ? 0 : 1;
    int w = N++;
    col[w] = c; deg[w] = 0;
    int *cand = malloc(sizeof(int) * (size_t)(N + 1));
    int nc = 0;
    for (int v = 0; v < w; v++) {
        if (col[v] != c && deg[v] < d_) cand[nc++] = v;
    }
    for (int i = nc - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    int k = nc < d_ ? nc : d_;
    for (int i = 0; i < k; i++) link_edge(w, cand[i]);
    free(cand);
    return 1;
}

static void save_best(void) {
    bestN = N; bestM = M;
    memcpy(bestCol, col, sizeof(int) * (size_t)N);
    memcpy(bestEu, eu, sizeof(int) * (size_t)M);
    memcpy(bestEv, ev, sizeof(int) * (size_t)M);
}

static void load_best(void) {
    N = bestN; M = bestM;
    memset(deg, 0, sizeof(int) * (size_t)NCAP);
    for (int v = 0; v < N; v++) col[v] = bestCol[v];
    for (int e = 0; e < M; e++) {
        eu[e] = bestEu[e]; ev[e] = bestEv[e];
        adj_add(eu[e], ev[e]); adj_add(ev[e], eu[e]);
    }
}

static void output_best(void) {
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestEu[i], bestEv[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs = 0x9E3779B97F4A7C15ULL * (u64)(strtoull(argv[3], NULL, 10) + 1);
    if (rs == 0) rs = 88172645463325252ULL;
    budget = atof(argv[4]);
    w0 = wall();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 < 0 || d_ < 1) {
        printf("0 0\n");
        return 0;
    }
    int *ia = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *ib = malloc(sizeof(int) * (size_t)(m0 + 1));
    int mread = 0;
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &ia[mread], &ib[mread]) != 2) break;
        mread++;
    }
    m0 = mread;

    NCAP = n0 + GROW_CAP;
    W = (NCAP + 63) >> 6;
    deg = calloc((size_t)NCAP, sizeof(int));
    adj = calloc((size_t)NCAP * d_, sizeof(int));
    col = calloc((size_t)NCAP, sizeof(int));
    eu = calloc((size_t)NCAP * d_ + 1, sizeof(int));
    ev = calloc((size_t)NCAP * d_ + 1, sizeof(int));
    RA = calloc((size_t)NCAP * W, sizeof(u64));
    RB = calloc((size_t)NCAP * W, sizeof(u64));
    bestCol = calloc((size_t)NCAP, sizeof(int));
    bestEu = calloc((size_t)NCAP * d_ + 1, sizeof(int));
    bestEv = calloc((size_t)NCAP * d_ + 1, sizeof(int));

    /* keep only well-formed input edges */
    int k = 0;
    for (int i = 0; i < m0; i++) {
        int u = ia[i], v = ib[i];
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) continue;
        if (deg[u] >= d_ || deg[v] >= d_ || has_edge(u, v)) continue;
        adj_add(u, v); adj_add(v, u);
        ia[k] = u; ib[k] = v; k++;
    }
    m0 = k;
    N = n0;

    /* bipartition by BFS */
    int *stack = malloc(sizeof(int) * (size_t)(n0 + 1));
    int bip = 1;
    for (int v = 0; v < n0; v++) col[v] = -1;
    for (int s = 0; s < n0 && bip; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stack[sp++] = s;
        while (sp > 0 && bip) {
            int u = stack[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[(size_t)u * d_ + i];
                if (col[v] == -1) { col[v] = 1 - col[u]; stack[sp++] = v; }
                else if (col[v] == col[u]) { bip = 0; break; }
            }
        }
    }
    if (!bip) {
        bestN = n0; bestM = m0;
        for (int i = 0; i < m0; i++) { bestEu[i] = ia[i]; bestEv[i] = ib[i]; }
        output_best();
        return 0;
    }

    M = 0;
    for (int i = 0; i < m0; i++) {
        int x = ia[i], y = ib[i];
        if (col[x] != 0) { int t = x; x = y; y = t; }
        eu[M] = x; ev[M] = y; M++;
    }

    int valid = (bad_cost() == 0);
    if (!valid) valid = anneal(ITERS, T_HI);
    if (valid) {
        save_best();
    } else {
        bestN = n0; bestM = m0;
        for (int i = 0; i < m0; i++) { bestEu[i] = ia[i]; bestEv[i] = ib[i]; }
        output_best();
        return 0;
    }

    while (elapsed() < budget) {
        load_best();
        if (!grow()) break;
        if (anneal(ITERS, T_HI)) save_best();
    }
    output_best();
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
#         q+1 lines through P. Every line holds <= s points of SA.
# B-side: a set SB of lines. Each j in SB gets a new vertex joined to all
#         q+1 points on j. Every point lies on <= s lines of SB.
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
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
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
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is optimal for D = 2. Safe fallback otherwise.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Arc-extended projective plane graphs (diameter 3, so valid for D >= 3).
    if D >= 3:
        cands = _arc_extensions(d, t_start + 0.1 * time_limit,
                                random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c <= best[0]:
                break
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Bipartite vertex-insertion annealing in C, started from the best graph so far.
    if D >= 3 and d >= 2:
        spent = time.monotonic() - t_start
        budget = min(0.8 * time_limit, time_limit - spent - 8.0)
        if d <= 4:
            budget = min(budget, 3.0)
        if budget >= 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=best, timeout=budget + 5.0)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
