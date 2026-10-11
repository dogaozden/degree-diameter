import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: insertion + annealing repair.
#
# State: a bipartite graph with max degree d and n vertices. cost = number of
# unordered vertex pairs at distance > D (bitset balls). Cost 0 means valid.
#
# Loop:
#   * cost 0: snapshot, then insert a vertex whose neighbourhood greedily covers
#     the radius-(D-1) balls (a new vertex w joined to N reaches x within D iff
#     some u in N has dist(u, x) <= D-1). Only partial covers are possible, so
#     the new vertex may start with cost > 0.
#   * cost > 0: anneal at fixed n. Moves: add a spare cross edge (biased to the
#     newest vertex) or a degree-preserving 2-switch. Metropolis acceptance.
#   * annealing fails: restore the snapshot and retry insertion with new random
#     choices.
# The output is the largest graph with cost 0 seen.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXW 16
#define DMAX 64
#define ANN_ITERS 1500

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][DMAX];
    int col[MAXN];
} State;

static State cur, best, snap;
static int dd, DD, cap;
static double t0, t_end;
static uint64_t rs;
static uint64_t RD[MAXN][MAXW], RR[MAXN][MAXW], BB[MAXN][MAXW];

static double wall(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(const State *s, int u, int v) {
    for (int i = 0; i < s->deg[u]; i++)
        if (s->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(State *s, int u, int v) {
    s->adj[u][s->deg[u]++] = v;
    s->adj[v][s->deg[v]++] = u;
}

static void del_arc(State *s, int u, int v) {
    for (int i = 0; i < s->deg[u]; i++) {
        if (s->adj[u][i] == v) {
            s->adj[u][i] = s->adj[u][--s->deg[u]];
            return;
        }
    }
}

static void remove_edge(State *s, int u, int v) {
    del_arc(s, u, v);
    del_arc(s, v, u);
}

static int moore(int d, int D) {
    if (d == 1) return 2;
    if (d == 2) return 2 * D;
    double s = 0, p = 1;
    for (int i = 0; i < D; i++) { s += p; p *= (d - 1); }
    double b = 2 * s;
    if (b > MAXN) return MAXN;
    return (int)b;
}

/* out[v] = bitset of vertices within distance R of v. */
static void balls(const State *s, int R, uint64_t out[][MAXW]) {
    int n = s->n, W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) out[v][w] = 0;
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) BB[v][w] = out[v][w];
            for (int i = 0; i < s->deg[v]; i++) {
                int u = s->adj[v][i];
                for (int w = 0; w < W; w++) BB[v][w] |= out[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) out[v][w] = BB[v][w];
    }
}

static long long bad_pairs(const State *s) {
    int n = s->n, W = (n + 63) / 64;
    balls(s, DD, RD);
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(RD[v][w]);
        tot += n - c;
    }
    return tot / 2;
}

static int colour_graph(State *s) {
    static int stk[MAXN];
    int n = s->n;
    for (int v = 0; v < n; v++) s->col[v] = -1;
    for (int src = 0; src < n; src++) {
        if (s->col[src] >= 0) continue;
        s->col[src] = 0;
        int sp = 0;
        stk[sp++] = src;
        while (sp > 0) {
            int u = stk[--sp];
            for (int i = 0; i < s->deg[u]; i++) {
                int v = s->adj[u][i];
                if (s->col[v] < 0) {
                    s->col[v] = 1 - s->col[u];
                    stk[sp++] = v;
                } else if (s->col[v] == s->col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Insert a vertex on a random side with a greedy cover of radius-(D-1) balls. */
static int insert_vertex(void) {
    int n = cur.n, W = (n + 63) / 64;
    int side = rndint(2);
    balls(&cur, DD - 1, RR);
    int cand[MAXN], nc = 0;
    for (int u = 0; u < n; u++)
        if (cur.col[u] == 1 - side && cur.deg[u] < dd) cand[nc++] = u;
    uint64_t cov[MAXW];
    for (int w = 0; w < W; w++) cov[w] = 0;
    int chosen[DMAX], nch = 0;
    while (nch < dd && nc > 0) {
        int bestg = 0, bu = -1;
        int off = rndint(nc);
        for (int k = 0; k < nc; k++) {
            int u = cand[(k + off) % nc];
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(RR[u][w] & ~cov[w]);
            if (g > bestg) { bestg = g; bu = u; }
        }
        if (bu < 0) break;
        chosen[nch++] = bu;
        for (int w = 0; w < W; w++) cov[w] |= RR[bu][w];
    }
    if (nch == 0) return 0;
    int w = n;
    cur.n = n + 1;
    cur.deg[w] = 0;
    cur.col[w] = side;
    for (int i = 0; i < nch; i++) add_edge(&cur, chosen[i], w);
    return 1;
}

/* Metropolis annealing at fixed n. Returns the final cost. */
static long long anneal(int iters, long long c) {
    static int L0[MAXN], S0[MAXN], S1[MAXN];
    for (int it = 0; it < iters && c > 0; it++) {
        if (wall() - t0 >= t_end) break;
        double T = 1.0 * (1.0 - (double)it / iters) + 0.05;
        int n = cur.n, n0 = 0, s0 = 0, s1 = 0;
        for (int v = 0; v < n; v++) {
            if (cur.col[v] == 0) L0[n0++] = v;
            if (cur.deg[v] < dd) {
                if (cur.col[v] == 0) S0[s0++] = v;
                else S1[s1++] = v;
            }
        }
        if (s0 > 0 && s1 > 0 && rnd01() < 0.4) {
            int u, v;
            if (rnd01() < 0.5 && cur.deg[n - 1] < dd) {
                u = n - 1;
                if (cur.col[u] == 0) {
                    if (s1 == 0) continue;
                    v = S1[rndint(s1)];
                } else {
                    if (s0 == 0) continue;
                    v = S0[rndint(s0)];
                }
            } else {
                u = S0[rndint(s0)];
                v = S1[rndint(s1)];
            }
            if (!has_edge(&cur, u, v)) {
                add_edge(&cur, u, v);
                c = bad_pairs(&cur);
            }
            continue;
        }
        if (n0 < 2) continue;
        int a = L0[rndint(n0)], a2 = L0[rndint(n0)];
        if (a == a2 || cur.deg[a] == 0 || cur.deg[a2] == 0) continue;
        int b = cur.adj[a][rndint(cur.deg[a])];
        int e = cur.adj[a2][rndint(cur.deg[a2])];
        if (b == e || has_edge(&cur, a, e) || has_edge(&cur, a2, b)) continue;
        remove_edge(&cur, a, b);
        remove_edge(&cur, a2, e);
        add_edge(&cur, a, e);
        add_edge(&cur, a2, b);
        long long nc = bad_pairs(&cur);
        if (nc <= c || rnd01() < exp(-(double)(nc - c) / T)) {
            c = nc;
        } else {
            remove_edge(&cur, a, e);
            remove_edge(&cur, a2, b);
            add_edge(&cur, a, b);
            add_edge(&cur, a2, e);
        }
    }
    return c;
}

static void print_state(const State *s) {
    long long m = 0;
    for (int v = 0; v < s->n; v++) m += s->deg[v];
    m /= 2;
    printf("%d %lld\n", s->n, m);
    for (int u = 0; u < s->n; u++)
        for (int i = 0; i < s->deg[u]; i++) {
            int v = s->adj[u][i];
            if (u < v) printf("%d %d\n", u, v);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit\n");
        return 1;
    }
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    t0 = wall();
    t_end = tl - 0.3;
    if (t_end < 0.2) t_end = 0.2;

    if (dd < 2 || DD < 2 || dd > DMAX) {
        if (dd >= 1 && DD >= 1) printf("2 1\n0 1\n");
        else printf("1 0\n");
        return 0;
    }
    cap = moore(dd, DD);

    int n0 = 0, m0 = 0, have = 0;
    memset(&cur, 0, sizeof cur);
    if (scanf("%d %d", &n0, &m0) == 2 && n0 >= 1 && n0 <= MAXN && m0 >= 0) {
        cur.n = n0;
        have = 1;
        for (int i = 0; i < m0 && have; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { have = 0; break; }
            if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v ||
                cur.deg[u] >= dd || cur.deg[v] >= dd || has_edge(&cur, u, v)) {
                have = 0;
                break;
            }
            add_edge(&cur, u, v);
        }
    }
    if (have) {
        have = colour_graph(&cur) && cur.n <= cap && bad_pairs(&cur) == 0;
    }
    if (!have) {
        memset(&cur, 0, sizeof cur);
        cur.n = 2 * dd;
        for (int v = 0; v < cur.n; v++) cur.col[v] = (v < dd) ? 0 : 1;
        for (int a = 0; a < dd; a++)
            for (int b = 0; b < dd; b++)
                add_edge(&cur, a, dd + b);
    }

    best = cur;
    snap = cur;
    long long cc = 0;
    while (wall() - t0 < t_end) {
        if (cc == 0) {
            if (cur.n > best.n) best = cur;
            if (cur.n >= cap) break;
            snap = cur;
            if (!insert_vertex()) break;
            cc = bad_pairs(&cur);
        } else {
            cc = anneal(ANN_ITERS, cc);
            if (cc != 0) {
                cur = snap;
                cc = 0;
            }
        }
    }
    if (cc == 0 && cur.n > best.n) best = cur;
    print_state(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S
# with every line holding <= s points of S and every point on <= s lines of S.
# For each P in S add an A-vertex joined to the q+1 lines through P; for each
# j in S add a B-vertex joined to the q+1 points on line j.
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


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
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


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
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
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
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
# Build: arc-extended starts (and GQ for D >= 4), then the C insertion/annealing
# engine improves the best start within the remaining time.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = g

    if D >= 3:
        for g in _arc_extensions(d, start + 0.08 * time_limit, random.Random(seed * 7919 + d)):
            consider(g)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    budget = start + 0.9 * time_limit - 2.5 - time.monotonic()
    if 2 <= d <= 64 and budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                             stdin_graph=best, timeout=budget + 5.0)
            consider(lib.parse_graph_text(text))
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
