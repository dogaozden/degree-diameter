import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: grow-and-repair annealing for bipartite graphs with diameter <= D.
#
# State: a valid bipartite graph with max degree d. Cost = number of ordered
# vertex pairs at distance > D (computed with bitset balls of radius D).
# Moves: add an edge (always cost-non-increasing), rewire one endpoint of an
# edge to another vertex on the same side, or remove an edge. Annealing accepts
# uphill moves with Boltzmann probability. When cost reaches 0 the current graph
# is saved and one new vertex is appended (on a random side, attached to random
# spare-degree vertices of the opposite side). If repair stalls, the best saved
# graph is restored and growth is retried with new random choices.
# Every saved state has cost 0, so the output is always valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 704
#define WORDS 11
#define DMAX 64
#define STALL 60000

static int n, d, D, W;
static int side[NMAX], deg[NMAX], nb[NMAX][DMAX];
static unsigned char adjm[NMAX][NMAX];
static uint64_t bufA[NMAX][WORDS], bufB[NMAX][WORDS];
static uint64_t rs;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int a, int b) {
    adjm[a][b] = adjm[b][a] = 1;
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void drop(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (nb[a][i] == b) { nb[a][i] = nb[a][--deg[a]]; return; }
}

static void rem_edge(int a, int b) {
    adjm[a][b] = adjm[b][a] = 0;
    drop(a, b);
    drop(b, a);
}

/* Ordered pairs (v, w) with dist(v, w) > D. Zero means valid. */
static long cost_eval(void) {
    uint64_t (*cur)[WORDS] = bufA, (*nxt)[WORDS] = bufB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = nb[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[WORDS] = cur;
        cur = nxt;
        nxt = t;
    }
    long c = 0;
    for (int v = 0; v < n; v++) {
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += popc(cur[v][w]);
        c += n - cnt;
    }
    return c;
}

static int bn = -1;
static int bm = 0;
static int bE[2 * (NMAX * DMAX / 2) + 8];

static void save_best(void) {
    bn = n;
    bm = 0;
    for (int a = 0; a < n; a++)
        for (int i = 0; i < deg[a]; i++) {
            int b = nb[a][i];
            if (a < b) {
                bE[2 * bm] = a;
                bE[2 * bm + 1] = b;
                bm++;
            }
        }
}

static void load_best(void) {
    for (int a = 0; a < n; a++) {
        memset(adjm[a], 0, sizeof(adjm[a]));
        deg[a] = 0;
    }
    n = bn;
    W = (n + 63) / 64;
    for (int i = 0; i < bm; i++) add_edge(bE[2 * i], bE[2 * i + 1]);
}

static void grow(void) {
    int v = n;
    n++;
    W = (n + 63) / 64;
    side[v] = rndint(2);
    deg[v] = 0;
    int cand[NMAX], nc = 0;
    for (int u = 0; u < v; u++)
        if (side[u] != side[v] && deg[u] < d) cand[nc++] = u;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    for (int i = 0; i < nc && deg[v] < d; i++) add_edge(v, cand[i]);
}

static int sample_side(int s) {
    for (int t = 0; t < 40; t++) {
        int z = rndint(n);
        if (side[z] == s) return z;
    }
    return -1;
}

static void print_best(void) {
    printf("%d %d\n", bn, bm);
    for (int i = 0; i < bm; i++) printf("%d %d\n", bE[2 * i], bE[2 * i + 1]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    clock_t t0 = clock();

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || n0 > NMAX - 80 || d < 1 || d > DMAX || D < 1) {
        printf("0 0\n");
        return 0;
    }
    n = n0;
    W = (n + 63) / 64;
    for (int i = 0; i < m0; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a < 0 || b < 0 || a >= n || b >= n || a == b || adjm[a][b]) continue;
        if (deg[a] >= d || deg[b] >= d) continue;
        add_edge(a, b);
    }

    /* Bipartition by BFS; a conflict means the input is not bipartite. */
    static int color[NMAX], qu[NMAX];
    for (int i = 0; i < n; i++) color[i] = -1;
    for (int s = 0; s < n; s++) {
        if (color[s] >= 0) continue;
        color[s] = 0;
        int h = 0, t = 0;
        qu[t++] = s;
        while (h < t) {
            int u = qu[h++];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (color[v] < 0) {
                    color[v] = 1 - color[u];
                    qu[t++] = v;
                } else if (color[v] == color[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    for (int i = 0; i < n; i++) side[i] = color[i];

    long cur = cost_eval();
    if (cur == 0 && n > bn) save_best();

    double T = 1.5;
    int stall = 0;
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < tl) {
        if (cur == 0) {
            if (n > bn) save_best();
            if (n >= NMAX - 1) break;
            grow();
            cur = cost_eval();
            stall = 0;
            continue;
        }
        stall++;
        if (stall > STALL) {
            load_best();
            cur = cost_eval();
            stall = 0;
            continue;
        }

        int mv = rndint(100);
        if (mv < 25) {
            /* Add an edge: never increases the cost. */
            int a = sample_side(0), b = sample_side(1);
            if (a < 0 || b < 0 || deg[a] >= d || deg[b] >= d || adjm[a][b]) continue;
            add_edge(a, b);
            cur = cost_eval();
        } else if (mv < 90) {
            /* Rewire: keep one endpoint of an edge, move the other to a new vertex on its side. */
            int x = rndint(n);
            if (deg[x] == 0) continue;
            int y = nb[x][rndint(deg[x])];
            int keep, other;
            if (rndint(2)) { keep = x; other = y; } else { keep = y; other = x; }
            int z = -1;
            for (int t = 0; t < 40; t++) {
                int c = rndint(n);
                if (side[c] == side[other] && c != other && !adjm[keep][c] && deg[c] < d) {
                    z = c;
                    break;
                }
            }
            if (z < 0) continue;
            rem_edge(keep, other);
            add_edge(keep, z);
            long c2 = cost_eval();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                rem_edge(keep, z);
                add_edge(keep, other);
            }
        } else {
            /* Remove an edge, accepted by the annealing rule. */
            int x = rndint(n);
            if (deg[x] == 0) continue;
            int y = nb[x][rndint(deg[x])];
            rem_edge(x, y);
            long c2 = cost_eval();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                add_edge(x, y);
            }
        }
    }

    if (bn < 0) {
        printf("0 0\n");
        return 0;
    }
    print_best();
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
#
# Order is 2(q^2+q+1) + |SA| + |SB|. The C engine then tries to append further
# vertices and repair the diameter by edge moves.
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
    """True if every target t is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements so that every target is hit by <= s chosen elements."""
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
# Build: best algebraic start, then C grow-and-repair search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_begin = time.monotonic()
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

    if D >= 3:
        # PG(2, d-1) when d-1 is a prime power: already optimal for diameter 3.
        if lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
        rng = random.Random(seed * 7919 + d)
        for n_c, e_c in _arc_extensions(d, t_begin + 0.25 * time_limit, rng):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # C grow-and-repair search, started from the best valid graph found so far.
    remaining = time_limit * 0.85 - (time.monotonic() - t_begin) - 1.0
    if remaining >= 1.0 and best_n <= 600 and d <= 60:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                            stdin_graph=best, timeout=remaining + 10.0)
            n_c, e_c = lib.parse_graph_text(out)
            consider(n_c, e_c)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
