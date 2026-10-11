"""Diameter-D bipartite search: arc-extended projective plane starts plus a C
grow-and-repair annealer.

Each start is a valid graph (arc-extended PG(2,q) incidence, the generalized quadrangle
for D >= 4, or K_{d,d}). The C engine works on a bipartite graph with a fixed side
assignment and keeps a count of bad ordered pairs (pairs at distance > D). Two kinds of
moves are used:

  * grow: add a vertex on one side, joined to up to d spare vertices of the other side
    chosen by greedy set cover of the ball of radius D-1, so it starts with few bad pairs;
  * repair: simulated annealing over edge additions and degree-preserving 2-switches that
    minimises the bad-pair count.

Whenever the bad-pair count reaches zero, the graph is saved as the best valid graph and
the engine grows it again. After a long stall it restarts from the best saved graph.
Python re-checks the result with lib.is_valid and falls back to the start graph otherwise.
"""
import itertools
import random
import time

import lib

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define WORDS (MAXN / 64)
#define MAXDEG 64
#define MAXE (MAXN * MAXDEG / 2)
#define STALL 40000

typedef uint64_t Row[WORDS];

static int N, Dd, Dr, W;
static int deg[MAXN], side[MAXN];
static int adj[MAXN][MAXDEG];
static unsigned char A[MAXN][MAXN];
static Row RA[MAXN], RB[MAXN];
static int cand[MAXN];
static uint64_t rs = 88172645463325252ULL;

static int bestN = -1;
static int bestSide[MAXN];
static int bestM = 0;
static int bestEA[MAXE], bestEB[MAXE];

static int mv_type = 0, ua1 = 0, ub1 = 0, ua2 = 0, ub2 = 0;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double unif(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int a, int b) {
    A[a][b] = A[b][a] = 1;
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void unlink_one(int v, int u) {
    for (int k = 0; k < deg[v]; k++) {
        if (adj[v][k] == u) {
            adj[v][k] = adj[v][--deg[v]];
            return;
        }
    }
}

static void del_edge(int a, int b) {
    A[a][b] = A[b][a] = 0;
    unlink_one(a, b);
    unlink_one(b, a);
}

/* Bitsets of vertices within `steps` of each vertex. Returns RA or RB. */
static Row *reach_steps(int steps) {
    W = (N + 63) / 64;
    Row *cur = RA, *nxt = RB;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < steps; s++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = cur[adj[v][k]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        Row *t = cur;
        cur = nxt;
        nxt = t;
    }
    return cur;
}

/* Number of ordered pairs at distance > Dr. */
static long eval_bad(void) {
    Row *R = reach_steps(Dr);
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(R[v][w]);
        bad += N - c;
    }
    return bad;
}

static int pick_side(int X) {
    for (int t = 0; t < 200; t++) {
        int v = rndint(N);
        if (side[v] == X && deg[v] > 0) return v;
    }
    return -1;
}

/* Apply a random move. Returns 0 if no move was made. */
static int propose(void) {
    if (unif() < 0.15) {
        int a = -1, b = -1;
        for (int t = 0; t < 40; t++) {
            int x = rndint(N);
            if (side[x] != 0 || deg[x] >= Dd) continue;
            int y = rndint(N);
            if (side[y] != 1 || deg[y] >= Dd || A[x][y]) continue;
            a = x;
            b = y;
            break;
        }
        if (a >= 0) {
            mv_type = 0;
            ua1 = a;
            ub1 = b;
            add_edge(a, b);
            return 1;
        }
    }
    int a1 = pick_side(0), a2 = pick_side(0);
    if (a1 < 0 || a2 < 0 || a1 == a2) return 0;
    int b1 = adj[a1][rndint(deg[a1])];
    int b2 = adj[a2][rndint(deg[a2])];
    if (b1 == b2 || A[a1][b2] || A[a2][b1]) return 0;
    del_edge(a1, b1);
    del_edge(a2, b2);
    add_edge(a1, b2);
    add_edge(a2, b1);
    mv_type = 1;
    ua1 = a1;
    ub1 = b1;
    ua2 = a2;
    ub2 = b2;
    return 1;
}

static void undo(void) {
    if (mv_type == 0) {
        del_edge(ua1, ub1);
    } else {
        del_edge(ua1, ub2);
        del_edge(ua2, ub1);
        add_edge(ua1, ub1);
        add_edge(ua2, ub2);
    }
}

/* Add one vertex on a side, joined to up to Dd spare vertices of the other side, chosen by
   greedy cover of the radius-(Dr-1) balls. Returns 1 if the graph grew. */
static int grow(void) {
    if (N + 2 >= MAXN) return 0;
    int X0 = rndint(2);
    for (int z = 0; z < 2; z++) {
        int X = (z == 0) ? X0 : 1 - X0;
        int nc = 0;
        for (int v = 0; v < N; v++)
            if (side[v] != X && deg[v] < Dd) cand[nc++] = v;
        if (nc < 1) continue;
        Row *B = reach_steps(Dr - 1);
        uint64_t U[WORDS];
        for (int w = 0; w < W; w++) U[w] = ~0ULL;
        if (N & 63) U[W - 1] = (1ULL << (N & 63)) - 1ULL;
        char used[MAXN];
        memset(used, 0, sizeof(used));
        int nch = 0;
        int chosen[MAXDEG];
        while (nch < Dd) {
            int best = -1;
            long bs = -1;
            for (int i = 0; i < nc; i++) {
                int t = cand[i];
                if (used[t]) continue;
                long g = 0;
                for (int w = 0; w < W; w++) g += popc(B[t][w] & U[w]);
                if (g <= 0) continue;
                long sc = g * 8 + rndint(8);
                if (sc > bs) {
                    bs = sc;
                    best = t;
                }
            }
            if (best < 0) break;
            used[best] = 1;
            chosen[nch++] = best;
            for (int w = 0; w < W; w++) U[w] &= ~B[best][w];
        }
        if (nch == 0) continue;
        int x = N++;
        for (int u = 0; u < x; u++) A[x][u] = A[u][x] = 0;
        side[x] = X;
        deg[x] = 0;
        for (int i = 0; i < nch; i++) add_edge(x, chosen[i]);
        return 1;
    }
    return 0;
}

static void save_best(void) {
    bestN = N;
    bestM = 0;
    for (int v = 0; v < N; v++) bestSide[v] = side[v];
    for (int v = 0; v < N; v++) {
        if (side[v] != 0) continue;
        for (int k = 0; k < deg[v]; k++) {
            if (bestM < MAXE) {
                bestEA[bestM] = v;
                bestEB[bestM] = adj[v][k];
                bestM++;
            }
        }
    }
}

static void restore_best(void) {
    int oldN = N;
    for (int v = 0; v < oldN; v++) {
        memset(A[v], 0, sizeof(A[v]));
        deg[v] = 0;
    }
    N = bestN;
    for (int v = 0; v < N; v++) side[v] = bestSide[v];
    for (int i = 0; i < bestM; i++) add_edge(bestEA[i], bestEB[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    if (Dd > MAXDEG) Dd = MAXDEG;
    Dr = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 2 || Dr < 1 || Dd < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (A[u][v] || deg[u] >= Dd || deg[v] >= Dd) continue;
        add_edge(u, v);
    }

    /* Side assignment by BFS; the start must be bipartite. */
    static int q[MAXN];
    int ok = 1;
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int u = q[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    q[qt++] = v;
                } else if (side[v] == side[u]) {
                    ok = 0;
                }
            }
        }
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    long bad = eval_bad();
    if (bad == 0) save_best();

    double t_end = now() + budget;
    long stall = 0;
    while (now() < t_end) {
        if (bad == 0) {
            if (N > bestN) save_best();
            if (!grow()) {
                for (int i = 0; i < 3; i++) propose();
            }
            bad = eval_bad();
            stall = 0;
            continue;
        }
        if (!propose()) {
            stall++;
        } else {
            long nb = eval_bad();
            double T = 0.3 + 2.0 * (1.0 - (double)stall / STALL);
            if (T < 0.3) T = 0.3;
            long delta = nb - bad;
            if (delta <= 0 || unif() < exp(-(double)delta / T)) {
                bad = nb;
            } else {
                undo();
            }
            stall++;
        }
        if (stall > STALL) {
            if (bestN > 0) {
                restore_best();
                bad = eval_bad();
            }
            stall = 0;
        }
    }

    if (bestN < 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestEA[i], bestEB[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has spare capacity s = d - q - 1. Choose a point set S that is an arc, so each
# line holds at most s points of S. Add an A-vertex for each P in S (joined to
# lines through P) and a B-vertex for each j in S (joined to points on line j).
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
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4), used for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
# Build: best start, then the C grow-and-repair annealer.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.80 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))

    starts = []
    if D >= 3:
        starts.extend(_arc_extensions(d, t0 + 0.20 * time_limit, rng))
    if D >= 4 and time.monotonic() < t0 + 0.20 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    starts = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    if lib.is_valid(fallback[0], fallback[1], d, D):
        starts.append(fallback)
    if not starts:
        return 1, []
    best = max(starts, key=lambda g: g[0])

    remaining = hard_end - time.monotonic() - 1.0
    if remaining >= 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                             stdin_graph=best, timeout=remaining + 8.0)
            n1, e1 = lib.parse_graph_text(text)
            if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                best = (n1, e1)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
