"""Diameter-3 bipartite search: arc-extended projective plane starts plus a C local search.

Starts are valid graphs: arc-extended PG(2,q) incidence graphs, the generalized quadrangle W(q)
for D >= 4, or K_{d,d}. The C engine runs one local search for most of the time budget. Its moves are:

  * growth: add one vertex on a random side, joined to a greedy set T of spare vertices on the
    other side. T is chosen by set cover of radius-(D-1) balls, with several randomized tries
    keeping the smallest T.
  * perturbation (new): delete a random vertex, repair by inserting up to two new vertices, and
    occasionally add spare edges between opposite sides. Deleting a vertex can break the diameter,
    so validity is re-checked globally. A vertex v is within distance D of everything iff the union
    of the radius-(D-1) balls of v and its neighbours covers all vertices. That check is cheap with
    bitsets.

A state is kept only if it is valid and has at least as many vertices as before. Plateau moves are
accepted, so the walk can drift. Python re-checks the final result with lib.is_valid.
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
#include <time.h>

#define MAXN 1024
#define WORDS (MAXN / 64)
#define MAXDEG 64

static int N, Dd, Dist, W;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static uint64_t ball[MAXN][WORDS];
static int mark[MAXN], lev[MAXN], bq[MAXN];
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void set_w(void) { W = (N + 63) / 64; }

/* Bitset of all vertices within distance r of src. */
static void ball_of(int src, int r, uint64_t *bits) {
    int head = 0, t = 0;
    stamp++;
    for (int i = 0; i < W; i++) bits[i] = 0;
    bq[t++] = src;
    mark[src] = stamp;
    lev[src] = 0;
    while (head < t) {
        int u = bq[head++];
        bits[u >> 6] |= 1ULL << (u & 63);
        if (lev[u] >= r) continue;
        for (int k = 0; k < deg[u]; k++) {
            int v = adj[u][k];
            if (mark[v] != stamp) {
                mark[v] = stamp;
                lev[v] = lev[u] + 1;
                bq[t++] = v;
            }
        }
    }
}

static void recompute_balls(void) {
    for (int v = 0; v < N; v++) ball_of(v, Dist - 1, ball[v]);
}

/* Diameter check: v and w are within D iff w is in ball(v, D-1) or in ball(u, D-1) for a neighbour u. */
static int full_ok(void) {
    uint64_t full[WORDS], acc[WORDS];
    for (int i = 0; i < W; i++) full[i] = ~0ULL;
    if (N & 63) full[W - 1] = (1ULL << (N & 63)) - 1ULL;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < W; i++) acc[i] = ball[v][i];
        for (int k = 0; k < deg[v]; k++) {
            int u = adj[v][k];
            for (int i = 0; i < W; i++) acc[i] |= ball[u][i];
        }
        for (int i = 0; i < W; i++)
            if (acc[i] != full[i]) return 0;
    }
    return 1;
}

/* Greedy cover plan for a new vertex on side X. Returns |T| or -1 if the cover fails. */
static int plan_add(int X, int *T) {
    uint64_t U[WORDS];
    int sel[MAXN];
    int nt = 0;
    for (int i = 0; i < W; i++) U[i] = ~0ULL;
    if (N & 63) U[W - 1] = (1ULL << (N & 63)) - 1ULL;
    memset(sel, 0, sizeof(int) * (size_t)N);
    while (nt < Dd) {
        int best = -1;
        long bestsc = -1;
        for (int v = 0; v < N; v++) {
            if (side[v] == X || deg[v] >= Dd || sel[v]) continue;
            int g = 0;
            for (int i = 0; i < W; i++) g += popc(ball[v][i] & U[i]);
            if (g <= 0) continue;
            long sc = (long)g * 16 + rndint(16);
            if (sc > bestsc) {
                bestsc = sc;
                best = v;
            }
        }
        if (best < 0) break;
        sel[best] = 1;
        T[nt++] = best;
        for (int i = 0; i < W; i++) U[i] &= ~ball[best][i];
    }
    for (int i = 0; i < W; i++)
        if (U[i]) return -1;
    if (nt == 0) return -1;
    return nt;
}

static void apply_add(int X, const int *T, int nt) {
    int x = N;
    side[x] = X;
    deg[x] = nt;
    for (int k = 0; k < nt; k++) {
        int t = T[k];
        adj[x][k] = t;
        adj[t][deg[t]++] = x;
    }
    N++;
    set_w();
}

/* Try to add one vertex on side X (best of several randomized covers). */
static int try_add(int X) {
    int bestT[MAXDEG], T[MAXDEG];
    int bestn = 1000;
    if (N + 1 >= MAXN) return 0;
    for (int rep = 0; rep < 3; rep++) {
        int nt = plan_add(X, T);
        if (nt > 0 && nt < bestn) {
            bestn = nt;
            memcpy(bestT, T, sizeof(int) * (size_t)nt);
        }
    }
    if (bestn == 1000) return 0;
    apply_add(X, bestT, bestn);
    return 1;
}

/* Delete vertex x; the last vertex takes its index. */
static void remove_vertex(int x) {
    for (int k = 0; k < deg[x]; k++) {
        int t = adj[x][k];
        for (int j = 0; j < deg[t]; j++)
            if (adj[t][j] == x) {
                adj[t][j] = adj[t][deg[t] - 1];
                deg[t]--;
                break;
            }
    }
    deg[x] = 0;
    int last = N - 1;
    if (x != last) {
        for (int k = 0; k < deg[last]; k++) {
            int t = adj[last][k];
            for (int j = 0; j < deg[t]; j++)
                if (adj[t][j] == last) {
                    adj[t][j] = x;
                    break;
                }
        }
        memcpy(adj[x], adj[last], sizeof(int) * MAXDEG);
        deg[x] = deg[last];
        side[x] = side[last];
    }
    deg[last] = 0;
    N--;
    set_w();
}

/* Add random edges between spare vertices on opposite sides (always keeps validity). */
static int add_spare_edges(void) {
    int added = 0;
    for (int it = 0; it < 4 * N; it++) {
        int a = rndint(N), b = rndint(N);
        if (a == b || side[a] == side[b] || deg[a] >= Dd || deg[b] >= Dd) continue;
        int dup = 0;
        for (int k = 0; k < deg[a]; k++)
            if (adj[a][k] == b) {
                dup = 1;
                break;
            }
        if (dup) continue;
        adj[a][deg[a]++] = b;
        adj[b][deg[b]++] = a;
        added++;
    }
    return added;
}

static int sN;
static int sdeg[MAXN], sside[MAXN];
static int sadj[MAXN][MAXDEG];

static void snap(void) {
    sN = N;
    memcpy(sdeg, deg, sizeof(int) * (size_t)N);
    memcpy(sside, side, sizeof(int) * (size_t)N);
    memcpy(sadj, adj, sizeof(adj[0]) * (size_t)N);
}

static void restore(void) {
    N = sN;
    memcpy(deg, sdeg, sizeof(int) * (size_t)N);
    memcpy(side, sside, sizeof(int) * (size_t)N);
    memcpy(adj, sadj, sizeof(adj[0]) * (size_t)N);
    set_w();
    recompute_balls();
}

static void output(void) {
    int M = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) M++;
    printf("%d %d\n", N, M);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) printf("%d %d\n", v, adj[v][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    if (Dd > MAXDEG) Dd = MAXDEG;
    Dist = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 2 || Dist < 1 || Dd < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= Dd || deg[v] >= Dd) continue;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }

    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, t = 0;
        bq[t++] = s;
        while (head < t) {
            int u = bq[head++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    bq[t++] = v;
                }
            }
        }
    }

    set_w();
    recompute_balls();
    if (!full_ok()) {
        output();
        return 0;
    }

    double t_end = elapsed() + budget;
    while (elapsed() < t_end) {
        snap();
        int oldN = N;
        if (rndint(100) < 45) {
            int X = rndint(2);
            if (!try_add(X)) try_add(1 - X);
        } else {
            int x = rndint(N);
            remove_vertex(x);
            recompute_balls();
            int got = 0;
            for (int a = 0; a < 6 && got < 2; a++)
                if (try_add(rndint(2))) got++;
        }
        if (rndint(100) < 15) add_spare_edges();
        set_w();
        recompute_balls();
        if (!full_ok()) {
            restore();
            continue;
        }
        if (N < oldN) restore();
    }

    output();
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
# C search driver.
# ----------------------------------------------------------------------------

def _augment(n0, e0, d, D, seed, budget, timeout):
    """Run the C engine from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=timeout)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 88% of time_limit."""
    t0 = time.monotonic()
    deadline = t0 + 0.88 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))

    starts = []
    if D >= 3:
        starts.extend(_arc_extensions(d, t0 + 0.2 * time_limit, rng))
    if D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    starts = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    if lib.is_valid(fallback[0], fallback[1], d, D):
        starts.append(fallback)
    if not starts:
        return 1, []
    best = max(starts, key=lambda g: g[0])

    # One long local search from the largest start, using most of the remaining time.
    rem = deadline - time.monotonic()
    if rem > 3.0:
        budget = rem - 2.5
        try:
            n1, e1 = _augment(best[0], best[1], d, D, seed * 31 + 1,
                              max(0.5, budget), rem + 3.0)
            if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                best = (n1, e1)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
