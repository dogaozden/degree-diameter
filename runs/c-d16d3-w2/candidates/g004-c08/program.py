import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: greedy vertex insertion with ball-cover certificates.
#
# Let R = D-1. A new vertex w joined to a set N of vertices on the opposite
# colour class is within distance D of every old vertex x whenever x lies in
# the R-ball of some u in N. Adding a vertex never increases distances between
# old vertices, so the graph stays valid. The engine repeats:
#   1. compute R-balls as bitsets,
#   2. for each colour class, greedily cover all vertices with spare-degree
#      neighbours (randomized tie-breaks), and insert a vertex on success,
#   3. on failure add a random spare cross edge to change the spare pattern.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4096
#define MAXD 64
#define MAXW (MAXN / 64)

static int n, d, D, W;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static int popc(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void compute_balls(int R) {
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) reach[v][w] = 0;
        reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = reach[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= reach[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) reach[v][w] = nxt[v][w];
    }
}

static int covers_all(const uint64_t *cov) {
    for (int w = 0; w < W; w++) {
        uint64_t want;
        if (w < W - 1) {
            want = ~0ULL;
        } else {
            int r = n - 64 * (W - 1);
            want = (r >= 64) ? ~0ULL : ((1ULL << r) - 1);
        }
        if ((cov[w] & want) != want) return 0;
    }
    return 1;
}

static int try_insert(int side) {
    int cand[MAXN];
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (col[u] == 1 - side && deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = (int)(rnd() % (uint32_t)(i + 1));
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    static int used[MAXN];
    for (int i = 0; i < n; i++) used[i] = 0;
    uint64_t cov[MAXW];
    for (int w = 0; w < W; w++) cov[w] = 0;
    int chosen[MAXD];
    int nch = 0;
    while (nch < d && !covers_all(cov)) {
        int best = -1, bg = 0;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (used[u]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(reach[u][w] & ~cov[w]);
            if (g > bg) { bg = g; best = u; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) cov[w] |= reach[best][w];
    }
    if (!covers_all(cov)) return 0;
    int w = n;
    n++;
    col[w] = side;
    deg[w] = 0;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], w);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2) { printf("0 0\n"); return 0; }
    if (N0 < 1 || N0 > MAXN) { printf("0 0\n"); return 0; }
    n = N0;
    W = (n + 63) >> 6;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    static int queue[MAXN];
    for (int s = 0; s < n; s++) col[s] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    queue[qt++] = v;
                }
            }
        }
    }

    clock_t t0 = clock();
    int fails = 0;
    const int maxfails = 200;
    while (fails < maxfails && n < MAXN) {
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        W = (n + 63) >> 6;
        compute_balls(D - 1);
        int sides[2] = {0, 1};
        if (rnd() & 1u) { sides[0] = 1; sides[1] = 0; }
        int ok = 0;
        for (int k = 0; k < 2 && !ok; k++) ok = try_insert(sides[k]);
        if (ok) { fails = 0; continue; }
        fails++;
        for (int t = 0; t < 50; t++) {
            int u = (int)(rnd() % (uint32_t)n);
            int v = (int)(rnd() % (uint32_t)n);
            if (u == v || col[u] == col[v]) continue;
            if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
            add_edge(u, v);
            break;
        }
    }

    int m2 = 0;
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) m2++;
    printf("%d %d\n", n, m2);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) printf("%d %d\n", u, adj[u][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2 (new): load-bounded set search by iterated local search.
#
# Problem: elements 0..ne-1 each hit a list of targets; choose the largest set
# S of elements such that every target is hit at most s times. For PG(2,q)
# with s = d-q-1 this is the choice of point-vertices (or line-vertices) that
# can receive one extra neighbour vertex each.
#
# Move: insert a random non-member, then for each target now over its limit,
# evict random other members that hit it. Accept if the size does not drop,
# sometimes accept a drop of one, and keep the best set seen.
#
# Input (stdin): graph "n m" with edges (x, ne+t), x < ne. Arguments:
#   s seed budget ne [initial elements...]
# Output: "k k" then k lines "x 0" for the chosen elements.
# ----------------------------------------------------------------------------

SET_SEARCH_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXV 2048
#define MAXDEG 256

static int ne, nt, s;
static int ed[MAXV], et[MAXV][MAXDEG];
static int td[MAXV], te[MAXV][MAXDEG];
static int inS[MAXV], load[MAXV];
static int bIn[MAXV], bLoad[MAXV], bestS[MAXV];
static int mem[MAXV];
static uint64_t rs = 88172645463325252ULL;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static int size_of(void) {
    int c = 0;
    for (int i = 0; i < ne; i++) c += inS[i];
    return c;
}

static void add_el(int x) {
    inS[x] = 1;
    for (int i = 0; i < ed[x]; i++) load[et[x][i]]++;
}

static void rem_el(int x) {
    inS[x] = 0;
    for (int i = 0; i < ed[x]; i++) load[et[x][i]]--;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    s = atoi(argv[1]);
    unsigned long seed = strtoul(argv[2], NULL, 10);
    double budget = atof(argv[3]);
    int ne_arg = atoi(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;

    int n, m;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    ne = ne_arg;
    nt = n - ne;
    if (s < 1 || ne < 1 || nt < 1 || n > MAXV) { printf("0 0\n"); return 0; }

    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u > v) { int t = u; u = v; v = t; }
        if (u < 0 || u >= ne || v < ne || v >= n) continue;
        int t = v - ne;
        if (ed[u] >= MAXDEG || td[t] >= MAXDEG) continue;
        et[u][ed[u]++] = t;
        te[t][td[t]++] = u;
    }

    for (int i = 5; i < argc; i++) {
        int x = atoi(argv[i]);
        if (x < 0 || x >= ne || inS[x]) continue;
        int ok = 1;
        for (int j = 0; j < ed[x]; j++)
            if (load[et[x][j]] >= s) { ok = 0; break; }
        if (ok) add_el(x);
    }

    int cur = size_of();
    int best = cur;
    memcpy(bestS, inS, sizeof(inS));

    clock_t t0 = clock();
    long iter = 0;
    while (1) {
        if ((iter & 15) == 0 &&
            (double)(clock() - t0) / CLOCKS_PER_SEC > budget)
            break;
        iter++;

        int x = -1;
        for (int tries = 0; tries < 64 && x < 0; tries++) {
            int c = (int)(rnd() % (uint32_t)ne);
            if (!inS[c]) x = c;
        }
        if (x < 0) continue;

        memcpy(bIn, inS, sizeof(inS));
        memcpy(bLoad, load, sizeof(load));
        add_el(x);

        int bad = 0;
        for (int j = 0; j < ed[x] && !bad; j++) {
            int t = et[x][j];
            while (load[t] > s) {
                int cnt = 0;
                for (int k = 0; k < td[t]; k++) {
                    int y = te[t][k];
                    if (inS[y] && y != x) mem[cnt++] = y;
                }
                if (cnt == 0) { bad = 1; break; }
                int y = mem[rnd() % (uint32_t)cnt];
                rem_el(y);
            }
        }

        int ns = size_of();
        int acc = 0;
        if (!bad) {
            if (ns >= cur) acc = 1;
            else if (ns == cur - 1 && rnd() % 6 == 0) acc = 1;
            else if (ns < cur - 1 && rnd() % 200 == 0) acc = 1;
        }
        if (!acc) {
            memcpy(inS, bIn, sizeof(inS));
            memcpy(load, bLoad, sizeof(load));
        } else {
            cur = ns;
        }
        if (cur > best) {
            best = cur;
            memcpy(bestS, inS, sizeof(inS));
        }
    }

    printf("%d %d\n", best, best);
    for (int i = 0; i < ne; i++)
        if (bestS[i]) printf("%d 0\n", i);
    return 0;
}
"""


def _c_augment(graph, d, D, seed, budget):
    """Run the C insertion engine on graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 0.5 or d > 64:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 5.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Projective-plane based diameter-3 graphs with extra vertices.
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1), degree q+1.
# With s = d - q - 1 spare degrees on every old vertex:
#   A-side: a set SA of points; each P in SA gets a new vertex joined to the
#           q+1 lines through P. Every line may be hit at most s times.
#   B-side: a set SB of lines; each j in SB gets a new vertex joined to the
#           q+1 points on j. Every point may be hit at most s times.
# The two sides are independent. Each side is a load-bounded set problem, and
# it is solved by the C iterated local search (SET_SEARCH_C), seeded by the
# conic and by randomized greedy.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by at most s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice of elements so that every target is hit at most s times."""
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


def _conic_set(q, pts, F):
    """Conic (plus nucleus for even q) as an index set: an arc, so loads are at most 1 per line."""
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _set_search(rows, nt, s, seed, budget, init):
    """Largest load-bounded element set found by the C local search; falls back to init."""
    ne = len(rows)
    init = list(init)
    if s < 1 or ne == 0 or budget < 0.2:
        return init
    edges = [(x, ne + t) for x, ts in enumerate(rows) for t in ts]
    args = [s, seed & 0x7FFFFFFF, round(budget, 2), ne] + init
    try:
        out = lib.run_c(SET_SEARCH_C, args, stdin_graph=(ne + nt, edges),
                        timeout=budget + 5.0)
        _, e = lib.parse_graph_text(out)
    except Exception:
        return init
    chosen = sorted({u for u, _ in e})
    if len(chosen) >= len(init) and _loads_ok(chosen, s, nt, rows):
        return chosen
    return init


def _best_side(rows, m, s, rng, conic, budget, seed):
    """Choose one side's set: best of conic and greedy as the start, then C local search."""
    init = []
    if conic and _loads_ok(conic, s, m, rows):
        init = list(conic)
    g = _greedy_side(m, s, rows, rng, 20, time.monotonic() + 0.2 * budget)
    if len(g) > len(init) and _loads_ok(g, s, m, rows):
        init = g
    return _set_search(rows, m, s, seed, budget, init)


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


def _arc_candidates(d, deadline, seed):
    """Return valid (n, edges) candidates from PG(2, q) extensions, best upper bounds first."""
    jobs = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 0:
            continue
        m = q * q + q + 1
        ub = 2 * m + 2 * ((s * m) // (q + 1))  # each element hits q+1 targets, load <= s
        jobs.append((ub, q, s))
    jobs.sort(reverse=True)

    rng = random.Random(seed * 7919 + d)
    out = []
    best_n = 0
    for idx, (ub, q, s) in enumerate(jobs):
        if ub <= best_n or time.monotonic() > deadline:
            continue
        m, edges, point_lines, line_points = _pg_data(q)
        pts = lib.projective_points(q)
        F = lib.GF(q)
        conic = _conic_set(q, pts, F)
        left = max(1, len(jobs) - idx)
        rem = deadline - time.monotonic()
        per_side = max(0.2, rem / (2 * left))
        SA = _best_side(point_lines, m, s, rng, conic, per_side, seed + 1)
        SB = _best_side(line_points, m, s, rng, conic, per_side, seed + 2)
        n, E = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        if lib.is_valid(n, E, d, 3):
            out.append((n, E))
            best_n = max(best_n, n)
    return out


# ----------------------------------------------------------------------------
# Driver.
#   D == 1: K2.   D == 2: K_{d,d}.
#   D == 3: PG(2,q)-based extensions (C local search on load-bounded sets),
#           then C greedy insertion on the best graph.
#   D >= 4: C greedy insertion starting from K_{d,d}.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def elapsed():
        return time.monotonic() - start

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        for g in _arc_candidates(d, start + 0.5 * time_limit, seed):
            consider(g)

    rem = 0.78 * time_limit - elapsed()
    if rem > 1.0:
        consider(_c_augment(best, d, D, seed, rem))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
