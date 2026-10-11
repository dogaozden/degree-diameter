import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: growth by simulated annealing on bipartite graphs.
#
# State: bipartite graph with max degree d, sides 0/1 (from BFS colouring),
# diameter target D. Cost = number of vertex pairs at distance > D.
# Moves: degree-preserving bipartite double-edge swaps (SA), then greedy
# edge fill (edge addition never increases cost). Growth: add one vertex on a
# random side, wire it to d opposite vertices (spare ones first, otherwise
# steal an edge), fill greedily, then anneal back to cost 0. Every cost-0
# state is saved, so the output is always a valid graph with diameter <= D.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXW 18
#define MAXDEG 64
#define SESSION 3000

static int d, DD, n, W;
static int side[MAXN];
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static unsigned char has[MAXN][MAXN];
static uint64_t RB[2][MAXN][MAXW];

static int haveBest = 0;
static int bestN = 0;
static int bestDeg[MAXN];
static int bestSide[MAXN];
static int bestAdj[MAXN][MAXDEG];

static double budget = 10.0;
static clock_t t0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t xr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rnd(int m) { return (int)(xr() % (uint64_t)m); }
static double rnd01(void) { return (double)(xr() >> 11) * (1.0 / 9007199254740992.0); }
static int time_up(void) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC > budget;
}
static int pc64(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
    has[u][v] = has[v][u] = 1;
}

static void drop_nbr(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            deg[u]--;
            adj[u][i] = adj[u][deg[u]];
            return;
        }
    }
}

static void del_edge(int u, int v) {
    drop_nbr(u, v);
    drop_nbr(v, u);
    has[u][v] = has[v][u] = 0;
}

static void shuffle(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* Number of unordered pairs at distance > DD. */
static long long cost(void) {
    int cur = 0;
    for (int v = 0; v < n; v++) {
        memset(RB[0][v], 0, sizeof(uint64_t) * W);
        RB[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < DD; t++) {
        int nx = 1 - cur;
        for (int v = 0; v < n; v++) {
            uint64_t *dst = RB[nx][v];
            memcpy(dst, RB[cur][v], sizeof(uint64_t) * W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = RB[cur][adj[v][i]];
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        cur = nx;
    }
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(RB[cur][v][w]);
        tot += n - c;
    }
    return tot / 2;
}

/* Greedily add edges between spare vertices on opposite sides (never hurts). */
static void fill_greedy(void) {
    static int s0[MAXN], s1[MAXN];
    int a0 = 0, a1 = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d) {
            if (side[v] == 0) s0[a0++] = v; else s1[a1++] = v;
        }
    }
    shuffle(s0, a0);
    shuffle(s1, a1);
    for (int i = 0; i < a0; i++) {
        int a = s0[i];
        for (int j = 0; j < a1 && deg[a] < d; j++) {
            int b = s1[j];
            if (deg[b] < d && !has[a][b]) add_edge(a, b);
        }
    }
}

/* Add a new vertex with up to d neighbours on the opposite side. */
static void grow_vertex(void) {
    int x = n;
    n++;
    W = (n + 63) / 64;
    side[x] = rnd(2);
    deg[x] = 0;
    int o = 1 - side[x];
    static int cand[MAXN];
    int m = 0;
    for (int v = 0; v < x; v++) if (side[v] == o) cand[m++] = v;
    shuffle(cand, m);
    int k = 0;
    for (int i = 0; i < m && k < d; i++) {
        int w = cand[i];
        if (deg[w] < d) { add_edge(x, w); k++; }
    }
    for (int i = 0; i < m && k < d; i++) {
        int w = cand[i];
        if (deg[w] >= d && deg[w] > 0 && !has[x][w]) {
            int u = adj[w][rnd(deg[w])];
            del_edge(u, w);
            add_edge(x, w);
            k++;
        }
    }
}

static void save_best(void) {
    bestN = n;
    for (int v = 0; v < n; v++) {
        bestDeg[v] = deg[v];
        bestSide[v] = side[v];
        for (int i = 0; i < deg[v]; i++) bestAdj[v][i] = adj[v][i];
    }
    haveBest = 1;
}

static void load_best(void) {
    for (int v = 0; v < n; v++)
        for (int i = 0; i < deg[v]; i++) has[v][adj[v][i]] = 0;
    n = bestN;
    W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        deg[v] = bestDeg[v];
        side[v] = bestSide[v];
        for (int i = 0; i < deg[v]; i++) {
            adj[v][i] = bestAdj[v][i];
            has[v][adj[v][i]] = 1;
        }
    }
}

/* Pick a double-edge swap (a1,b1),(a2,b2) -> (a1,b2),(a2,b1) on valid sides. */
static int pick_swap(int *pa1, int *pb1, int *pa2, int *pb2) {
    for (int tr = 0; tr < 200; tr++) {
        int a1 = rnd(n), a2 = rnd(n);
        if (side[a1] != 0 || side[a2] != 0) continue;
        if (deg[a1] == 0 || deg[a2] == 0 || a1 == a2) continue;
        int b1 = adj[a1][rnd(deg[a1])];
        int b2 = adj[a2][rnd(deg[a2])];
        if (b1 == b2 || has[a1][b2] || has[a2][b1]) continue;
        *pa1 = a1; *pb1 = b1; *pa2 = a2; *pb2 = b2;
        return 1;
    }
    return 0;
}

static int read_graph(void) {
    int m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 1 || n > MAXN - 2 || m < 0) return 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (has[u][v] || deg[u] >= d || deg[v] >= d) return 0;
        add_edge(u, v);
    }
    W = (n + 63) / 64;
    for (int v = 0; v < n; v++) side[v] = -1;
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (side[v] == -1) {
                    side[v] = 1 - side[u];
                    queue[qt++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void print_best(void) {
    int m = 0;
    for (int u = 0; u < bestN; u++) if (bestSide[u] == 0) m += bestDeg[u];
    printf("%d %d\n", bestN, m);
    for (int u = 0; u < bestN; u++) {
        if (bestSide[u] != 0) continue;
        for (int i = 0; i < bestDeg[u]; i++) printf("%d %d\n", u, bestAdj[u][i]);
    }
}

int main(int argc, char **argv) {
    d = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    budget = argc > 4 ? atof(argv[4]) : 10.0;
    t0 = clock();
    rs ^= (seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) xr();

    if (d < 1 || d > MAXDEG - 2 || DD < 1) { printf("1 0\n"); return 0; }
    if (!read_graph()) { printf("1 0\n"); return 0; }
    if (cost() == 0) save_best();

    while (!time_up()) {
        if (haveBest) {
            load_best();
            if (n + 1 >= MAXN - 1 || (n + 64) / 64 > MAXW) break;
            grow_vertex();
            fill_greedy();
        }
        long long c = cost();
        int iters = 0;
        while (c > 0 && iters < SESSION) {
            if ((iters & 63) == 0 && time_up()) break;
            double T = 0.3 + 1.5 * (1.0 - (double)iters / SESSION);
            iters++;
            int a1, b1, a2, b2;
            if (!pick_swap(&a1, &b1, &a2, &b2)) continue;
            del_edge(a1, b1);
            del_edge(a2, b2);
            add_edge(a1, b2);
            add_edge(a2, b1);
            long long c2 = cost();
            if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) {
                c = c2;
            } else {
                del_edge(a1, b2);
                del_edge(a2, b1);
                add_edge(a1, b1);
                add_edge(a2, b2);
            }
        }
        if (c == 0) save_best();
    }

    if (haveBest) print_best();
    else printf("1 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions: start graphs (arc-extended projective planes, GQ).
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


def _arc_graph(m, edges, point_lines, S, line_points):
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
        n_c, e_c = _arc_graph(m, edges, point_lines, S, line_points)
        out.append((n_c, e_c))
    return out


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
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    rng = random.Random(seed * 7919 + d)
    pre_deadline = t0 + 0.1 * time_limit
    if D >= 3:
        for n_c, e_c in _arc_extensions(d, pre_deadline, rng):
            consider(n_c, e_c)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Growth search in C, only if the Moore bound is not already reached.
    if best_n < lib.moore_bound(d, D):
        remaining = 0.9 * time_limit - (time.monotonic() - t0)
        budget = remaining - 4.0
        if budget > 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=best, timeout=remaining)
                consider(*lib.parse_graph_text(out))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
