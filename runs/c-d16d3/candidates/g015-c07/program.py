import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: degree-preserving annealing on bipartite graphs with diameter D.
#
# The state is a bipartite graph (A = colour 0, B = colour 1) with max degree d.
# Cost = number of unordered vertex pairs at distance > D. Moves are degree-
# preserving edge switches (a1-b1, a2-b2 -> a1-b2, a2-b1). When the cost hits
# zero the graph is saved and grown by one A and one B vertex, using a
# degree-preserving insertion that steals edges. If a level stalls, the search
# reverts to the best saved graph and grows again.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define WM ((MAXN + 63) / 64)
#define DMAX 64
#define LEVEL_LIMIT 15000

static int N, DEG_MAX, DIAM;
static int deg[MAXN];
static int adj[MAXN][DMAX];
static unsigned char isadj[MAXN][MAXN];
static int color[MAXN];
static int listA[MAXN], nA, listB[MAXN], nB;
static uint64_t bufA[MAXN][WM], bufB[MAXN][WM];
static uint64_t rs;
static int best_n, best_m;
static int best_u[MAXN * DMAX], best_v[MAXN * DMAX];
static int in_u[MAXN * DMAX], in_v[MAXN * DMAX];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long eval_cost(void) {
    int W = (N + 63) >> 6;
    uint64_t (*cur)[WM] = bufA;
    uint64_t (*nxt)[WM] = bufB;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int j = 0; j < deg[v]; j++) {
                const uint64_t *s = cur[adj[v][j]];
                for (int w = 0; w < W; w++) nxt[v][w] |= s[w];
            }
        }
        uint64_t (*tmp)[WM] = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long unreached = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        unreached += N - c;
    }
    return unreached / 2;
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
    isadj[a][b] = 1;
    isadj[b][a] = 1;
}

static void del_edge(int a, int b) {
    for (int j = 0; j < deg[a]; j++) {
        if (adj[a][j] == b) {
            adj[a][j] = adj[a][--deg[a]];
            break;
        }
    }
    for (int j = 0; j < deg[b]; j++) {
        if (adj[b][j] == a) {
            adj[b][j] = adj[b][--deg[b]];
            break;
        }
    }
    isadj[a][b] = 0;
    isadj[b][a] = 0;
}

static void rebuild_lists(void) {
    nA = 0;
    nB = 0;
    for (int v = 0; v < N; v++) {
        if (color[v] == 0) listA[nA++] = v;
        else listB[nB++] = v;
    }
}

static void clear_graph(void) {
    for (int v = 0; v < MAXN; v++) {
        for (int j = 0; j < deg[v]; j++) isadj[v][adj[v][j]] = 0;
        deg[v] = 0;
    }
    N = 0;
}

static void load_best(void) {
    clear_graph();
    N = best_n;
    for (int i = 0; i < best_m; i++) add_edge(best_u[i], best_v[i]);
    rebuild_lists();
}

static void save_best(void) {
    best_n = N;
    best_m = 0;
    for (int v = 0; v < N; v++) {
        if (color[v] != 0) continue;
        for (int j = 0; j < deg[v]; j++) {
            best_u[best_m] = v;
            best_v[best_m] = adj[v][j];
            best_m++;
        }
    }
}

static void fill_graph(void) {
    for (int i = 0; i < nA; i++) {
        int a = listA[i];
        for (int j = 0; j < nB && deg[a] < DEG_MAX; j++) {
            int b = listB[j];
            if (deg[b] < DEG_MAX && !isadj[a][b]) add_edge(a, b);
        }
    }
}

/* Add two vertices x (colour A) and y (colour B). Steal edges so that both
   reach degree DEG_MAX while every old vertex keeps its degree. */
static int insert_pair(void) {
    if (N + 2 > MAXN) return 0;
    int x = N, y = N + 1;
    for (int u = 0; u < MAXN; u++) {
        isadj[x][u] = 0;
        isadj[u][x] = 0;
        isadj[y][u] = 0;
        isadj[u][y] = 0;
    }
    deg[x] = 0;
    deg[y] = 0;
    color[x] = 0;
    color[y] = 1;
    N += 2;
    rebuild_lists();
    int tries = 0, limit = 400 * DEG_MAX;
    while (deg[x] < DEG_MAX && deg[y] < DEG_MAX && tries < limit) {
        tries++;
        int b = listB[rndint(nB)];
        if (b == y || deg[b] == 0 || isadj[x][b]) continue;
        int a = adj[b][rndint(deg[b])];
        if (isadj[a][y]) continue;
        del_edge(a, b);
        add_edge(x, b);
        add_edge(a, y);
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG_MAX = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        n = 0;
        m = 0;
    }
    if (DEG_MAX < 1 || DEG_MAX > DMAX || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    if (n == 0 || m == 0) {
        n = 2 * DEG_MAX;
        m = 0;
        for (int i = 0; i < DEG_MAX; i++)
            for (int j = 0; j < DEG_MAX; j++) {
                in_u[m] = i;
                in_v[m] = DEG_MAX + j;
                m++;
            }
    } else {
        if (n > MAXN || m > MAXN * DMAX) {
            printf("0 0\n");
            return 0;
        }
        for (int i = 0; i < m; i++) {
            if (scanf("%d %d", &in_u[i], &in_v[i]) != 2) {
                printf("0 0\n");
                return 0;
            }
        }
    }

    /* Validate the start graph and load it. */
    N = n;
    for (int v = 0; v < N; v++) deg[v] = 0;
    memset(isadj, 0, sizeof(isadj));
    for (int i = 0; i < m; i++) {
        int u = in_u[i], v = in_v[i];
        if (u < 0 || u >= N || v < 0 || v >= N || u == v || isadj[u][v] ||
            deg[u] >= DEG_MAX || deg[v] >= DEG_MAX) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }
    for (int v = 0; v < N; v++) color[v] = -1;
    static int stk[MAXN];
    for (int s = 0; s < N; s++) {
        if (color[s] >= 0) continue;
        color[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int j = 0; j < deg[u]; j++) {
                int w = adj[u][j];
                if (color[w] < 0) {
                    color[w] = 1 - color[u];
                    stk[sp++] = w;
                } else if (color[w] == color[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    best_n = N;
    best_m = m;
    for (int i = 0; i < m; i++) {
        best_u[i] = in_u[i];
        best_v[i] = in_v[i];
    }

    rebuild_lists();
    fill_graph();
    long long cur_cost = eval_cost();
    if (cur_cost == 0) save_best();

    clock_t deadline = clock() + (clock_t)(tl * CLOCKS_PER_SEC);
    int level_it = 0;

    while (clock() < deadline) {
        if (cur_cost == 0) {
            save_best();
            if (!insert_pair()) break;
            level_it = 0;
            cur_cost = eval_cost();
            continue;
        }
        if (level_it >= LEVEL_LIMIT) {
            load_best();
            if (!insert_pair()) break;
            level_it = 0;
            cur_cost = eval_cost();
            continue;
        }
        if (nA == 0 || nB == 0) break;

        level_it++;
        double frac = (double)level_it / LEVEL_LIMIT;
        double T = 0.15 + 1.0 * (1.0 - frac);

        int a1 = listA[rndint(nA)];
        int a2 = listA[rndint(nA)];
        if (a1 == a2 || deg[a1] == 0 || deg[a2] == 0) continue;
        int b1 = adj[a1][rndint(deg[a1])];
        int b2 = adj[a2][rndint(deg[a2])];
        if (b1 == b2 || isadj[a1][b2] || isadj[a2][b1]) continue;

        del_edge(a1, b1);
        del_edge(a2, b2);
        add_edge(a1, b2);
        add_edge(a2, b1);
        long long nc = eval_cost();
        long long delta = nc - cur_cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur_cost = nc;
        } else {
            del_edge(a1, b2);
            del_edge(a2, b1);
            add_edge(a1, b1);
            add_edge(a2, b2);
        }
    }

    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", best_u[i], best_v[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions (fallbacks and starting points).
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
    """Old PG incidence plus a new A and a new B vertex per element of S (diameter 3)."""
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
        m, edges, point_lines, line_points, index, _ = _pg_data(q)
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

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.2 * time_limit, random.Random(seed * 7919 + d))
        for c in sorted(cands, key=lambda t: -t[0]):
            consider(c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # Main search: C annealing with vertex insertion, started from the best graph so far.
    avail = time_limit - (time.monotonic() - t0)
    if D >= 3 and avail > 6:
        cbudget = avail * 0.8 - 3.0
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(cbudget, 2)],
                             stdin_graph=best, timeout=avail * 0.9 - 1.0)
            consider(lib.parse_graph_text(text))
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
