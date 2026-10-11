import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: fixed-order bad-pair annealing with vertex growth.
#
# The graph is kept bipartite and valid. A growth step adds one vertex on a
# random side, joins it greedily to spare vertices on the opposite side, and
# then anneals over degree-respecting edge moves (double-edge swaps, edge
# insertions, edge deletions). The cost is the number of vertex pairs at
# distance greater than D, computed by bitset ball expansion. A growth step
# is kept only if the annealing reaches cost 0; otherwise the last valid graph
# is restored. The best valid graph found is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 2048
#define MAXW ((MAXN + 63) / 64)
#define MAXDEG 64
#define MAXE ((MAXN * MAXDEG) / 2)
#define ITERS_GROW 6000

typedef uint64_t Row[MAXW];

static int dmax = 0, Dist = 0;
static int N = 0;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int col[MAXN];
static int lst[2][MAXN];
static int cnt[2];
static Row BUFA[MAXN];
static Row BUFB[MAXN];
static uint64_t rs = 88172645463325252ULL;
static double deadline = 0.0;

static int sN = 0;
static int sdeg[MAXN];
static int sadj[MAXN][MAXDEG];
static int scol[MAXN];

static int bestN = 0, bestM = 0;
static int bestU[MAXE], bestV[MAXE];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int m) { return (int)(rnd64() % (uint64_t)m); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void rebuild_lists(void) {
    cnt[0] = cnt[1] = 0;
    for (int v = 0; v < N; v++) {
        int c = col[v];
        lst[c][cnt[c]++] = v;
    }
}

static int is_adj(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adj[a][i] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void del_arc(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a][i] == b) {
            adj[a][i] = adj[a][--deg[a]];
            return;
        }
    }
}

static void del_edge(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
}

/* Number of unordered vertex pairs at distance greater than Dist. */
static int cost_eval(void) {
    int W = (N + 63) >> 6;
    Row *cur = BUFA, *nxt = BUFB, *t;
    for (int v = 0; v < N; v++) {
        memset(cur[v], 0, sizeof(Row));
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < Dist; s++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt[v];
            memcpy(o, cur[v], sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = cur[adj[v][i]];
                for (int w = 0; w < W; w++) o[w] |= src[w];
            }
        }
        t = cur;
        cur = nxt;
        nxt = t;
    }
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        tot += N - c;
    }
    return (int)(tot / 2);
}

static int anneal(int iters, double T0, double T1, int cur) {
    if (cnt[0] == 0 || cnt[1] == 0) return cur;
    double lr = log(T1 / T0);
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && now() > deadline) break;
        double T = T0 * exp(lr * (double)it / (double)iters);
        int r = rndint(100);
        int c2, delta;
        if (r < 60) {
            /* degree-preserving double-edge swap */
            int a = lst[0][rndint(cnt[0])];
            int a2 = lst[0][rndint(cnt[0])];
            if (a == a2 || deg[a] == 0 || deg[a2] == 0) continue;
            int b = adj[a][rndint(deg[a])];
            int b2 = adj[a2][rndint(deg[a2])];
            if (b == b2 || is_adj(a, b2) || is_adj(a2, b)) continue;
            del_edge(a, b);
            del_edge(a2, b2);
            add_edge(a, b2);
            add_edge(a2, b);
            c2 = cost_eval();
            delta = c2 - cur;
            if (delta <= 0 || rnd01() < exp(-delta / T)) cur = c2;
            else {
                del_edge(a, b2);
                del_edge(a2, b);
                add_edge(a, b);
                add_edge(a2, b2);
            }
        } else if (r < 90) {
            /* insert a cross edge into spare capacity */
            int a = lst[0][rndint(cnt[0])];
            int b = lst[1][rndint(cnt[1])];
            if (deg[a] >= dmax || deg[b] >= dmax || is_adj(a, b)) continue;
            add_edge(a, b);
            c2 = cost_eval();
            delta = c2 - cur;
            if (delta <= 0 || rnd01() < exp(-delta / T)) cur = c2;
            else del_edge(a, b);
        } else {
            /* delete a cross edge */
            int a = lst[0][rndint(cnt[0])];
            if (deg[a] == 0) continue;
            int b = adj[a][rndint(deg[a])];
            del_edge(a, b);
            c2 = cost_eval();
            delta = c2 - cur;
            if (delta <= 0 || rnd01() < exp(-delta / T)) cur = c2;
            else add_edge(a, b);
        }
    }
    return cur;
}

/* Greedy initial neighbourhood for a new vertex w, using random spare vertices. */
static void attach_new(int w) {
    int other = 1 - col[w];
    if (cnt[other] == 0) return;
    int tries = 8 * cnt[other] + 16;
    for (int t = 0; t < tries && deg[w] < dmax; t++) {
        int x = lst[other][rndint(cnt[other])];
        if (deg[x] < dmax && !is_adj(w, x)) add_edge(w, x);
    }
}

static void save_state(void) {
    sN = N;
    memcpy(sdeg, deg, sizeof(int) * (size_t)N);
    memcpy(scol, col, sizeof(int) * (size_t)N);
    for (int v = 0; v < N; v++) memcpy(sadj[v], adj[v], sizeof(int) * (size_t)deg[v]);
}

static void restore_state(void) {
    N = sN;
    memcpy(deg, sdeg, sizeof(int) * (size_t)N);
    memcpy(col, scol, sizeof(int) * (size_t)N);
    for (int v = 0; v < N; v++) memcpy(adj[v], sadj[v], sizeof(int) * (size_t)deg[v]);
    rebuild_lists();
}

static void record_best(void) {
    if (N <= bestN) return;
    bestN = N;
    bestM = 0;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v][i];
            if (u > v && bestM < MAXE) {
                bestU[bestM] = v;
                bestV[bestM] = u;
                bestM++;
            }
        }
    }
}

static int qbuf[MAXN];

/* 2-colours the graph; returns 0 if it is not bipartite. */
static int color_graph(void) {
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        qbuf[tail++] = s;
        while (head < tail) {
            int u = qbuf[head++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    qbuf[tail++] = v;
                } else if (col[v] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static int set_kdd(void) {
    if (dmax < 1 || 2 * dmax > MAXN - 2) return 0;
    memset(deg, 0, sizeof(deg));
    N = 2 * dmax;
    for (int i = 0; i < dmax; i++)
        for (int j = 0; j < dmax; j++) add_edge(i, dmax + j);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    dmax = atoi(argv[1]);
    Dist = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    if (dmax < 1 || dmax > MAXDEG || Dist < 2) {
        printf("0 0\n");
        return 0;
    }
    deadline = now() + budget;

    /* Read the start graph. */
    memset(deg, 0, sizeof(deg));
    N = 0;
    int n = 0, m = 0, ok = 1;
    if (scanf("%d %d", &n, &m) != 2) {
        n = 0;
        m = 0;
    }
    if (n < 1 || n > MAXN - 2 || m < 0) ok = 0;
    if (ok) {
        N = n;
        for (int i = 0; i < m; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) {
                ok = 0;
                break;
            }
            if (u < 0 || v < 0 || u >= n || v >= n || u == v ||
                deg[u] >= dmax || deg[v] >= dmax || is_adj(u, v)) {
                ok = 0;
                break;
            }
            add_edge(u, v);
        }
    }
    if (ok && !color_graph()) ok = 0;
    if (!ok) {
        if (!set_kdd()) {
            printf("0 0\n");
            return 0;
        }
        color_graph();
    }

    rebuild_lists();
    int cur = cost_eval();
    if (cur > 0) cur = anneal(150000, 3.0, 0.05, cur);
    if (cur == 0) record_best();
    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Growth loop: add a vertex, repair by annealing, keep on success. */
    while (now() < deadline && N < MAXN - 1) {
        save_state();
        int w = N;
        N++;
        col[w] = rndint(2);
        deg[w] = 0;
        rebuild_lists();
        attach_new(w);
        int c = cost_eval();
        c = anneal(ITERS_GROW, 2.0, 0.05, c);
        if (c == 0) record_best();
        else restore_state();
    }

    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S
# with every line containing <= s points of S and every point on <= s lines
# indexed by S. Add an A-vertex for each P in S (joined to the lines through P)
# and a B-vertex for each j in S (joined to the points on line j).
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
# Build: arc-extended PG graphs, then the C growth/repair annealer on the best.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    ceiling = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < start + 0.20 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # C stage: grow from the best valid graph by bad-pair annealing.
    # Skipped when the best graph already meets the Moore bound.
    if best[0] < ceiling:
        elapsed = time.monotonic() - start
        budget = 0.85 * time_limit - elapsed
        if budget > 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"], stdin_graph=best,
                                timeout=0.95 * time_limit - elapsed)
                consider(*lib.parse_graph_text(out))
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
