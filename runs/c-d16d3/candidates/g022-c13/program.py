import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: fixed-order simulated annealing on bipartite graphs.
#
# Input: a valid bipartite graph (max degree d, diameter <= D). The engine keeps
# a global 2-colouring and never breaks it. Cost = number of unordered vertex
# pairs at distance > D (bitset ball computation). Moves:
#   - edge switch (a,b),(c,e) -> (a,e),(c,b): keeps all degrees and the colouring,
#   - add a spare cross edge (never increases cost),
#   - once cost == 0, record the graph and add a new vertex joined to spare
#     vertices of the opposite colour, then keep annealing.
# The best (largest valid) graph is printed at the end.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 512
#define W 8
#define MAXDEG 64
#define MAXM 40000

typedef uint64_t u64;

static int d, D, n, m;
static int color[MAXN];
static int deg[MAXN];
static unsigned char adj[MAXN][MAXN];
static int eu[MAXM], ev[MAXM];
static int nb[MAXN][MAXDEG];
static int nd[MAXN];
static u64 BA[MAXN][W], BB[MAXN][W];
static u64 rs;

static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd64() % (u64)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long cost(void) {
    int v, k, t, w;
    for (v = 0; v < n; v++) nd[v] = 0;
    for (k = 0; k < m; k++) {
        int a = eu[k], b = ev[k];
        nb[a][nd[a]++] = b;
        nb[b][nd[b]++] = a;
    }
    for (v = 0; v < n; v++) {
        for (w = 0; w < W; w++) BA[v][w] = 0;
        BA[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (t = 0; t < D; t++) {
        for (v = 0; v < n; v++) {
            for (w = 0; w < W; w++) BB[v][w] = BA[v][w];
            for (k = 0; k < nd[v]; k++) {
                int u = nb[v][k];
                for (w = 0; w < W; w++) BB[v][w] |= BA[u][w];
            }
        }
        for (v = 0; v < n; v++)
            for (w = 0; w < W; w++) BA[v][w] = BB[v][w];
    }
    long long bad = 0;
    for (v = 0; v < n; v++) {
        int c = 0;
        for (w = 0; w < W; w++) c += pc(BA[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static void setadj(int a, int b, int val) {
    adj[a][b] = adj[b][a] = (unsigned char)val;
}

static void add_edge_raw(int p, int q) {
    int a = (color[p] == 0) ? p : q;
    int b = (a == p) ? q : p;
    eu[m] = a;
    ev[m] = b;
    m++;
    setadj(p, q, 1);
    deg[p]++;
    deg[q]++;
}

static int color_graph(void) {
    static int qu[MAXN];
    int s, qh, qt, u, v;
    for (v = 0; v < n; v++) color[v] = -1;
    for (s = 0; s < n; s++) {
        if (color[s] >= 0) continue;
        color[s] = 0;
        qh = qt = 0;
        qu[qt++] = s;
        while (qh < qt) {
            u = qu[qh++];
            for (v = 0; v < n; v++) {
                if (!adj[u][v]) continue;
                if (color[v] < 0) {
                    color[v] = 1 - color[u];
                    qu[qt++] = v;
                } else if (color[v] == color[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void add_vertex(void) {
    int w = n, col = rndint(2), cnt = 0, k, i, j;
    static int cand[MAXN];
    n++;
    color[w] = col;
    deg[w] = 0;
    for (k = 0; k < w; k++)
        if (color[k] == 1 - col && deg[k] < d) cand[cnt++] = k;
    for (i = cnt - 1; i > 0; i--) {
        j = rndint(i + 1);
        k = cand[i]; cand[i] = cand[j]; cand[j] = k;
    }
    for (k = 0; k < cnt && deg[w] < d && m < MAXM; k++)
        add_edge_raw(w, cand[k]);
}

static void try_add_edge(void) {
    static int s0[MAXN], s1[MAXN];
    int c0 = 0, c1 = 0, v, t;
    if (m >= MAXM) return;
    for (v = 0; v < n; v++) {
        if (deg[v] < d) {
            if (color[v] == 0) s0[c0++] = v;
            else s1[c1++] = v;
        }
    }
    if (c0 == 0 || c1 == 0) return;
    for (t = 0; t < 40; t++) {
        int x = s0[rndint(c0)], y = s1[rndint(c1)];
        if (!adj[x][y]) {
            add_edge_raw(x, y);
            return;
        }
    }
}

int main(int argc, char **argv) {
    static int tu[MAXM], tv[MAXM];
    static int bestU[MAXM], bestV[MAXM];
    int bestN = 0, bestM = 0, k;
    long long cur;
    double tl, T, el;
    clock_t t0 = clock();

    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (!rs) rs = 1;
    tl = atof(argv[4]);

    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    if (n < 1 || n > MAXN || m < 0 || m > MAXM || d < 1 || d > MAXDEG || D < 1) {
        printf("0 0\n");
        return 0;
    }
    for (k = 0; k < m; k++) {
        int x, y;
        if (scanf("%d %d", &x, &y) != 2 || x < 0 || y < 0 || x >= n || y >= n ||
            x == y || adj[x][y]) {
            printf("0 0\n");
            return 0;
        }
        setadj(x, y, 1);
        tu[k] = x;
        tv[k] = y;
        deg[x]++;
        deg[y]++;
    }
    for (k = 0; k < n; k++)
        if (deg[k] > d) { printf("0 0\n"); return 0; }
    if (!color_graph()) { printf("0 0\n"); return 0; }
    for (k = 0; k < m; k++) {
        int x = tu[k], y = tv[k];
        if (color[x] == 0) { eu[k] = x; ev[k] = y; }
        else { eu[k] = y; ev[k] = x; }
    }

    cur = cost();
    if (cur == 0) {
        bestN = n; bestM = m;
        memcpy(bestU, eu, sizeof(int) * m);
        memcpy(bestV, ev, sizeof(int) * m);
    }

    for (;;) {
        el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (el >= tl) break;
        T = 0.2 + 0.6 * (1.0 - el / tl);

        if (cur == 0) {
            bestN = n; bestM = m;
            memcpy(bestU, eu, sizeof(int) * m);
            memcpy(bestV, ev, sizeof(int) * m);
            if (n >= MAXN) break;
            add_vertex();
            cur = cost();
            continue;
        }

        if (rnd01() < 0.1) {
            try_add_edge();
            cur = cost();
            continue;
        }

        if (m < 2) break;
        {
            int i = rndint(m), j = rndint(m);
            int a, b, c, e;
            long long nw, delta;
            if (i == j) continue;
            a = eu[i]; b = ev[i]; c = eu[j]; e = ev[j];
            if (a == c || b == e || adj[a][e] || adj[c][b]) continue;
            setadj(a, b, 0);
            setadj(c, e, 0);
            setadj(a, e, 1);
            setadj(c, b, 1);
            eu[i] = a; ev[i] = e;
            eu[j] = c; ev[j] = b;
            nw = cost();
            delta = nw - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cur = nw;
            } else {
                setadj(a, e, 0);
                setadj(c, b, 0);
                setadj(a, b, 1);
                setadj(c, e, 1);
                eu[i] = a; ev[i] = b;
                eu[j] = c; ev[j] = e;
            }
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bestM);
    for (k = 0; k < bestM; k++)
        printf("%d %d\n", bestU[k], bestV[k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions: arc-extended projective planes (start graphs) and
# the W(q) generalized quadrangle for D = 4.
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
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# build: start from the best Python construction, then let the C annealer
# try to insert more vertices while keeping every pair within distance D.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        arcs = _arc_extensions(d, start + 0.08 * time_limit,
                               random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < start + 0.15 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # C annealing: starts from the best valid graph and tries to grow it.
    # Skipped when the start already meets the Moore bound (nothing to gain).
    budget = 0.85 * time_limit - (time.monotonic() - start) - 1.0
    if d <= 64 and best[0] < lib.moore_bound(d, D) and budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                             stdin_graph=best, timeout=budget + 4.0)
            n2, e2 = lib.parse_graph_text(text)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
