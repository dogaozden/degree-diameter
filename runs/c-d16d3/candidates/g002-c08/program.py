import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with d >= q+1 it has spare s = d - q - 1. Add one new A-vertex per point of
# SA (joined to the q+1 lines through it, each line hit at most s times) and one
# new B-vertex per line of SB (joined to its q+1 points, each point hit at most
# s times). Diameter stays 3 for any SA, SB.
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
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
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
# C engine: vertex-growth annealing with bitset distance cost.
#
# Cost = number of unordered vertex pairs at distance > D (bitset BFS, D rounds).
# Moves keep the graph bipartite and degree <= d:
#   switch: 2-switch on two edges whose left ends share a side (degrees kept);
#   attach: join v to a random opposite-side w, removing an edge at a saturated end.
# Growth: add one vertex, anneal the cost to 0, record the larger graph, repeat.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXDEG 64
#define WMAX 16
#define ITERS 30000

static int dd, DD, N;
static int side[MAXN], deg[MAXN], adj[MAXN * MAXDEG];
static int bdeg[MAXN], badj[MAXN * MAXDEG];
static int sdeg[MAXN], sadj[MAXN * MAXDEG];
static int bestN;
static uint64_t BA[MAXN * WMAX], BB[MAXN * WMAX];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) if (adj[a * MAXDEG + k] == b) return 1;
    return 0;
}
static void del_half(int a, int b) {
    int *r = &adj[a * MAXDEG];
    for (int k = 0; k < deg[a]; k++)
        if (r[k] == b) { r[k] = r[deg[a] - 1]; deg[a]--; return; }
}
static void add_edge(int a, int b) {
    adj[a * MAXDEG + deg[a]++] = b;
    adj[b * MAXDEG + deg[b]++] = a;
}
static void del_edge(int a, int b) { del_half(a, b); del_half(b, a); }

static long long cost(void) {
    int nw = (N + 63) / 64;
    uint64_t *cur = BA, *nxt = BB;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < nw; w++) cur[v * WMAX + w] = 0;
        cur[v * WMAX + (v >> 6)] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < DD; s++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + v * WMAX;
            for (int w = 0; w < nw; w++) o[w] = cur[v * WMAX + w];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = cur + adj[v * MAXDEG + k] * WMAX;
                for (int w = 0; w < nw; w++) o[w] |= src[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += pc64(cur[v * WMAX + w]);
        bad += N - c;
    }
    return bad / 2;
}

static void move_switch(void) {
    for (int tries = 0; tries < 20; tries++) {
        int a = rndi(N);
        if (!deg[a]) continue;
        int b = adj[a * MAXDEG + rndi(deg[a])];
        int c = rndi(N);
        if (c == a || side[c] != side[a] || !deg[c]) continue;
        int e = adj[c * MAXDEG + rndi(deg[c])];
        if (e == b) continue;
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        return;
    }
}

static void move_attach(int v) {
    int s = side[v];
    for (int tries = 0; tries < 50; tries++) {
        int w = rndi(N);
        if (side[w] == s || has_edge(v, w)) continue;
        if (deg[v] >= dd) { int x = adj[v * MAXDEG + rndi(deg[v])]; del_edge(v, x); }
        if (deg[w] >= dd) { int y = adj[w * MAXDEG + rndi(deg[w])]; del_edge(w, y); }
        add_edge(v, w);
        return;
    }
}

static void save_state(void) {
    for (int v = 0; v < N; v++) {
        bdeg[v] = deg[v];
        memcpy(badj + v * MAXDEG, adj + v * MAXDEG, sizeof(int) * dd);
    }
}
static void restore_state(void) {
    for (int v = 0; v < N; v++) {
        deg[v] = bdeg[v];
        memcpy(adj + v * MAXDEG, badj + v * MAXDEG, sizeof(int) * dd);
    }
}
static void save_best(void) {
    bestN = N;
    for (int v = 0; v < N; v++) {
        sdeg[v] = deg[v];
        memcpy(sadj + v * MAXDEG, adj + v * MAXDEG, sizeof(int) * dd);
    }
}
static void load_best(void) {
    N = bestN;
    for (int v = 0; v < N; v++) {
        deg[v] = sdeg[v];
        memcpy(adj + v * MAXDEG, sadj + v * MAXDEG, sizeof(int) * dd);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL + 1;
    double tl = atof(argv[4]);
    if (dd < 1 || dd > MAXDEG || DD < 1) { printf("0 0\n"); return 0; }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n <= 0 || n >= MAXN) { printf("0 0\n"); return 0; }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (deg[u] >= dd || deg[v] >= dd || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    /* bipartition by BFS */
    int *q = malloc(sizeof(int) * N);
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        int head = 0, tail = 0;
        side[s] = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            for (int k = 0; k < deg[u]; k++) {
                int w = adj[u * MAXDEG + k];
                if (side[w] < 0) { side[w] = 1 - side[u]; q[tail++] = w; }
            }
        }
    }
    free(q);

    clock_t t0 = clock();
    double limit = tl * (double)CLOCKS_PER_SEC;
    save_best();

    while ((double)(clock() - t0) < limit && bestN < MAXN - 1) {
        load_best();
        int nv = N;
        N++;
        side[nv] = rndi(2);
        deg[nv] = 0;
        for (int k = 0; k < dd; k++) move_attach(nv);

        long long c = cost();
        const double T0 = 1.0, T1 = 0.05;
        for (int it = 0; it < ITERS && c > 0; it++) {
            if ((it & 127) == 0 && (double)(clock() - t0) >= limit) break;
            double T = T0 * pow(T1 / T0, (double)it / ITERS);
            save_state();
            if (rndi(100) < 60) {
                move_switch();
            } else {
                int v = (rndi(10) < 4) ? nv : rndi(N);
                move_attach(v);
            }
            long long c2 = cost();
            if (c2 <= c || rndu() < exp(-(double)(c2 - c) / T)) c = c2;
            else restore_state();
        }
        if (c == 0) save_best();
    }

    int cnt = 0;
    for (int v = 0; v < bestN; v++)
        for (int k = 0; k < sdeg[v]; k++)
            if (sadj[v * MAXDEG + k] > v) cnt++;
    printf("%d %d\n", bestN, cnt);
    for (int v = 0; v < bestN; v++)
        for (int k = 0; k < sdeg[v]; k++) {
            int u = sadj[v * MAXDEG + k];
            if (u > v) printf("%d %d\n", v, u);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Build: best algebraic start, then the C growth search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    rng = random.Random(seed)

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

    if D >= 3:
        cands = _arc_extensions(d, t_start + 0.15 * time_limit,
                                random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Growth search in C, starting from the best valid graph found so far.
    remaining = time_limit - (time.monotonic() - t_start)
    budget = remaining * 0.8 - 1.0
    if budget >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best, timeout=remaining * 0.9 - 0.5)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
