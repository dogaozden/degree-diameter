import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: local search that extends a valid start graph by one vertex at a
# time. Each attempt inserts a vertex, steals d edges for it, then anneals over
# degree-preserving 2-switches and endpoint transfers to remove every pair at
# distance > D. Cost = number of unordered pairs at distance > D (bitset balls).
# On failure the last valid snapshot is restored and the attempt is retried.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 1024
#define WMAX 16
#define MMAX 40000
#define DDMAX 64

static int dd, DD;
static int n, m;
static int side[NMAX];
static int deg[NMAX];
static int adj[NMAX][DDMAX];
static unsigned char A[NMAX][NMAX];
static int eu[MMAX], ev[MMAX];
static uint64_t bufA[NMAX][WMAX], bufB[NMAX][WMAX];
static uint64_t rs;

static int bestN, bestM;
static int bestSide[NMAX];
static int bestEu[MMAX], bestEv[MMAX];
static int candv[NMAX];

static double wall(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

/* Number of unordered pairs at distance > DD. */
static long cost_full(void) {
    int W = (n + 63) >> 6;
    uint64_t (*cur)[WMAX] = bufA;
    uint64_t (*nxt)[WMAX] = bufB;
    int v, k, u, w, r;
    for (v = 0; v < n; v++) {
        for (w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (r = 0; r < DD; r++) {
        for (v = 0; v < n; v++) {
            for (w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (k = 0; k < deg[v]; k++) {
                u = adj[v][k];
                for (w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[WMAX] = cur;
        cur = nxt;
        nxt = t;
    }
    long bad = 0;
    for (v = 0; v < n; v++) {
        int c = 0;
        for (w = 0; w < W; w++) c += __builtin_popcountll(cur[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static void adj_add(int v, int x) { adj[v][deg[v]++] = x; }

static void adj_remove(int v, int x) {
    int k;
    for (k = 0; k < deg[v]; k++) {
        if (adj[v][k] == x) {
            adj[v][k] = adj[v][deg[v] - 1];
            deg[v]--;
            return;
        }
    }
}

static void adj_replace(int v, int o, int nw) {
    int k;
    for (k = 0; k < deg[v]; k++) {
        if (adj[v][k] == o) { adj[v][k] = nw; return; }
    }
}

static void raw_link(int a, int b) {
    A[a][b] = A[b][a] = 1;
    adj_add(a, b);
    adj_add(b, a);
}

/* Edge e = (keep, from) becomes (keep, to); from and to lie on the same side. */
static void reattach(int e, int keep, int from, int to) {
    adj_remove(from, keep);
    adj_add(to, keep);
    adj_replace(keep, from, to);
    A[from][keep] = A[keep][from] = 0;
    A[to][keep] = A[keep][to] = 1;
    if (eu[e] == from) eu[e] = to; else ev[e] = to;
}

/* Involution: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). */
static void switch_edges(int e1, int e2) {
    int a1 = eu[e1], b1 = ev[e1], a2 = eu[e2], b2 = ev[e2];
    A[a1][b1] = A[b1][a1] = 0;
    A[a2][b2] = A[b2][a2] = 0;
    A[a1][b2] = A[b2][a1] = 1;
    A[a2][b1] = A[b1][a2] = 1;
    adj_replace(a1, b1, b2);
    adj_replace(b2, a2, a1);
    adj_replace(a2, b2, b1);
    adj_replace(b1, a1, a2);
    eu[e1] = a1; ev[e1] = b2;
    eu[e2] = a2; ev[e2] = b1;
}

static int find_edge(int z, int y) {
    int e;
    for (e = 0; e < m; e++) {
        if ((eu[e] == z && ev[e] == y) || (eu[e] == y && ev[e] == z)) return e;
    }
    return -1;
}

/* Add edges between deficient opposite-side vertices. Never increases cost. */
static void greedy_fill(void) {
    int a, b;
    for (a = 0; a < n; a++) {
        if (side[a] != 0 || deg[a] >= dd) continue;
        for (b = 0; b < n && deg[a] < dd; b++) {
            if (side[b] != 1 || deg[b] >= dd || A[a][b] || m >= MMAX) continue;
            eu[m] = a; ev[m] = b; m++;
            raw_link(a, b);
        }
    }
}

/* Insert one vertex and anneal until cost 0 or time 'until'. Returns 1 on success. */
static int extend_one(double until) {
    int x = n, s = rndint(2), j, tries, found, y, z, e, nc, xx;
    side[x] = s;
    deg[x] = 0;
    n++;
    for (j = 0; j < dd; j++) {
        found = 0;
        for (tries = 0; tries < 4000 && !found; tries++) {
            y = rndint(n);
            if (side[y] == s || A[x][y] || deg[y] == 0) continue;
            z = adj[y][rndint(deg[y])];
            e = find_edge(z, y);
            if (e < 0) continue;
            reattach(e, y, z, x);
            found = 1;
        }
        if (!found) break;
    }
    greedy_fill();
    long cur = cost_full();
    if (cur == 0) { greedy_fill(); return 1; }

    double tb = wall();
    double span = until - tb;
    if (span <= 0.05) return 0;

    double T = 1.0;
    long it = 0;
    while (cur > 0) {
        if ((it & 15) == 0) {
            double nw = wall();
            if (nw >= until) break;
            double f = (nw - tb) / span;
            T = 2.0 * pow(0.02 / 2.0, f);
        }
        it++;
        if (rnd01() < 0.3) {
            /* Endpoint transfer: give a deficient vertex xx one more edge, taking it from a neighbour. */
            nc = 0;
            for (xx = 0; xx < n; xx++) if (deg[xx] < dd) candv[nc++] = xx;
            if (nc == 0) continue;
            xx = candv[rndint(nc)];
            y = rndint(n);
            if (side[y] == side[xx] || A[xx][y] || deg[y] == 0) continue;
            z = adj[y][rndint(deg[y])];
            e = find_edge(z, y);
            if (e < 0) continue;
            reattach(e, y, z, xx);
            long c2 = cost_full();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                reattach(e, y, xx, z);
            }
        } else {
            /* Degree-preserving 2-switch. */
            if (m < 2) continue;
            e = rndint(m);
            int e2 = rndint(m);
            if (e == e2) continue;
            int a1 = eu[e], b1 = ev[e], a2 = eu[e2], b2 = ev[e2];
            if (a1 == a2 || b1 == b2 || A[a1][b2] || A[a2][b1]) continue;
            switch_edges(e, e2);
            long c3 = cost_full();
            if (c3 <= cur || rnd01() < exp(-(double)(c3 - cur) / T)) {
                cur = c3;
            } else {
                switch_edges(e, e2);
            }
        }
    }
    if (cur != 0) return 0;
    greedy_fill();
    return 1;
}

static void snapshot(void) {
    int i;
    bestN = n;
    bestM = m;
    for (i = 0; i < n; i++) bestSide[i] = side[i];
    for (i = 0; i < m; i++) { bestEu[i] = eu[i]; bestEv[i] = ev[i]; }
}

static void rebuild_from_best(void) {
    int v;
    n = bestN;
    m = bestM;
    memset(A, 0, sizeof(A));
    for (v = 0; v < n; v++) { deg[v] = 0; side[v] = bestSide[v]; }
    for (v = 0; v < m; v++) {
        eu[v] = bestEu[v];
        ev[v] = bestEv[v];
        raw_link(eu[v], ev[v]);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    double t0 = wall();
    double end_all = t0 + limit;

    int nin, min_, i;
    if (scanf("%d %d", &nin, &min_) != 2 || nin <= 0 || nin > NMAX - 8 ||
        min_ < 0 || min_ > MMAX / 2 || dd < 1 || dd > DDMAX || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    static int ru[MMAX], rv[MMAX];
    static int color[NMAX], queue[NMAX];
    int ok = 1;
    n = nin;
    m = 0;
    for (i = 0; i < min_ && ok; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) ok = 0;
        else if (u < 0 || v < 0 || u >= n || v >= n || u == v || A[u][v] ||
                 deg[u] >= dd || deg[v] >= dd) ok = 0;
        else {
            A[u][v] = A[v][u] = 1;
            adj_add(u, v);
            adj_add(v, u);
            ru[i] = u;
            rv[i] = v;
        }
    }
    for (i = 0; i < n; i++) color[i] = -1;
    for (int s = 0; s < n && ok; s++) {
        if (color[s] >= 0) continue;
        int qh = 0, qt = 0, k;
        color[s] = 0;
        queue[qt++] = s;
        while (qh < qt && ok) {
            int u = queue[qh++];
            for (k = 0; k < deg[u]; k++) {
                int w = adj[u][k];
                if (color[w] < 0) {
                    color[w] = 1 - color[u];
                    queue[qt++] = w;
                } else if (color[w] == color[u]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    for (i = 0; i < n; i++) side[i] = color[i];
    for (i = 0; i < min_; i++) {
        if (side[ru[i]] == 0) { eu[i] = ru[i]; ev[i] = rv[i]; }
        else { eu[i] = rv[i]; ev[i] = ru[i]; }
    }
    m = min_;
    snapshot();

    while (1) {
        double rem = end_all - wall();
        if (rem < 0.3 || n + 2 > NMAX || m + dd > MMAX) break;
        double until = wall() + rem * 0.5;
        if (until > end_all) until = end_all;
        if (extend_one(until)) snapshot();
        else rebuild_from_best();
    }

    printf("%d %d\n", bestN, bestM);
    for (i = 0; i < bestM; i++) printf("%d %d\n", bestEu[i], bestEv[i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions used as start graphs.
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
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
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
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
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
    """Projective-plane incidence graphs with extra A-vertices and B-vertices; diameter 3."""
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Start graphs from algebraic constructions.
    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.15 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Bold step: C local search adds vertices to the best start graph.
    if D >= 3 and d >= 4:
        elapsed = time.monotonic() - t0
        budget = 0.7 * time_limit - elapsed
        if budget > 1.0:
            timeout = max(1.0, 0.9 * time_limit - elapsed)
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed & 0xFFFFFFFF, round(budget, 2)],
                                stdin_graph=best, timeout=timeout)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
