import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing on a fixed-order bipartite graph.
#
# Cost = number of unordered vertex pairs at distance > D (bitset balls).
# Moves keep the graph bipartite and degrees <= d:
#   switch: (a,b),(c,e) -> (a,e),(c,b) with a,c on side 0 and b,e on side 1.
#   shift : a deficient vertex w takes an edge (x,y) from its side's partner,
#           which moves one unit of spare degree onto x.
# Adding an edge never increases any distance, so whenever a spare pair exists
# it is filled greedily. The engine grows the graph by one vertex at a time
# after each zero-cost state, and restores the last valid snapshot when a
# growth attempt does not reach zero cost within a phase.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 2048
#define MAXD 64
#define MAXW (MAXN / 64)
#define MAXM (MAXN * MAXD / 2)

typedef uint64_t row_t[MAXW];

static int n, d, D, M;
static int deg[MAXN], col[MAXN];
static int adj[MAXN][MAXD];
static int eu[MAXM], ev[MAXM];
static row_t bufA[MAXN], bufB[MAXN];
static int defi[MAXN];
static uint64_t rs = 88172645463325252ULL;

static int sn, sM;
static int scol[MAXN];
static int seu[MAXM], sev[MAXM];

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int popc64(uint64_t x) {
#if defined(__GNUC__) || defined(__clang__)
    return __builtin_popcountll(x);
#else
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
#endif
}

static int has_edge(int u, int v) {
    int a = u, b = v;
    if (deg[a] > deg[b]) { a = v; b = u; }
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) return 1;
    return 0;
}

static void link_add(int u, int v) { adj[u][deg[u]++] = v; }

static void link_pair(int u, int v) { link_add(u, v); link_add(v, u); }

static void push_edge(int u, int v) {
    if (col[u] == 0) { eu[M] = u; ev[M] = v; }
    else { eu[M] = v; ev[M] = u; }
    M++;
}

static void add_edge_full(int u, int v) {
    link_pair(u, v);
    push_edge(u, v);
}

static void replace_nb(int u, int old, int nw) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == old) { adj[u][i] = nw; return; }
    }
}

static void remove_nb(int u, int old) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == old) {
            adj[u][i] = adj[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

/* Degree-preserving switch of edges i and j. Reverting is the same call. */
static int try_switch(int i, int j) {
    if (i == j) return 0;
    int a = eu[i], b = ev[i], c = eu[j], e = ev[j];
    if (a == c || b == e) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    replace_nb(a, b, e);
    replace_nb(e, c, a);
    replace_nb(c, e, b);
    replace_nb(b, a, c);
    eu[i] = a; ev[i] = e;
    eu[j] = c; ev[j] = b;
    return 1;
}

/* Deficient vertex w takes edge k = (x, y) from the other endpoint. */
static int try_shift(int w, int k) {
    int x = eu[k], y = ev[k];
    if (col[w] == 0) {
        if (x == w || has_edge(w, y)) return 0;
        remove_nb(x, y);
        replace_nb(y, x, w);
        link_add(w, y);
        eu[k] = w;
    } else {
        if (y == w || has_edge(x, w)) return 0;
        remove_nb(y, x);
        replace_nb(x, y, w);
        link_add(w, x);
        ev[k] = w;
    }
    return 1;
}

static void shift_undo(int w, int k, int x, int y) {
    if (col[w] == 0) {
        remove_nb(w, y);
        replace_nb(y, w, x);
        link_add(x, y);
        eu[k] = x;
    } else {
        remove_nb(w, x);
        replace_nb(x, w, y);
        link_add(y, x);
        ev[k] = y;
    }
}

static row_t *compute_balls(void) {
    row_t *P = bufA, *Q = bufB;
    int W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) P[v][w] = 0;
        P[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) Q[v][w] = P[v][w];
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = P[adj[v][i]];
                for (int w = 0; w < W; w++) Q[v][w] |= src[w];
            }
        }
        row_t *t = P; P = Q; Q = t;
    }
    return P;
}

static long cost_eval(void) {
    int W = (n + 63) >> 6;
    row_t *R = compute_balls();
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(R[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static void shuffle_list(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = (int)(rnd() % (uint32_t)(i + 1));
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

static void greedy_fill(void) {
    static int sa[MAXN], sb[MAXN];
    int na = 0, nb = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d) {
            if (col[v] == 0) sa[na++] = v;
            else sb[nb++] = v;
        }
    }
    shuffle_list(sa, na);
    shuffle_list(sb, nb);
    for (int i = 0; i < na; i++) {
        int x = sa[i];
        for (int j = 0; j < nb && deg[x] < d; j++) {
            int y = sb[j];
            if (deg[y] >= d || has_edge(x, y)) continue;
            if (M >= MAXM) return;
            add_edge_full(x, y);
        }
    }
}

static int add_vertex(int side) {
    if (n >= MAXN) return 0;
    int w = n++;
    col[w] = side;
    deg[w] = 0;
    greedy_fill();
    return 1;
}

static void take_snapshot(void) {
    sn = n;
    sM = M;
    memcpy(scol, col, sizeof(int) * (size_t)n);
    memcpy(seu, eu, sizeof(int) * (size_t)M);
    memcpy(sev, ev, sizeof(int) * (size_t)M);
}

static void restore_snapshot(void) {
    n = sn;
    M = 0;
    for (int v = 0; v < n; v++) {
        deg[v] = 0;
        col[v] = scol[v];
    }
    for (int k = 0; k < sM; k++) add_edge_full(seu[k], sev[k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    long phase = (argc > 5) ? atol(argv[5]) : 30000L;
    if (phase < 100) phase = 100;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int k = 0; k < 20; k++) rnd();

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2 || N0 < 1 || N0 > MAXN) { printf("0 0\n"); return 0; }
    n = N0;
    M = 0;
    for (int v = 0; v < n; v++) { deg[v] = 0; col[v] = -1; }

    static int tu[MAXM], tv[MAXM];
    int tm = 0;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        if (tm >= MAXM) break;
        link_pair(u, v);
        tu[tm] = u; tv[tm] = v; tm++;
    }

    static int queue[MAXN];
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
    for (int k = 0; k < tm; k++) {
        if (col[tu[k]] == col[tv[k]]) { printf("0 0\n"); return 0; }
    }
    for (int v = 0; v < n; v++) deg[v] = 0;
    M = 0;
    for (int k = 0; k < tm; k++) add_edge_full(tu[k], tv[k]);

    take_snapshot();
    long cost = cost_eval();
    double t0 = now();
    long phase_it = 0;

    while (1) {
        if (now() - t0 > budget) break;

        if (cost == 0) {
            take_snapshot();
            if (n >= MAXN - 1) break;
            add_vertex((int)(rnd() & 1u));
            cost = cost_eval();
            phase_it = 0;
            continue;
        }
        if (phase_it >= phase) {
            restore_snapshot();
            cost = 0;
            phase_it = 0;
            continue;
        }
        if (M < 2) break;

        phase_it++;
        if (phase_it % 200 == 0) {
            greedy_fill();
            cost = cost_eval();
            if (cost == 0) continue;
        }

        int nd = 0;
        for (int v = 0; v < n; v++) if (deg[v] < d) defi[nd++] = v;

        int kind = 0, k1 = 0, k2 = 0, w = 0, x = 0, y = 0;
        if (nd > 0 && (rnd() % 10u) < 3u) {
            w = defi[rnd() % (uint32_t)nd];
            k1 = (int)(rnd() % (uint32_t)M);
            x = eu[k1];
            y = ev[k1];
            if (!try_shift(w, k1)) continue;
            kind = 1;
        } else {
            k1 = (int)(rnd() % (uint32_t)M);
            k2 = (int)(rnd() % (uint32_t)M);
            if (!try_switch(k1, k2)) continue;
            kind = 2;
        }

        long c2 = cost_eval();
        long delta = c2 - cost;
        int acc = 0;
        if (delta <= 0) {
            acc = 1;
        } else {
            double T = 0.2 + 1.0 * (1.0 - (double)phase_it / (double)phase);
            double p = exp(-(double)delta / T);
            if ((double)(rnd() & 0xFFFFFu) / 1048576.0 < p) acc = 1;
        }
        if (acc) {
            cost = c2;
        } else if (kind == 1) {
            shift_undo(w, k1, x, y);
        } else {
            try_switch(k1, k2);
        }
    }

    if (cost == 0) take_snapshot();

    printf("%d %d\n", sn, sM);
    for (int k = 0; k < sM; k++) printf("%d %d\n", seu[k], sev[k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3). Start graphs.
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare s = d - q - 1.
# A-side: SA points each get a new vertex joined to the q+1 lines through them.
# B-side: SB lines each get a new vertex joined to the q+1 points on them.
# ----------------------------------------------------------------------------

_LS_ITERS = 30000


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
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy load-constrained set."""
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


def _local_search(m, s, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the load-constrained set problem."""
    if s < 1:
        return list(S)
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= s:
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc."""
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
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for q in qs:
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

        SA = _local_search(m, s, point_lines, SA, rng, deadline, _LS_ITERS)
        SB = _local_search(m, s, line_points, SB, rng, deadline, _LS_ITERS)

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used as a start graph for D >= 4.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Search driver: C annealing that grows a valid graph vertex by vertex.
# ----------------------------------------------------------------------------

def _c_sa(graph, d, D, seed, budget):
    """Run the C annealing engine from a valid graph; return (n, edges) or None."""
    if graph is None or budget < 1.0 or d > 64:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), 30000],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 6.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


def build(d, D, seed, time_limit):
    start = time.monotonic()

    def el():
        return time.monotonic() - start

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        cands = _arc_extensions(d, start + 0.20 * time_limit,
                                random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for g in cands[:3]:
            consider(g)
    elif D >= 4:
        consider(_best_gq(d))

    rem = 0.90 * time_limit - el() - 1.5
    if rem >= 1.0:
        consider(_c_sa(best, d, D, seed, rem))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
