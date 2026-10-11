import random
import time

import lib


C_SOURCE = r"""
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

/* Vertex-insertion + annealed edge repair search for bipartite graphs with
   max degree D_MAX and diameter DIAM. The state is always bipartite with
   fixed sides. Cost = number of unordered vertex pairs at distance > DIAM.
   Whenever cost is 0 the graph is valid: it is saved as a snapshot and a new
   vertex (joined to D_MAX vertices of the opposite side) is inserted. */

#define MAXV 2600
#define MAXW 41

static int D_MAX, DIAM, NV;
static int side[MAXV], deg[MAXV];
static int *adj;
static uint64_t bufA[MAXV * MAXW], bufB[MAXV * MAXW];
static int snapN = 0, snapM = 0;
static int snapSide[MAXV];
static int *snapE;
static uint64_t rs = 88172645463325252ULL;
static int nlog;
typedef struct { int type, a, b; } Op;
static Op oplog[8];

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int has_edge(int a, int b) {
    const int *p = adj + (size_t)a * D_MAX;
    for (int i = 0; i < deg[a]; i++) if (p[i] == b) return 1;
    return 0;
}
static void raw_rem1(int a, int b) {
    int *p = adj + (size_t)a * D_MAX;
    for (int i = 0; i < deg[a]; i++) {
        if (p[i] == b) { p[i] = p[deg[a] - 1]; deg[a]--; return; }
    }
}
static void raw_add(int a, int b) {
    adj[(size_t)a * D_MAX + deg[a]++] = b;
    adj[(size_t)b * D_MAX + deg[b]++] = a;
}
static void raw_rem(int a, int b) { raw_rem1(a, b); raw_rem1(b, a); }
static void op_add(int a, int b) {
    raw_add(a, b);
    oplog[nlog].type = 1; oplog[nlog].a = a; oplog[nlog].b = b; nlog++;
}
static void op_rem(int a, int b) {
    raw_rem(a, b);
    oplog[nlog].type = 0; oplog[nlog].a = a; oplog[nlog].b = b; nlog++;
}
static void undo_all(void) {
    while (nlog > 0) {
        nlog--;
        Op o = oplog[nlog];
        if (o.type) raw_rem(o.a, o.b);
        else raw_add(o.a, o.b);
    }
}

static long long bad_cost(void) {
    int W = (NV + 63) / 64;
    uint64_t *cur = bufA, *nxt = bufB;
    for (int v = 0; v < NV; v++) {
        for (int w = 0; w < W; w++) cur[v * W + w] = 0;
        cur[v * W + (v >> 6)] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < DIAM; s++) {
        for (int v = 0; v < NV; v++) {
            uint64_t *o = nxt + v * W;
            uint64_t *c = cur + v * W;
            for (int w = 0; w < W; w++) o[w] = c[w];
            const int *p = adj + (size_t)v * D_MAX;
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *c2 = cur + p[i] * W;
                for (int w = 0; w < W; w++) o[w] |= c2[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < NV; v++) {
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += __builtin_popcountll(cur[v * W + w]);
        bad += NV - cnt;
    }
    return bad / 2;
}

static void save_snapshot(void) {
    snapN = NV;
    snapM = 0;
    for (int v = 0; v < NV; v++) snapSide[v] = side[v];
    for (int v = 0; v < NV; v++) {
        const int *p = adj + (size_t)v * D_MAX;
        for (int i = 0; i < deg[v]; i++) {
            int u = p[i];
            if (u > v) {
                snapE[2 * snapM] = v;
                snapE[2 * snapM + 1] = u;
                snapM++;
            }
        }
    }
}

static void restore_snapshot(void) {
    for (int v = 0; v < MAXV; v++) deg[v] = 0;
    NV = snapN;
    for (int v = 0; v < NV; v++) side[v] = snapSide[v];
    for (int i = 0; i < snapM; i++) raw_add(snapE[2 * i], snapE[2 * i + 1]);
    nlog = 0;
}

/* Insert a new vertex on a random side joined to D_MAX opposite-side vertices.
   Saturated neighbours give up one random edge to make room. */
static int grow_once(void) {
    if (NV + 1 >= MAXV) return 0;
    int s = rndint(2);
    static int cand[MAXV];
    int nc = 0;
    for (int v = 0; v < NV; v++) if (side[v] != s) cand[nc++] = v;
    if (nc < D_MAX) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    int x = NV;
    side[x] = s;
    deg[x] = 0;
    int got = 0;
    for (int i = 0; i < nc && got < D_MAX; i++) {
        int b = cand[i];
        if (deg[b] < D_MAX) { raw_add(x, b); got++; }
    }
    for (int i = 0; i < nc && got < D_MAX; i++) {
        int b = cand[i];
        if (deg[b] >= D_MAX && !has_edge(x, b)) {
            int a2 = adj[(size_t)b * D_MAX + rndint(deg[b])];
            raw_rem(b, a2);
            raw_add(x, b);
            got++;
        }
    }
    NV++;
    return 1;
}

/* One random move on the bipartite state; logs ops for undo. */
static int random_move(void) {
    nlog = 0;
    int r = rndint(10);
    if (r < 3) {
        int a = rndint(NV), b = rndint(NV);
        if (side[a] == side[b] || deg[a] >= D_MAX || deg[b] >= D_MAX || has_edge(a, b)) return 0;
        op_add(a, b);
        return 1;
    }
    if (r < 5) {
        int a = rndint(NV);
        if (deg[a] == 0) return 0;
        int b = adj[(size_t)a * D_MAX + rndint(deg[a])];
        op_rem(a, b);
        return 1;
    }
    /* degree-preserving switch: (a,b),(c,e) -> (a,e),(c,b) on the same side of a,c */
    int a = rndint(NV);
    if (deg[a] == 0) return 0;
    int b = adj[(size_t)a * D_MAX + rndint(deg[a])];
    int c = rndint(NV);
    if (c == a || side[c] != side[a] || deg[c] == 0) return 0;
    int e = adj[(size_t)c * D_MAX + rndint(deg[c])];
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    op_rem(a, b);
    op_rem(c, e);
    op_add(a, e);
    op_add(c, b);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    D_MAX = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    if (D_MAX < 1 || DIAM < 1) { printf("0 0\n"); return 0; }

    adj = malloc(sizeof(int) * (size_t)MAXV * D_MAX);
    snapE = malloc(sizeof(int) * 2 * (size_t)MAXV * D_MAX);
    if (!adj || !snapE) { printf("0 0\n"); return 0; }

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXV - 2 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(m + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m + 1));
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { printf("0 0\n"); return 0; }
    }
    int ok = 1;
    for (int i = 0; i < m && ok; i++) {
        if (eu[i] < 0 || eu[i] >= n || ev[i] < 0 || ev[i] >= n || eu[i] == ev[i]) ok = 0;
    }
    NV = n;
    for (int v = 0; v < MAXV; v++) deg[v] = 0;
    for (int i = 0; i < m && ok; i++) {
        int a = eu[i], b = ev[i];
        if (deg[a] >= D_MAX || deg[b] >= D_MAX || has_edge(a, b)) ok = 0;
        else raw_add(a, b);
    }
    for (int v = 0; v < n; v++) side[v] = -1;
    int *q = malloc(sizeof(int) * (size_t)n);
    for (int s = 0; s < n && ok; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail && ok) {
            int v = q[head++];
            const int *p = adj + (size_t)v * D_MAX;
            for (int i = 0; i < deg[v]; i++) {
                int u = p[i];
                if (side[u] < 0) { side[u] = 1 - side[v]; q[tail++] = u; }
                else if (side[u] == side[v]) { ok = 0; break; }
            }
        }
    }
    free(q);
    if (!ok) { printf("0 0\n"); return 0; }

    long long cost = bad_cost();
    if (cost == 0) save_snapshot();

    double t0 = now();
    long long stall = 0;
    const long long STALL_LIMIT = 40000;
    const double T = 0.6;
    while (now() - t0 < budget) {
        if (cost == 0) {
            if (NV > snapN) save_snapshot();
            if (!grow_once()) break;
            cost = bad_cost();
            stall = 0;
            continue;
        }
        if (stall > STALL_LIMIT) {
            if (snapN > 0) { restore_snapshot(); cost = bad_cost(); }
            stall = 0;
            continue;
        }
        stall++;
        if (!random_move()) continue;
        long long nc = bad_cost();
        long long delta = nc - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cost = nc;
        else undo_all();
    }

    if (snapN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", snapN, snapM);
    for (int i = 0; i < snapM; i++) printf("%d %d\n", snapE[2 * i], snapE[2 * i + 1]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), as in the parent.
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with spare capacity s = d-q-1 we pick a point set S (an arc or a greedy
# set) whose line loads and point loads are <= s. For each P in S add an A-vertex
# joined to the lines through P; for each j in S add a B-vertex joined to the
# points on line j.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


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
    """Randomized greedy set S with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old incidence graph plus a new A-vertex and a new B-vertex per element of S."""
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


def _best_arc_graph(d, seed, deadline):
    """Largest arc-extended PG(2,q) graph over prime powers q with q + 1 <= d, or None."""
    rng = random.Random(seed * 7919 + d)
    best = None
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, S)
        if best is None or n_c > best[0]:
            best = (n_c, e_c)
    return best


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        cand = _best_arc_graph(d, seed, t_start + 0.3 * time_limit)
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand

    if D < 3 or best[0] >= lib.moore_bound(d, D):
        return best

    # New search: C vertex insertion with annealed degree-preserving edge repair,
    # started from the best construction. Leave margin for compile and I/O.
    elapsed = time.monotonic() - t_start
    remaining = time_limit - elapsed - 6.0
    budget = min(0.8 * time_limit, remaining)
    if budget < 1.0:
        return best
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=best, timeout=remaining)
        n, edges = lib.parse_graph_text(out)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError):
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
