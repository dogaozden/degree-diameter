import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy (bold change from parent):
#   1. Build the strongest algebraic start graph available in Python: arc-extended
#      projective-plane incidence graphs for D >= 3, the W(q) generalized quadrangle
#      for D >= 4, and K_{d,d} as a safe fallback for D >= 2.
#   2. Hand that graph to a C engine that performs simulated annealing with
#      degree-preserving-or-reducing edge moves. The cost is the number of ordered
#      vertex pairs at distance > D, computed with bitset ball expansion. Whenever a
#      valid graph is reached, the engine snapshots it and adds one new vertex
#      (attached by later moves), so it grows the order while staying valid.
#   3. Python validates the returned graph and keeps the best valid graph seen.
#
# The voltage-lift annealing from the parent is removed in favour of this direct
# vertex-growth search. Cases already at the Moore bound skip the search.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXD 64
#define MAXW (MAXN / 64)

static int N, CAP, DIAM;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int side[MAXN];
static uint64_t BUF1[MAXN][MAXW];
static uint64_t BUF2[MAXN][MAXW];

static int bestN = 0;
static int bestDeg[MAXN];
static int bestAdj[MAXN][MAXD];

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc64(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int has_edge(int a, int b) {
    int k;
    for (k = 0; k < deg[a]; k++) if (adj[a][k] == b) return 1;
    return 0;
}

static void raw_remove_one(int a, int c) {
    int k;
    for (k = 0; k < deg[a]; k++) {
        if (adj[a][k] == c) {
            adj[a][k] = adj[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}
static void raw_add(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}
static void raw_remove(int a, int b) {
    raw_remove_one(a, b);
    raw_remove_one(b, a);
}

typedef struct { int add, a, b; } Op;
static Op oplog[8];
static int nops = 0;

static void op_add(int a, int b) {
    raw_add(a, b);
    oplog[nops].add = 1; oplog[nops].a = a; oplog[nops].b = b;
    nops++;
}
static void op_remove(int a, int b) {
    raw_remove(a, b);
    oplog[nops].add = 0; oplog[nops].a = a; oplog[nops].b = b;
    nops++;
}
static void undo_ops(void) {
    while (nops > 0) {
        nops--;
        if (oplog[nops].add) raw_remove(oplog[nops].a, oplog[nops].b);
        else raw_add(oplog[nops].a, oplog[nops].b);
    }
}

/* Number of ordered pairs (v, w) with dist(v, w) > DIAM (0 means valid). */
static long long eval_cost(void) {
    int W = (N + 63) >> 6;
    int v, w, it, k;
    for (v = 0; v < N; v++) {
        for (w = 0; w < W; w++) BUF1[v][w] = 0;
        BUF1[v][v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t (*cur)[MAXW] = BUF1;
    uint64_t (*nxt)[MAXW] = BUF2;
    for (it = 0; it < DIAM; it++) {
        for (v = 0; v < N; v++) {
            uint64_t *o = nxt[v];
            for (w = 0; w < W; w++) o[w] = cur[v][w];
            for (k = 0; k < deg[v]; k++) {
                const uint64_t *s = cur[adj[v][k]];
                for (w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (v = 0; v < N; v++) {
        int c = 0;
        for (w = 0; w < W; w++) c += popc64(cur[v][w]);
        bad += N - c;
    }
    return bad;
}

static void snapshot(void) {
    int v;
    bestN = N;
    for (v = 0; v < N; v++) {
        bestDeg[v] = deg[v];
        memcpy(bestAdj[v], adj[v], sizeof(int) * (size_t)deg[v]);
    }
}

static int qbuf[MAXN];
static void color_sides(void) {
    int i, k;
    for (i = 0; i < N; i++) side[i] = -1;
    for (i = 0; i < N; i++) {
        if (side[i] != -1) continue;
        int h = 0, t = 0;
        side[i] = 0;
        qbuf[t++] = i;
        while (h < t) {
            int u = qbuf[h++];
            for (k = 0; k < deg[u]; k++) {
                int w = adj[u][k];
                if (side[w] == -1) {
                    side[w] = 1 - side[u];
                    qbuf[t++] = w;
                }
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (d < 1 || d > MAXD || DIAM < 1) return 1;
    CAP = d;
    rs = seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    int n0, m0, i;
    if (scanf("%d %d", &n0, &m0) != 2) return 1;
    if (n0 < 0 || n0 > MAXN - 8 || m0 < 0) return 1;
    N = n0;
    for (i = 0; i < N; i++) deg[i] = 0;
    for (i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (deg[u] >= CAP || deg[v] >= CAP || has_edge(u, v)) continue;
        raw_add(u, v);
    }
    if (N == 0) {
        printf("0 0\n");
        return 0;
    }
    color_sides();
    snapshot();

    clock_t c0 = clock();
    long long cur = eval_cost();
    double T = 3.0;
    long long stage_it = 0;
    long long it = 0;
    for (;;) {
        if ((it & 63) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el > budget) break;
        }
        it++;
        if (cur == 0) {
            snapshot();
            if (N + 1 >= MAXN) break;
            side[N] = rndint(2);
            deg[N] = 0;
            N++;
            T = 3.0;
            stage_it = 0;
            cur = eval_cost();
            continue;
        }
        stage_it++;
        T *= 0.9996;
        if (T < 0.2) T = 0.2;
        if (stage_it % 40000 == 0) T = 2.0;

        int x = rndint(N);
        int b = -1;
        int tr;
        for (tr = 0; tr < 64; tr++) {
            int c = rndint(N);
            if (side[c] != side[x] && !has_edge(x, c)) {
                b = c;
                break;
            }
        }
        if (b < 0) continue;

        nops = 0;
        if (deg[x] >= CAP) {
            int c = adj[x][rndint(deg[x])];
            op_remove(x, c);
        }
        if (deg[b] >= CAP) {
            int a = adj[b][rndint(deg[b])];
            op_remove(a, b);
        }
        op_add(x, b);

        long long nc = eval_cost();
        long long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            undo_ops();
        }
    }
    if (cur == 0) snapshot();

    long long m = 0;
    int v, k;
    for (v = 0; v < bestN; v++)
        for (k = 0; k < bestDeg[v]; k++)
            if (v < bestAdj[v][k]) m++;
    printf("%d %lld\n", bestN, m);
    for (v = 0; v < bestN; v++)
        for (k = 0; k < bestDeg[v]; k++)
            if (v < bestAdj[v][k]) printf("%d %d\n", v, bestAdj[v][k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1, so
# with d >= q+1 it has spare s = d - q - 1. New A-vertices attach to the q+1 lines
# through a chosen point set SA (each line hit by <= s points), and new B-vertices
# attach to the q+1 points on a chosen line set SB (each point hit by <= s lines).
# ----------------------------------------------------------------------------

_LS_ITERS = 30000


def _pg_data(q):
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


def _local_search(m, s, nbr, S, rng, deadline, iters):
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
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
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
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total_deadline = start + 0.88 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Algebraic starts.
    if D >= 3 and d >= 2:
        try:
            cands = _arc_extensions(d, start + 0.2 * time_limit,
                                    random.Random(seed * 7919 + d))
            for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
                consider(n_c, e_c)
        except Exception:
            pass
    if D >= 4:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

    # Already at the Moore bound: nothing to gain, return immediately.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Vertex-growth annealing in C, started from the best algebraic graph.
    avail = total_deadline - time.monotonic()
    budget = avail - 3.0
    if budget >= 1.0 and best_n >= 2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                             stdin_graph=best, timeout=avail)
            n2, e2 = lib.parse_graph_text(text)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
