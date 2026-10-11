import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: the arc-extended PG(2,q) start graph is kept as the base, but
# growth is now done by a C engine instead of voltage lifts. The C engine keeps
# the bipartition fixed, adds one vertex at a time and anneals the edge set
# (attach, degree-preserving double swaps, endpoint moves) to minimise the
# number of ordered vertex pairs at distance > D. Every accepted state with
# cost 0 is a valid graph, so the output is always checked with lib.is_valid
# and the Python side keeps the best valid graph it already has.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define NLIM 4000
#define WCAP 64

typedef uint64_t u64;

static int dd = 1;
static int DIST = 3;
static int N = 0;
static int W = 1;
static int *adjm = NULL;
static int *badj = NULL;
static int deg[NLIM];
static int bdeg[NLIM];
static int side[NLIM];
static int bside[NLIM];
static int bN = 0;
static int sv[2][NLIM];
static int ns[2];
static u64 *RA = NULL;
static u64 *RB = NULL;
static u64 rs = 88172645463325252ULL;
static double tlimit = 10.0;
static clock_t t_start;

typedef struct { int u, v, t; } op_t;
static op_t ops[64];
static int nops = 0;

static u64 rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) {
    if (n <= 1) return 0;
    return (int)(rnd() % (u64)n);
}

static double rnd01(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static double elapsed(void) {
    return (double)(clock() - t_start) / CLOCKS_PER_SEC;
}

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    const int *a = adjm + (size_t)u * dd;
    for (int k = 0; k < deg[u]; k++) if (a[k] == v) return 1;
    return 0;
}

static void raw_del1(int u, int v) {
    int *a = adjm + (size_t)u * dd;
    for (int k = 0; k < deg[u]; k++) {
        if (a[k] == v) {
            a[k] = a[deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void raw_add(int u, int v) {
    adjm[(size_t)u * dd + deg[u]++] = v;
    adjm[(size_t)v * dd + deg[v]++] = u;
}

static void raw_del(int u, int v) {
    raw_del1(u, v);
    raw_del1(v, u);
}

static void add_e(int u, int v) {
    raw_add(u, v);
    ops[nops].u = u; ops[nops].v = v; ops[nops].t = 1;
    nops++;
}

static void del_e(int u, int v) {
    raw_del(u, v);
    ops[nops].u = u; ops[nops].v = v; ops[nops].t = -1;
    nops++;
}

static void undo_all(void) {
    while (nops > 0) {
        nops--;
        if (ops[nops].t == 1) raw_del(ops[nops].u, ops[nops].v);
        else raw_add(ops[nops].u, ops[nops].v);
    }
}

static long long cost_eval(void) {
    u64 *cur = RA, *nxt = RB;
    size_t wn = (size_t)W;
    memset(RA, 0, sizeof(u64) * (size_t)N * wn);
    for (int v = 0; v < N; v++) RA[(size_t)v * wn + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIST; r++) {
        for (int v = 0; v < N; v++) {
            u64 *out = nxt + (size_t)v * wn;
            const u64 *self = cur + (size_t)v * wn;
            memcpy(out, self, sizeof(u64) * wn);
            const int *a = adjm + (size_t)v * dd;
            for (int k = 0; k < deg[v]; k++) {
                const u64 *src = cur + (size_t)a[k] * wn;
                for (size_t w = 0; w < wn; w++) out[w] |= src[w];
            }
        }
        u64 *t = cur; cur = nxt; nxt = t;
    }
    long long reach = 0;
    for (int v = 0; v < N; v++) {
        const u64 *p = cur + (size_t)v * wn;
        for (size_t w = 0; w < wn; w++) reach += popc(p[w]);
    }
    return (long long)N * N - reach;
}

static int pick_deficient(int s) {
    int c = ns[s];
    if (c == 0) return -1;
    for (int t = 0; t < 8; t++) {
        int x = sv[s][rndint(c)];
        if (deg[x] < dd) return x;
    }
    int off = rndint(c);
    for (int t = 0; t < c; t++) {
        int x = sv[s][(off + t) % c];
        if (deg[x] < dd) return x;
    }
    return -1;
}

static int pick_nonempty(int s) {
    int c = ns[s];
    if (c == 0) return -1;
    for (int t = 0; t < 8; t++) {
        int x = sv[s][rndint(c)];
        if (deg[x] > 0) return x;
    }
    int off = rndint(c);
    for (int t = 0; t < c; t++) {
        int x = sv[s][(off + t) % c];
        if (deg[x] > 0) return x;
    }
    return -1;
}

static int move_attach(void) {
    for (int t = 0; t < 4; t++) {
        int u = pick_deficient(0);
        int v = pick_deficient(1);
        if (u < 0 || v < 0) return 0;
        if (!has_edge(u, v)) {
            add_e(u, v);
            return 1;
        }
    }
    return 0;
}

static int move_swap(void) {
    int a = pick_nonempty(0);
    int c = pick_nonempty(0);
    if (a < 0 || c < 0 || a == c) return 0;
    int b = adjm[(size_t)a * dd + rndint(deg[a])];
    int e = adjm[(size_t)c * dd + rndint(deg[c])];
    if (b == e) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    del_e(a, b);
    del_e(c, e);
    add_e(a, e);
    add_e(c, b);
    return 1;
}

static int move_endpoint(void) {
    int s = rndint(2);
    int a = pick_nonempty(s);
    if (a < 0) return 0;
    int b = adjm[(size_t)a * dd + rndint(deg[a])];
    int x = pick_deficient(s);
    if (x < 0 || x == a) return 0;
    if (has_edge(x, b)) return 0;
    del_e(a, b);
    add_e(x, b);
    return 1;
}

static int anneal(long long budget, double T0) {
    long long cur = cost_eval();
    if (cur == 0) return 1;
    for (long long it = 0; it < budget; it++) {
        if ((it & 127) == 0 && elapsed() > tlimit) return 0;
        double T = T0 * (1.0 - (double)it / (double)budget) + 0.05;
        int r = rndint(100);
        int ok;
        nops = 0;
        if (r < 35) ok = move_attach();
        else if (r < 70) ok = move_swap();
        else ok = move_endpoint();
        if (!ok) {
            nops = 0;
            continue;
        }
        long long nw = cost_eval();
        long long delta = nw - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nw;
            nops = 0;
            if (cur == 0) return 1;
        } else {
            undo_all();
        }
    }
    return cur == 0;
}

static void save_best(void) {
    bN = N;
    memcpy(bdeg, deg, sizeof(int) * (size_t)N);
    memcpy(bside, side, sizeof(int) * (size_t)N);
    memcpy(badj, adjm, sizeof(int) * (size_t)N * dd);
}

static void restore_best(void) {
    N = bN;
    memcpy(deg, bdeg, sizeof(int) * (size_t)N);
    memcpy(side, bside, sizeof(int) * (size_t)N);
    memcpy(adjm, badj, sizeof(int) * (size_t)N * dd);
    ns[0] = 0;
    ns[1] = 0;
    for (int v = 0; v < N; v++) sv[side[v]][ns[side[v]]++] = v;
    W = (N + 63) / 64;
}

static void add_vertex(int s) {
    int v = N;
    N++;
    W = (N + 63) / 64;
    deg[v] = 0;
    side[v] = s;
    sv[s][ns[s]++] = v;
}

static void print_best(void) {
    long long tot = 0;
    for (int v = 0; v < bN; v++) tot += bdeg[v];
    printf("%d %lld\n", bN, tot / 2);
    for (int v = 0; v < bN; v++) {
        for (int k = 0; k < bdeg[v]; k++) {
            int u = badj[(size_t)v * dd + k];
            if (v < u) printf("%d %d\n", v, u);
        }
    }
}

int main(int argc, char **argv) {
    t_start = clock();
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    tlimit = atof(argv[4]);
    dd = d < 1 ? 1 : d;
    DIST = D < 1 ? 1 : D;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 0) n = 0;
    if (n >= NLIM - 2) {
        printf("0 0\n");
        return 0;
    }
    adjm = malloc(sizeof(int) * (size_t)NLIM * dd);
    badj = malloc(sizeof(int) * (size_t)NLIM * dd);
    RA = malloc(sizeof(u64) * (size_t)NLIM * WCAP);
    RB = malloc(sizeof(u64) * (size_t)NLIM * WCAP);
    if (!adjm || !badj || !RA || !RB) return 1;

    N = (n == 0) ? 2 : n;
    W = (N + 63) / 64;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (deg[u] >= dd || deg[v] >= dd || has_edge(u, v)) continue;
        raw_add(u, v);
    }
    if (n == 0) raw_add(0, 1);

    int *queue = malloc(sizeof(int) * (size_t)N);
    for (int v = 0; v < N; v++) side[v] = -1;
    int bip = 1;
    for (int s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int head = 0, tail = 0;
        queue[tail++] = s;
        while (head < tail) {
            int x = queue[head++];
            for (int k = 0; k < deg[x]; k++) {
                int y = adjm[(size_t)x * dd + k];
                if (side[y] == -1) {
                    side[y] = 1 - side[x];
                    queue[tail++] = y;
                } else if (side[y] == side[x]) {
                    bip = 0;
                }
            }
        }
    }
    free(queue);

    save_best();
    if (!bip) {
        print_best();
        return 0;
    }

    int fails = 0;
    while (elapsed() < tlimit && N + 1 < NLIM) {
        restore_best();
        int s;
        if (ns[0] < ns[1]) s = 0;
        else if (ns[1] < ns[0]) s = 1;
        else s = rndint(2);
        add_vertex(s);
        long long budget = 20000 + 1000LL * (fails < 30 ? fails : 30);
        if (anneal(budget, 3.0)) {
            save_best();
            fails = 0;
        } else {
            fails++;
        }
    }
    print_best();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
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
    """True if every target t is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements so that every target is hit by <= s chosen elements."""
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
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
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
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    # Diameter-3 start: largest valid arc-extended projective plane graph.
    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.2 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
                best = (n_c, e_c)
                break

    # Diameter-4 start from the generalized quadrangle.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None and gq[0] > best[0] and lib.is_valid(gq[0], gq[1], d, D):
            best = gq

    # Let the C engine grow the best start by adding vertices and annealing.
    remaining = time_limit - (time.monotonic() - t0)
    budget = 0.85 * remaining - 2.0
    if budget >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"], stdin_graph=best,
                            timeout=max(1.0, remaining - 3.0))
            n, e = lib.parse_graph_text(out)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
