"""Vertex insertion with annealed repair, seeded from the best algebraic construction.

Start: the largest valid graph among projective-plane arc extensions (D >= 3),
the generalized quadrangle W(q) (D >= 4), and K_{d,d} as a safe fallback.

Search (C engine): repeatedly add one vertex to the current valid graph, attach it
to spare or stolen slots, then anneal on the number of vertex pairs at distance > D.
Moves are degree-preserving 2-switches, edge additions and rewires between spare
vertices, and edge removals. Bipartiteness is kept by only joining opposite sides.
Each attempt either reaches cost zero (accepted as the new state) or is rolled back
to the last valid snapshot. Reachability uses 64-bit bitsets, so each cost evaluation
is cheap.
"""
import itertools
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1536
#define MAXW 24
#define MAXDEG 64
#define ITERS 4000

static int N = 0, Dg = 0, Dist = 0, W = 0;
static int side_of[MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXDEG];
static int slist[2][MAXN];
static int scnt[2];
static uint64_t BA[MAXN][MAXW];
static uint64_t BB[MAXN][MAXW];
static uint64_t rng_s = 88172645463325252ULL;
static long long clk_limit = 0;

typedef struct { int t, a, b; } Op;
static Op oplog[32];
static int nops = 0;

static int sN = 0, sC[2];
static int sdeg[MAXN];
static int snb[MAXN][MAXDEG];

static uint64_t rnd64(void) {
    rng_s ^= rng_s >> 12;
    rng_s ^= rng_s << 25;
    rng_s ^= rng_s >> 27;
    return rng_s * 2685821657736338717ULL;
}

static int rndint(int n) {
    if (n <= 0) return 0;
    return (int)(rnd64() % (uint64_t)n);
}

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int timeup(void) {
    return (long long)clock() >= clk_limit;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int is_adj(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (nb[a][i] == b) return 1;
    return 0;
}

static void add_arc(int a, int b) { nb[a][deg[a]++] = b; }

static void del_arc(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (nb[a][i] == b) {
            nb[a][i] = nb[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void add_edge(int a, int b) { add_arc(a, b); add_arc(b, a); }
static void del_edge(int a, int b) { del_arc(a, b); del_arc(b, a); }

static void op_add(int a, int b) {
    add_edge(a, b);
    oplog[nops].t = 0; oplog[nops].a = a; oplog[nops].b = b; nops++;
}

static void op_del(int a, int b) {
    del_edge(a, b);
    oplog[nops].t = 1; oplog[nops].a = a; oplog[nops].b = b; nops++;
}

static void undo_ops(void) {
    while (nops > 0) {
        nops--;
        Op o = oplog[nops];
        if (o.t == 0) del_edge(o.a, o.b);
        else add_edge(o.a, o.b);
    }
}

/* Number of unordered vertex pairs at distance > Dist (0 means valid). */
static long long cost_of(void) {
    uint64_t (*cur)[MAXW] = BA;
    uint64_t (*nxt)[MAXW] = BB;
    for (int v = 0; v < N; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * (size_t)W);
        cur[v][v >> 6] |= (uint64_t)1 << (v & 63);
    }
    for (int r = 0; r < Dist; r++) {
        for (int v = 0; v < N; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = cur[nb[v][i]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(cur[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

/* Uniform random vertex on side s with spare degree, or -1. */
static int pick_spare(int s) {
    int chosen = -1, seen = 0;
    for (int i = 0; i < scnt[s]; i++) {
        int v = slist[s][i];
        if (deg[v] < Dg) {
            seen++;
            if (rndint(seen) == 0) chosen = v;
        }
    }
    return chosen;
}

static int move_switch(void) {
    if (scnt[0] < 2) return 0;
    int a1 = slist[0][rndint(scnt[0])];
    int a2 = slist[0][rndint(scnt[0])];
    if (a1 == a2 || deg[a1] == 0 || deg[a2] == 0) return 0;
    int b1 = nb[a1][rndint(deg[a1])];
    int b2 = nb[a2][rndint(deg[a2])];
    if (b1 == b2) return 0;
    if (is_adj(a1, b2) || is_adj(a2, b1)) return 0;
    op_del(a1, b1);
    op_del(a2, b2);
    op_add(a1, b2);
    op_add(a2, b1);
    return 1;
}

static int move_add(void) {
    int a = pick_spare(0);
    int b = pick_spare(1);
    if (a < 0 || b < 0 || is_adj(a, b)) return 0;
    op_add(a, b);
    return 1;
}

static int move_rewire(void) {
    int s = rndint(2);
    if (scnt[s] == 0) return 0;
    int x = slist[s][rndint(scnt[s])];
    if (deg[x] == 0) return 0;
    int y = nb[x][rndint(deg[x])];
    int z = pick_spare(1 - s);
    if (z < 0 || z == y || is_adj(x, z)) return 0;
    op_del(x, y);
    op_add(x, z);
    return 1;
}

static int move_remove(void) {
    int s = rndint(2);
    if (scnt[s] == 0) return 0;
    int x = slist[s][rndint(scnt[s])];
    if (deg[x] == 0) return 0;
    int y = nb[x][rndint(deg[x])];
    op_del(x, y);
    return 1;
}

/* Annealing from the current state. Returns 1 if cost reaches zero. */
static int anneal(int iters, double T0) {
    long long cost = cost_of();
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 127) == 0 && timeup()) break;
        double T = T0 * (1.0 - (double)it / (double)iters) + 0.05;
        nops = 0;
        int r = rndint(100);
        int ok;
        if (r < 40) ok = move_switch();
        else if (r < 70) ok = move_add();
        else if (r < 97) ok = move_rewire();
        else ok = move_remove();
        if (!ok) continue;
        long long c2 = cost_of();
        long long delta = c2 - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cost = c2;
        } else {
            undo_ops();
        }
        nops = 0;
    }
    return cost == 0;
}

/* Append a vertex on side s, attach it to up to Dg opposite vertices
   (spare ones first, otherwise steal one edge from a full vertex). */
static int add_vertex(int s) {
    if (N >= MAXN) return 0;
    int v = N++;
    W = (N + 63) >> 6;
    side_of[v] = s;
    deg[v] = 0;
    slist[s][scnt[s]++] = v;
    int t = 1 - s;
    for (int k = 0; k < Dg && deg[v] < Dg; k++) {
        int u = pick_spare(t);
        if (u >= 0 && !is_adj(v, u)) {
            add_edge(v, u);
            continue;
        }
        if (scnt[t] == 0) break;
        int u2 = -1;
        for (int tries = 0; tries < 50 && u2 < 0; tries++) {
            int c = slist[t][rndint(scnt[t])];
            if (deg[c] >= Dg && !is_adj(v, c)) u2 = c;
        }
        if (u2 < 0) break;
        int w = nb[u2][rndint(deg[u2])];
        del_edge(u2, w);
        add_edge(v, u2);
    }
    return 1;
}

static void take_snapshot(void) {
    sN = N;
    sC[0] = scnt[0];
    sC[1] = scnt[1];
    for (int v = 0; v < N; v++) {
        sdeg[v] = deg[v];
        memcpy(snb[v], nb[v], sizeof(int) * (size_t)deg[v]);
    }
}

static void restore_snapshot(void) {
    N = sN;
    W = (N + 63) >> 6;
    scnt[0] = sC[0];
    scnt[1] = sC[1];
    for (int v = 0; v < N; v++) {
        deg[v] = sdeg[v];
        memcpy(nb[v], snb[v], sizeof(int) * (size_t)deg[v]);
    }
}

static int color_graph(int n) {
    int *q = malloc(sizeof(int) * (size_t)n);
    if (!q) return 0;
    for (int v = 0; v < n; v++) side_of[v] = -1;
    for (int s0 = 0; s0 < n; s0++) {
        if (side_of[s0] >= 0) continue;
        side_of[s0] = 0;
        int h = 0, tl = 0;
        q[tl++] = s0;
        while (h < tl) {
            int x = q[h++];
            for (int i = 0; i < deg[x]; i++) {
                int y = nb[x][i];
                if (side_of[y] < 0) {
                    side_of[y] = 1 - side_of[x];
                    q[tl++] = y;
                } else if (side_of[y] == side_of[x]) {
                    free(q);
                    return 0;
                }
            }
        }
    }
    free(q);
    return 1;
}

static void echo_input(int n, int m, const int *eu, const int *ev) {
    printf("%d %d\n", n, m);
    for (int i = 0; i < m; i++) printf("%d %d\n", eu[i], ev[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dg = atoi(argv[1]);
    Dist = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rng_s ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (rng_s == 0) rng_s = 1;
    clk_limit = (long long)clock() + (long long)(tl * (double)CLOCKS_PER_SEC);

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0) {
        printf("0 0\n");
        return 0;
    }
    if (m < 0) m = 0;
    int *eu = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    int *ev = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    int read = 0;
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) break;
        read++;
    }
    m = read;

    int bad = (n > MAXN || Dg < 1 || Dg > MAXDEG - 1 || Dist < 1);
    if (!bad) {
        N = n;
        W = (N + 63) >> 6;
        for (int v = 0; v < N; v++) deg[v] = 0;
        for (int i = 0; i < m && !bad; i++) {
            int u = eu[i], v = ev[i];
            if (u < 0 || v < 0 || u >= n || v >= n || u == v) { bad = 1; break; }
            if (deg[u] >= Dg || deg[v] >= Dg) { bad = 1; break; }
            if (is_adj(u, v)) { bad = 1; break; }
            add_edge(u, v);
        }
    }
    if (!bad) {
        if (!color_graph(n)) bad = 1;
    }
    if (!bad) {
        scnt[0] = scnt[1] = 0;
        for (int v = 0; v < N; v++) slist[side_of[v]][scnt[side_of[v]]++] = v;
        if (cost_of() != 0) bad = 1;
    }
    if (bad) {
        echo_input(n, m, eu, ev);
        return 0;
    }

    take_snapshot();
    while (!timeup() && N < MAXN) {
        restore_snapshot();
        int s = rndint(2);
        if (!add_vertex(s)) break;
        if (anneal(ITERS, 2.0)) take_snapshot();
    }
    restore_snapshot();

    int M = 0;
    for (int v = 0; v < N; v++)
        for (int i = 0; i < deg[v]; i++)
            if (nb[v][i] > v) M++;
    printf("%d %d\n", N, M);
    for (int v = 0; v < N; v++)
        for (int i = 0; i < deg[v]; i++)
            if (nb[v][i] > v) printf("%d %d\n", v, nb[v][i]);
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
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice of elements so that every target is hit by <= s chosen elements."""
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
# Generalized quadrangle W(q) (diameter 4).
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
# Build: best algebraic start, then C vertex insertion with annealed repair.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
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

    if D >= 3:
        rng = random.Random(seed * 7919 + d)
        deadline = t_start + 0.15 * time_limit
        for n_c, e_c in _arc_extensions(d, deadline, rng):
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < t_start + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # C search from the best valid start. Leave margin for compilation and startup.
    if D >= 2 and 1 <= d <= 60:
        elapsed = time.monotonic() - t_start
        c_budget = 0.80 * time_limit - elapsed - 3.0
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed % 2147483647, f"{c_budget:.2f}"],
                                 stdin_graph=best,
                                 timeout=max(1.0, 0.92 * time_limit - elapsed))
                n_c, e_c = lib.parse_graph_text(text)
                consider(n_c, e_c)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
