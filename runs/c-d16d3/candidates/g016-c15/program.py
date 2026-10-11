import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy
#
# 1. Safe baselines in Python (always validated with lib.is_valid):
#    K_{d,d} (diameter 2), arc-extended projective plane graphs (diameter 3),
#    and the generalized quadrangle W(q) (diameter 4).
#
# 2. A substantially different search, in C. It does not extend a known
#    algebraic object. It treats the bipartite graph as a covering problem:
#    every pair of same-side vertices needs a common neighbour (distance 2),
#    and cross pairs need distance <= 3. The C engine keeps a simple bipartite
#    graph with max degree d, grows the vertex count one vertex at a time,
#    and runs simulated annealing on the number of pairs at distance > D.
#    Moves are edge add, edge remove, endpoint move and degree-preserving
#    double swap. Distances are computed with bitsets for every vertex.
#    When the cost reaches zero the graph is valid, so it is saved and the
#    search grows again. If the search stalls, it restarts from the best graph.
#
# 3. build() returns the largest validated graph among these candidates.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXW (MAXN / 64)
#define MAXDEG 64
#define MAXE (MAXN * MAXDEG / 2)

static int N, Nhigh, Dd, Dist;
static int deg[MAXN];
static int nb[MAXN][MAXDEG];
static unsigned char M[MAXN][MAXN];
static int side[MAXN];
static uint64_t RA[MAXN][MAXW], RB[MAXN][MAXW];
static uint64_t rs;
static int BN, BM;
static int BU[MAXE], BV[MAXE];
static int BSide[MAXN];

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndd(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int a, int b) {
    M[a][b] = 1;
    M[b][a] = 1;
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void del_one(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (nb[a][i] == b) {
            nb[a][i] = nb[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void del_edge(int a, int b) {
    M[a][b] = 0;
    M[b][a] = 0;
    del_one(a, b);
    del_one(b, a);
}

/* Number of ordered pairs (v,w) with dist(v,w) > Dist. Zero means valid. */
static long cost_full(void) {
    int W = (N + 63) / 64;
    uint64_t (*cur)[MAXW] = RA, (*nxt)[MAXW] = RB, (*tmp)[MAXW];
    for (int v = 0; v < N; v++) {
        for (int j = 0; j < W; j++) cur[v][j] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < Dist; s++) {
        for (int v = 0; v < N; v++) {
            for (int j = 0; j < W; j++) nxt[v][j] = cur[v][j];
            for (int k = 0; k < deg[v]; k++) {
                int u = nb[v][k];
                for (int j = 0; j < W; j++) nxt[v][j] |= cur[u][j];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long c = 0;
    for (int v = 0; v < N; v++) {
        int cnt = 0;
        for (int j = 0; j < W; j++) cnt += popc(cur[v][j]);
        c += N - cnt;
    }
    return c;
}

static void save_best(void) {
    BN = N;
    BM = 0;
    for (int a = 0; a < N; a++) {
        for (int k = 0; k < deg[a]; k++) {
            int b = nb[a][k];
            if (a < b && BM < MAXE) {
                BU[BM] = a;
                BV[BM] = b;
                BM++;
            }
        }
    }
    for (int v = 0; v < N; v++) BSide[v] = side[v];
}

static void reload(void) {
    for (int a = 0; a < Nhigh; a++) {
        deg[a] = 0;
        for (int b = 0; b < Nhigh; b++) M[a][b] = 0;
    }
    N = BN;
    for (int v = 0; v < N; v++) side[v] = BSide[v];
    for (int i = 0; i < BM; i++) add_edge(BU[i], BV[i]);
    if (N > Nhigh) Nhigh = N;
}

static int accept(long dl, double T) {
    if (dl <= 0) return 1;
    return rndd() < exp(-(double)dl / T);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    Dist = atoi(argv[2]);
    rs = (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (!rs) rs = 1;
    double budget = atof(argv[4]);
    if (Dd < 1 || Dd > MAXDEG || Dist < 1) {
        printf("0 0\n");
        return 0;
    }
    clock_t tend = clock() + (clock_t)(budget * CLOCKS_PER_SEC);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    int ok = 1;
    if (n0 > 0 && n0 <= MAXN) {
        N = n0;
        for (int i = 0; i < m0; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
            if (u < 0 || v < 0 || u >= N || v >= N || u == v || M[u][v] ||
                deg[u] >= Dd || deg[v] >= Dd) {
                ok = 0;
                break;
            }
            add_edge(u, v);
        }
    } else {
        ok = 0;
    }
    if (ok) {
        static int col[MAXN];
        static int stk[MAXN];
        int bip = 1;
        for (int v = 0; v < N; v++) col[v] = -1;
        for (int s = 0; s < N; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int sp = 0;
            stk[sp++] = s;
            while (sp) {
                int u = stk[--sp];
                for (int k = 0; k < deg[u]; k++) {
                    int w = nb[u][k];
                    if (col[w] < 0) {
                        col[w] = 1 - col[u];
                        stk[sp++] = w;
                    } else if (col[w] == col[u]) {
                        bip = 0;
                    }
                }
            }
        }
        if (!bip) ok = 0;
        else for (int v = 0; v < N; v++) side[v] = col[v];
    }
    if (!ok) {
        memset(M, 0, sizeof(M));
        memset(deg, 0, sizeof(deg));
        N = 2 * Dd;
        if (N > MAXN) {
            printf("0 0\n");
            return 0;
        }
        for (int v = 0; v < N; v++) side[v] = (v < Dd) ? 0 : 1;
        for (int a = 0; a < Dd; a++)
            for (int b = Dd; b < 2 * Dd; b++) add_edge(a, b);
    }

    Nhigh = N;
    BN = 0;
    BM = 0;
    long cost = cost_full();
    if (cost == 0) save_best();

    double T = 2.0;
    long since = 0;
    const long LIM = 150000;
    while (clock() < tend) {
        if (cost == 0) {
            if (N > BN) save_best();
            if (N >= MAXN) break;
            int c0 = 0;
            for (int v = 0; v < N; v++) if (side[v] == 0) c0++;
            side[N] = (2 * c0 <= N) ? 0 : 1;
            deg[N] = 0;
            N++;
            if (N > Nhigh) Nhigh = N;
            cost = cost_full();
            T = 2.0;
            since = 0;
            continue;
        }
        if (since > LIM) {
            if (BN == 0) break;
            reload();
            cost = cost_full();
            T = 2.0;
            since = 0;
            continue;
        }
        since++;
        T *= 0.99997;
        if (T < 0.3) T = 0.3;

        int kind = rndi(100);
        if (kind < 25) {
            /* add an edge between two deficient vertices on opposite sides */
            int a = rndi(N), b = rndi(N);
            if (side[a] == side[b] || M[a][b] || deg[a] >= Dd || deg[b] >= Dd) continue;
            add_edge(a, b);
            long c2 = cost_full();
            if (accept(c2 - cost, T)) cost = c2;
            else del_edge(a, b);
        } else if (kind < 40) {
            /* remove an edge */
            int a = rndi(N);
            if (!deg[a]) continue;
            int b = nb[a][rndi(deg[a])];
            del_edge(a, b);
            long c2 = cost_full();
            if (accept(c2 - cost, T)) cost = c2;
            else add_edge(a, b);
        } else if (kind < 70) {
            /* endpoint move: (a,b) -> (a,x), x on b's side with spare degree */
            int a = rndi(N);
            if (!deg[a]) continue;
            int b = nb[a][rndi(deg[a])];
            int x = rndi(N);
            if (side[x] != side[b] || x == b || M[a][x] || deg[x] >= Dd) continue;
            del_edge(a, b);
            add_edge(a, x);
            long c2 = cost_full();
            if (accept(c2 - cost, T)) cost = c2;
            else {
                del_edge(a, x);
                add_edge(a, b);
            }
        } else {
            /* degree-preserving double swap across the bipartition */
            int a1 = rndi(N), a2 = rndi(N);
            if (side[a1] != 0 || side[a2] != 0 || a1 == a2 || !deg[a1] || !deg[a2]) continue;
            int b1 = nb[a1][rndi(deg[a1])];
            int b2 = nb[a2][rndi(deg[a2])];
            if (b1 == b2 || M[a1][b2] || M[a2][b1]) continue;
            del_edge(a1, b1);
            del_edge(a2, b2);
            add_edge(a1, b2);
            add_edge(a2, b1);
            long c2 = cost_full();
            if (accept(c2 - cost, T)) cost = c2;
            else {
                del_edge(a1, b2);
                del_edge(a2, b1);
                add_edge(a1, b1);
                add_edge(a2, b2);
            }
        }
    }

    printf("%d %d\n", BN, BM);
    for (int i = 0; i < BM; i++) printf("%d %d\n", BU[i], BV[i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python baselines
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
    """True if every target is hit by at most s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy selection with per-target load at most s."""
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
    """Conic (plus nucleus for even q) as a point-index set."""
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
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Diameter-3 algebraic baseline.
    if D >= 3 and d >= 3:
        for n_c, e_c in _arc_extensions(d, t0 + 0.2 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    # Diameter-4 baseline.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: covering-style annealing in C, started from the best valid graph.
    remain = time_limit - (time.monotonic() - t0)
    if d >= 4 and remain > 6.0:
        timeout = remain - 2.0
        budget = 0.85 * remain - 2.5
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=timeout)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
