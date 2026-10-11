import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 (Python): arc-extended projective plane incidence graphs, diameter 3.
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Old vertices have
# degree q+1, so each has spare s = d-q-1. Add an A-vertex for a set SA of points
# (joined to the q+1 lines through each point) and a B-vertex for a set SB of lines.
# Every line may carry at most s SA-points, every point at most s SB-lines.
# Diameter stays 3 for any such SA, SB.
#
# Stage 2 (C): a simulated-annealing "grow and repair" engine. It starts from the
# best valid graph and works on the bipartite graph directly:
#   * 2-switch moves (degree preserving, bipartite preserving) change the edges;
#   * add-vertex moves attach a new vertex of one side to up to d spare
#     vertices of the other side;
#   * the cost is the number of vertex pairs at distance > D (counted with
#     bitsets). Cost 0 means a valid graph, and the best valid graph is kept.
#   * after a long stagnation the state is reset to the best valid graph.
# Every output is re-checked with lib.is_valid; the fallback is K_{d,d}.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXD 64
#define WORDS 16

static int N = 0, DEG_MAX = 0, DIAM = 0;
static int nadj[MAXN][MAXD];
static int deg[MAXN];
static int side[MAXN];

static int bestN = 0;
static int bestDeg[MAXN];
static int bestAdj[MAXN][MAXD];
static int bestSide[MAXN];

static uint64_t RA[MAXN][WORDS];
static uint64_t RB[MAXN][WORDS];

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int is_adj(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (nadj[u][i] == v) return 1;
    return 0;
}
static void add_arc(int u, int v) { nadj[u][deg[u]++] = v; }
static void del_arc(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nadj[u][i] == v) {
            nadj[u][i] = nadj[u][--deg[u]];
            return;
        }
    }
}
static void add_edge(int u, int v) { add_arc(u, v); add_arc(v, u); }
static void del_edge(int u, int v) { del_arc(u, v); del_arc(v, u); }

/* Number of unordered pairs at distance > DIAM (unreachable counts too). */
static int cost_fn(void) {
    int W = (N + 63) >> 6;
    for (int v = 0; v < N; v++) {
        memset(RA[v], 0, sizeof(uint64_t) * (size_t)W);
        RA[v][v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t (*cur)[WORDS] = RA;
    uint64_t (*nxt)[WORDS] = RB;
    for (int s = 0; s < DIAM; s++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nxt[v];
            memcpy(dst, cur[v], sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = cur[nadj[v][i]];
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t (*t)[WORDS] = cur;
        cur = nxt;
        nxt = t;
    }
    long long total = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        total += N - c;
    }
    return (int)(total / 2);
}

static void save_best(void) {
    bestN = N;
    memcpy(bestDeg, deg, sizeof(int) * (size_t)N);
    memcpy(bestSide, side, sizeof(int) * (size_t)N);
    for (int v = 0; v < N; v++) memcpy(bestAdj[v], nadj[v], sizeof(int) * (size_t)deg[v]);
}

static void load_best(void) {
    N = bestN;
    memcpy(deg, bestDeg, sizeof(int) * (size_t)N);
    memcpy(side, bestSide, sizeof(int) * (size_t)N);
    for (int v = 0; v < N; v++) memcpy(nadj[v], bestAdj[v], sizeof(int) * (size_t)deg[v]);
}

static int color_graph(void) {
    static int queue[MAXN];
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int w = nadj[u][i];
                if (side[w] < 0) {
                    side[w] = 1 - side[u];
                    queue[qt++] = w;
                } else if (side[w] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void build_kdd(int d) {
    N = 2 * d;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < d; i++) {
        side[i] = 0;
        side[d + i] = 1;
    }
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            add_edge(i, d + j);
}

static int accept(int delta, double T) {
    if (delta <= 0) return 1;
    return rnd01() < exp(-(double)delta / T);
}

static void print_best(void) {
    load_best();
    long m = 0;
    for (int v = 0; v < N; v++)
        for (int i = 0; i < deg[v]; i++)
            if (nadj[v][i] > v) m++;
    printf("%d %ld\n", N, m);
    for (int v = 0; v < N; v++)
        for (int i = 0; i < deg[v]; i++)
            if (nadj[v][i] > v) printf("%d %d\n", v, nadj[v][i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (d < 1 || d > MAXD || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    DEG_MAX = d;
    rs = 88172645463325252ULL ^ (seed * 0x9E3779B97F4A7C15ULL + 12345ULL);
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    clock_t t0 = clock();

    /* Read the start graph (or "0 0"). */
    int n0 = 0, m0 = 0, ok = 1;
    if (scanf("%d %d", &n0, &m0) != 2) ok = 0;
    if (ok) {
        if (n0 < 1 || n0 > MAXN || m0 < 0) {
            ok = 0;
        } else {
            N = n0;
            for (int v = 0; v < N; v++) deg[v] = 0;
            for (int i = 0; i < m0 && ok; i++) {
                int u, v;
                if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
                if (u < 0 || u >= N || v < 0 || v >= N || u == v) { ok = 0; break; }
                if (deg[u] >= DEG_MAX || deg[v] >= DEG_MAX || is_adj(u, v)) { ok = 0; break; }
                add_edge(u, v);
            }
        }
    }
    if (ok && !color_graph()) ok = 0;
    if (ok && cost_fn() != 0) ok = 0;
    if (!ok) build_kdd(d);

    save_best();
    int cur = cost_fn();
    const double T = 0.5;
    const long long STAG = 4000;
    long long it = 0, lastImp = 0;
    static int cand[MAXN];

    for (;;) {
        if ((it & 63) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= budget) break;
        }
        it++;

        if (rndint(100) < 10) {
            /* Add-vertex move. */
            if (N >= MAXN) continue;
            int s = rndint(2);
            int nc = 0;
            for (int v = 0; v < N; v++)
                if (side[v] == 1 - s && deg[v] < DEG_MAX) cand[nc++] = v;
            if (nc == 0) continue;
            int k = nc < DEG_MAX ? nc : DEG_MAX;
            for (int i = 0; i < k; i++) {
                int j = i + rndint(nc - i);
                int tmp = cand[i];
                cand[i] = cand[j];
                cand[j] = tmp;
            }
            int x = N;
            N++;
            side[x] = s;
            deg[x] = 0;
            for (int i = 0; i < k; i++) add_edge(x, cand[i]);
            int nw = cost_fn();
            if (accept(nw - cur, T)) {
                cur = nw;
            } else {
                for (int i = 0; i < k; i++) del_edge(x, cand[i]);
                deg[x] = 0;
                N--;
            }
        } else {
            /* Bipartite 2-switch: (u0,u1),(c,e) -> (u0,e),(c,u1). */
            int a = rndint(N);
            if (deg[a] == 0) continue;
            int b = nadj[a][rndint(deg[a])];
            int u0 = (side[a] == 0) ? a : b;
            int u1 = (side[a] == 0) ? b : a;
            int c = rndint(N);
            if (side[c] != 0 || deg[c] == 0 || c == u0) continue;
            int e = nadj[c][rndint(deg[c])];
            if (is_adj(u0, e) || is_adj(c, u1)) continue;
            del_edge(u0, u1);
            del_edge(c, e);
            add_edge(u0, e);
            add_edge(c, u1);
            int nw = cost_fn();
            if (accept(nw - cur, T)) {
                cur = nw;
            } else {
                del_edge(u0, e);
                del_edge(c, u1);
                add_edge(u0, u1);
                add_edge(c, e);
            }
        }

        if (cur == 0 && N > bestN) {
            save_best();
            lastImp = it;
        }
        if (it - lastImp > STAG) {
            load_best();
            cur = cost_fn();
            lastImp = it;
        }
    }

    print_best();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions (arc extensions and generalized quadrangle baseline).
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
    """Randomized greedy selection with load bound s."""
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


def _local_side(m, s, nbr, S0, rng, deadline, iters=6000):
    """Plateau local search: insert, or swap out one blocking element."""
    if s < 1:
        return list(S0)
    inS = [False] * m
    load = [0] * m
    S = list(S0)
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            load[t] += 1
    best = list(S)
    for it in range(iters):
        if it % 256 == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        over = {t for t in nbr[x] if load[t] >= s}
        if not over:
            S.append(x)
            inS[x] = True
            for t in nbr[x]:
                load[t] += 1
            if len(S) > len(best):
                best = list(S)
            continue
        cand = [y for y in S if any(t in over for t in nbr[y])]
        if not cand:
            continue
        y = rng.choice(cand)
        for t in nbr[y]:
            load[t] -= 1
        if all(load[t] < s for t in nbr[x]):
            S.remove(y)
            inS[y] = False
            S.append(x)
            inS[x] = True
            for t in nbr[x]:
                load[t] += 1
        else:
            for t in nbr[y]:
                load[t] += 1
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

        SA = _local_side(m, s, point_lines, SA, rng, deadline)
        SB = _local_side(m, s, line_points, SB, rng, deadline)

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n_c, e_c))
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
# Build: Python constructions, then C grow-and-repair search from the best one.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    best = fallback

    if lib.moore_bound(d, D) <= best[0]:
        return best

    # Stage 1: Python constructions, at most about 15% of the time.
    deadline = t0 + 0.15 * time_limit
    rng = random.Random(seed * 7919 + d)
    cands = []
    if D >= 3:
        try:
            cands += _arc_extensions(d, deadline, rng)
        except Exception:
            pass
    if D >= 4 and time.monotonic() < deadline:
        try:
            gq = _best_gq(d)
            if gq is not None:
                cands.append(gq)
        except Exception:
            pass
    for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
        if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
            best = (n_c, e_c)
            break

    # Stage 2: C grow-and-repair search, leaving a safety margin.
    remaining = time_limit - (time.monotonic() - t0)
    budget = remaining - 7.0
    if budget >= 2.0 and best[0] < lib.moore_bound(d, D):
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=remaining - 3.0)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
