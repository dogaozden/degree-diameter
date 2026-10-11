import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: vertex growth plus annealing on the number of bad pairs.
#
# State: bipartite graph with max degree d. Cost = ordered pairs at distance
# > D (unreachable counts). Moves: grow a vertex whose neighbourhood covers
# the radius-(D-1) balls of all old vertices (greedy, may be partial), add a
# cross edge between spare vertices, or a degree-preserving 2-switch. Valid
# states (cost 0) are snapshotted whenever they have more vertices. The engine
# restarts from the best snapshot after a long stretch without improvement.
# Output is always re-checked in Python with lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXDEG 128
#define W 16

typedef uint64_t Bits[W];

static int n, d, D;
static int adj[MAXN][MAXDEG];
static int deg[MAXN];
static int side[MAXN];

static int bestAdj[MAXN][MAXDEG];
static int bestDeg[MAXN];
static int bestSide[MAXN];
static int bestN = 0;
static int bestValid = 0;

static Bits BA[MAXN], BB[MAXN], PREV[MAXN];
static uint64_t rs = 88172645463325252ULL;

static unsigned rnd(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return (unsigned)((rs * 0x2545F4914F6CDD1DULL) >> 32);
}

static double rnd01(void) { return rnd() / 4294967296.0; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int nwords(void) { return (n + 63) >> 6; }

static int isAdj(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (adj[u][i] == v) return 1;
    return 0;
}

static void addEdge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void removeFrom(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][--deg[u]];
            return;
        }
    }
}

static void delEdge(int u, int v) {
    removeFrom(u, v);
    removeFrom(v, u);
}

/* Returns sum over vertices of (n - |ball_D(v)|). Also fills PREV with radius D-1 balls. */
static long long evalCost(void) {
    int nw = nwords();
    Bits *cur = BA, *nx = BB;
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, sizeof(Bits));
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    if (D - 1 <= 0) memcpy(PREV, cur, sizeof(Bits) * (size_t)n);
    for (int it = 1; it <= D; it++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < nw; w++) nx[v][w] = cur[v][w];
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *cu = cur[adj[v][i]];
                for (int w = 0; w < nw; w++) nx[v][w] |= cu[w];
            }
        }
        Bits *t = cur;
        cur = nx;
        nx = t;
        if (it == D - 1) memcpy(PREV, cur, sizeof(Bits) * (size_t)n);
    }
    long long cost = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += popc(cur[v][w]);
        cost += n - c;
    }
    return cost;
}

/* Greedy cover of all old vertices by radius-(D-1) balls of opposite-side spare vertices.
   Adds the new vertex even when the cover is partial (annealing repairs it). */
static int growVertex(void) {
    evalCost();
    int nw = nwords();
    Bits U;
    memset(U, 0, sizeof(Bits));
    for (int v = 0; v < n; v++) U[v >> 6] |= 1ULL << (v & 63);
    int s = (int)(rnd() & 1u);
    static char chosen[MAXN];
    memset(chosen, 0, sizeof(chosen));
    int picked[MAXDEG];
    int k = 0;
    int off = (int)(rnd() % (unsigned)n);
    while (k < d) {
        int bestC = -1, bestGain = 0;
        for (int t = 0; t < n; t++) {
            int c = (t + off) % n;
            if (side[c] == s || deg[c] >= d || chosen[c]) continue;
            int g = 0;
            for (int w = 0; w < nw; w++) g += popc(PREV[c][w] & U[w]);
            if (g > bestGain) {
                bestGain = g;
                bestC = c;
            }
        }
        if (bestC < 0) break;
        chosen[bestC] = 1;
        picked[k++] = bestC;
        for (int w = 0; w < nw; w++) U[w] &= ~PREV[bestC][w];
    }
    if (k == 0) return 0;
    int nv = n;
    n++;
    side[nv] = s;
    deg[nv] = 0;
    for (int i = 0; i < k; i++) addEdge(nv, picked[i]);
    return 1;
}

static int randomEdge(int *a, int *b) {
    for (int t = 0; t < 100; t++) {
        int v = (int)(rnd() % (unsigned)n);
        if (deg[v] == 0) continue;
        int u = adj[v][rnd() % (unsigned)deg[v]];
        if (side[v] == 0) {
            *a = v;
            *b = u;
        } else {
            *a = u;
            *b = v;
        }
        return 1;
    }
    return 0;
}

/* Degree-preserving 2-switch: (a,b),(x,y) -> (a,y),(x,b); a,x on side 0. */
static int twoSwitch(int *a, int *b, int *x, int *y) {
    if (!randomEdge(a, b) || !randomEdge(x, y)) return 0;
    if (*a == *x || *b == *y) return 0;
    if (isAdj(*a, *y) || isAdj(*x, *b)) return 0;
    delEdge(*a, *b);
    delEdge(*x, *y);
    addEdge(*a, *y);
    addEdge(*x, *b);
    return 1;
}

static int addRandomEdge(int *u, int *v) {
    static int s0[MAXN], s1[MAXN];
    int n0 = 0, n1 = 0;
    for (int i = 0; i < n; i++) {
        if (deg[i] < d) {
            if (side[i] == 0) s0[n0++] = i;
            else s1[n1++] = i;
        }
    }
    if (n0 == 0 || n1 == 0) return 0;
    for (int t = 0; t < 40; t++) {
        int x = s0[rnd() % (unsigned)n0];
        int y = s1[rnd() % (unsigned)n1];
        if (!isAdj(x, y)) {
            addEdge(x, y);
            *u = x;
            *v = y;
            return 1;
        }
    }
    return 0;
}

static void saveBest(void) {
    bestN = n;
    memcpy(bestAdj, adj, sizeof(adj));
    memcpy(bestDeg, deg, sizeof(deg));
    memcpy(bestSide, side, sizeof(side));
}

static void restoreBest(void) {
    n = bestN;
    memcpy(adj, bestAdj, sizeof(adj));
    memcpy(deg, bestDeg, sizeof(deg));
    memcpy(side, bestSide, sizeof(side));
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    if (d > MAXDEG) d = MAXDEG;
    if (d < 1) d = 1;

    int N0 = 0, M0 = 0;
    if (scanf("%d %d", &N0, &M0) != 2) {
        N0 = 0;
        M0 = 0;
    }
    if (N0 <= 0 || N0 > MAXN || M0 < 0) {
        printf("0 0\n");
        return 0;
    }
    n = N0;
    for (int i = 0; i < n; i++) {
        deg[i] = 0;
        side[i] = -1;
    }
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || deg[u] >= MAXDEG || deg[v] >= MAXDEG) {
            printf("0 0\n");
            return 0;
        }
        addEdge(u, v);
    }

    static int queue[MAXN];
    int bip = 1;
    for (int s0 = 0; s0 < n && bip; s0++) {
        if (side[s0] != -1) continue;
        side[s0] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s0;
        while (qh < qt && bip) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (side[v] == -1) {
                    side[v] = 1 - side[u];
                    queue[qt++] = v;
                } else if (side[v] == side[u]) {
                    bip = 0;
                    break;
                }
            }
        }
    }
    if (!bip) {
        printf("0 0\n");
        return 0;
    }

    long long cost = evalCost();
    saveBest();
    bestValid = 0;
    if (cost == 0) bestValid = 1;

    long long it = 0, lastImp = 0;
    clock_t endc = clock() + (clock_t)(tl * (double)CLOCKS_PER_SEC);
    while (clock() < endc) {
        it++;
        double T = 0.15 + 1.2 * exp(-(double)(it - lastImp) / 2000.0);
        int kind = -1, ra = 0, rb = 0, rx = 0, ry = 0;
        int oldn = n;
        long long oldcost = cost;
        int r = (int)(rnd() % 100u);
        if (r < 12) {
            if (n + 1 >= MAXN) continue;
            if (!growVertex()) continue;
            kind = 0;
        } else if (r < 40) {
            if (!addRandomEdge(&ra, &rb)) continue;
            kind = 1;
        } else {
            if (!twoSwitch(&ra, &rb, &rx, &ry)) continue;
            kind = 2;
        }
        long long c2 = evalCost();
        long long delta = c2 - oldcost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cost = c2;
            if (cost == 0 && (!bestValid || n > bestN)) {
                saveBest();
                bestValid = 1;
                lastImp = it;
            }
        } else {
            if (kind == 0) {
                int w = n - 1;
                while (deg[w] > 0) delEdge(w, adj[w][0]);
                n = oldn;
            } else if (kind == 1) {
                delEdge(ra, rb);
            } else {
                delEdge(ra, ry);
                delEdge(rx, rb);
                addEdge(ra, rb);
                addEdge(rx, ry);
            }
        }
        if (bestValid && it - lastImp > 6000) {
            restoreBest();
            cost = evalCost();
            lastImp = it;
        }
    }

    int m = 0;
    for (int v = 0; v < bestN; v++)
        for (int i = 0; i < bestDeg[v]; i++)
            if (bestAdj[v][i] > v) m++;
    printf("%d %d\n", bestN, m);
    for (int v = 0; v < bestN; v++)
        for (int i = 0; i < bestDeg[v]; i++) {
            int u = bestAdj[v][i];
            if (u > v) printf("%d %d\n", v, u);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1, so spare capacity is s = d - q - 1. Choose point sets SA and
# SB, each an s-arc-like set (every line holds <= s points of SA, every point
# lies on <= s lines of SB). Add an A-vertex per point of SA (joined to its
# lines) and a B-vertex per line of SB (joined to its points).
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
    """Randomized greedy: choose elements so every target is hit by <= s chosen elements."""
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
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one A-vertex per SA point and one B-vertex per SB line."""
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


def _has_spare(n, edges, d):
    """True if some vertex has degree below d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return any(x < d for x in deg)


def build(d, D, seed, time_limit):
    start = time.monotonic()
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
        for n_c, e_c in _arc_extensions(d, start + 0.2 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < start + 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # C refinement: grow and repair from the best construction.
    end = start + 0.9 * time_limit
    remaining = end - time.monotonic()
    if (D >= 2 and remaining > 4 and best_n < lib.moore_bound(d, D)
            and _has_spare(best_n, best[1], d)):
        c_budget = max(0.5, remaining - 3.0)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}"],
                             stdin_graph=best, timeout=remaining)
            n_c, e_c = lib.parse_graph_text(text)
            consider(n_c, e_c)
        except (RuntimeError, ValueError, OSError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
