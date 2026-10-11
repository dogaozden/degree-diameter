import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# A-side: a set SA of points. Each SA point P gets a new vertex joined to all
#         q+1 lines through P. Constraint: every line holds <= s points of SA.
# B-side: a set SB of lines. Each j in SB gets a new vertex joined to all
#         q+1 points on j. Constraint: every point lies on <= s lines of SB.
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
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n_c, e_c))
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
# C engine: bitset-based bounded-diameter annealing with vertex insertion.
#
# State is a bipartite graph with max degree d. Cost = number of unordered
# vertex pairs at distance > D (unreachable counts too), computed exactly by
# bitset ball expansion. Moves: add an edge (never raises cost), rewire one
# endpoint, or swap two edges of the same side pair. When cost reaches 0 the
# current graph is saved and a new vertex is inserted; on stagnation the search
# restarts from the best saved graph. Output is always a valid graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 1024
#define WMAX 16
#define MAXD 64
#define MAXE (NMAX * MAXD / 2)

static int dd, DD;
static int n;
static int side[NMAX];
static int deg[NMAX];
static int adj[NMAX][MAXD];
static uint64_t RA[NMAX][WMAX];
static uint64_t RB[NMAX][WMAX];
static int W;

static int bestn = 0, bestm = 0;
static int bestside[NMAX];
static int bestU[MAXE], bestV[MAXE];

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_sec(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static inline int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long cost_fn(void) {
    W = (n + 63) >> 6;
    if (W < 1) W = 1;
    for (int v = 0; v < n; v++) {
        memset(RA[v], 0, sizeof(uint64_t) * (size_t)W);
        RA[v][v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t (*cu)[WMAX] = RA;
    uint64_t (*nx)[WMAX] = RB;
    for (int r = 0; r < DD; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nx[v];
            memcpy(dst, cu[v], sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = cu[adj[v][k]];
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t (*t)[WMAX] = cu;
        cu = nx;
        nx = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(cu[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) return 1;
    return 0;
}

static void rm_half(int x, int y) {
    for (int k = 0; k < deg[x]; k++) {
        if (adj[x][k] == y) {
            adj[x][k] = adj[x][--deg[x]];
            return;
        }
    }
}

static void del_edge(int a, int b) {
    rm_half(a, b);
    rm_half(b, a);
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void greedy_fill(void) {
    for (int a = 0; a < n; a++) {
        if (side[a] != 0) continue;
        for (int b = 0; b < n && deg[a] < dd; b++) {
            if (side[b] == 1 && deg[b] < dd && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

static void save_best(void) {
    bestn = n;
    bestm = 0;
    for (int v = 0; v < n; v++) bestside[v] = side[v];
    for (int v = 0; v < n; v++) {
        for (int k = 0; k < deg[v]; k++) {
            int u = adj[v][k];
            if (u > v && bestm < MAXE) {
                bestU[bestm] = v;
                bestV[bestm] = u;
                bestm++;
            }
        }
    }
}

static void load_best(void) {
    int old = n > bestn ? n : bestn;
    for (int v = 0; v < old; v++) deg[v] = 0;
    n = bestn;
    for (int v = 0; v < n; v++) side[v] = bestside[v];
    for (int i = 0; i < bestm; i++) add_edge(bestU[i], bestV[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    long long seed = atoll(argv[3]);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    double deadline = now_sec() + budget;

    if (dd < 1 || DD < 1 || dd > MAXD) {
        printf("1 0\n");
        return 0;
    }

    int n_in = 0, m_in = 0;
    if (scanf("%d %d", &n_in, &m_in) != 2) {
        n_in = 0;
        m_in = 0;
    }
    int good = (n_in >= 1 && n_in <= NMAX && m_in >= 0 && m_in <= MAXE);
    n = good ? n_in : 0;
    if (good)
        for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m_in; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            good = 0;
            break;
        }
        if (!good) continue;
        if (u < 0 || u >= n || v < 0 || v >= n || u == v || has_edge(u, v) ||
            deg[u] >= dd || deg[v] >= dd)
            good = 0;
        else
            add_edge(u, v);
    }

    if (good) {
        int col[NMAX];
        int q[NMAX];
        for (int v = 0; v < n; v++) col[v] = -1;
        for (int s = 0; s < n && good; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int h = 0, t = 0;
            q[t++] = s;
            while (h < t && good) {
                int x = q[h++];
                for (int k = 0; k < deg[x]; k++) {
                    int y = adj[x][k];
                    if (col[y] < 0) {
                        col[y] = 1 - col[x];
                        q[t++] = y;
                    } else if (col[y] == col[x]) {
                        good = 0;
                        break;
                    }
                }
            }
        }
        if (good)
            for (int v = 0; v < n; v++) side[v] = col[v];
    }

    if (!good) {
        n = 2;
        deg[0] = 0;
        deg[1] = 0;
        side[0] = 0;
        side[1] = 1;
        add_edge(0, 1);
    }

    greedy_fill();
    long long cur = cost_fn();
    if (cur == 0) save_best();

    double T0 = 4.0, T = T0;
    long long iters = 0, since_add = 0;
    const long long STALL = 6000;

    while (1) {
        if ((iters & 127) == 0 && now_sec() > deadline) break;
        iters++;
        since_add++;
        T *= 0.9995;
        if (T < 0.1) T = T0;

        if (cur == 0 && n < NMAX - 1) {
            if (n > bestn) save_best();
            side[n] = rndint(2);
            deg[n] = 0;
            n++;
            greedy_fill();
            cur = cost_fn();
            T = T0;
            since_add = 0;
            continue;
        }

        if (since_add > STALL && bestn > 0) {
            load_best();
            cur = 0;
            since_add = 0;
            T = T0;
            continue;
        }

        double u = rnd01();
        if (u < 0.10) {
            int x = rndint(n), z = rndint(n);
            if (side[x] == side[z] || deg[x] >= dd || deg[z] >= dd || has_edge(x, z)) continue;
            add_edge(x, z);
            cur = cost_fn();
        } else if (u < 0.55) {
            int x = rndint(n);
            if (deg[x] == 0) continue;
            int y = adj[x][rndint(deg[x])];
            int z = rndint(n);
            if (side[z] != side[y] || z == y || deg[z] >= dd || has_edge(x, z)) continue;
            del_edge(x, y);
            add_edge(x, z);
            long long nc = cost_fn();
            long long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cur = nc;
            } else {
                del_edge(x, z);
                add_edge(x, y);
            }
        } else {
            int x1 = rndint(n);
            if (deg[x1] == 0) continue;
            int y1 = adj[x1][rndint(deg[x1])];
            int x2 = rndint(n);
            if (x2 == x1 || side[x2] != side[x1] || deg[x2] == 0) continue;
            int y2 = adj[x2][rndint(deg[x2])];
            if (y2 == y1 || has_edge(x1, y2) || has_edge(x2, y1)) continue;
            del_edge(x1, y1);
            del_edge(x2, y2);
            add_edge(x1, y2);
            add_edge(x2, y1);
            long long nc = cost_fn();
            long long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cur = nc;
            } else {
                del_edge(x1, y2);
                del_edge(x2, y1);
                add_edge(x1, y1);
                add_edge(x2, y2);
            }
        }
    }

    if (cur == 0 && n > bestn) save_best();
    if (bestn == 0) {
        printf("2 1\n0 1\n");
        return 0;
    }
    printf("%d %d\n", bestn, bestm);
    for (int i = 0; i < bestm; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
"""


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is a valid fallback for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    rng = random.Random(seed * 7919 + d)

    if D >= 3:
        for n_c, e_c in _arc_extensions(d, t_start + 0.15 * time_limit, rng):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing can be gained.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Vertex-insertion annealing in C, started from the best graph found so far.
    # Reserve time for compilation (first call) and parsing.
    remaining = 0.8 * time_limit - (time.monotonic() - t_start) - 2.0
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                            stdin_graph=best, timeout=remaining + 1.5)
            n_c, e_c = lib.parse_graph_text(out)
            consider(n_c, e_c)
        except (RuntimeError, ValueError, OSError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
