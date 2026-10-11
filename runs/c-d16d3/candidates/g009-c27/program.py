import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: repair search for diameter-D bipartite graphs with extra vertices.
#
# Starts from a valid input graph, then repeatedly adds one vertex on each side
# and anneals over degree-preserving 2-switches, edge additions, and endpoint
# rewiring. The cost is the number of ordered vertex pairs at distance > D,
# computed with bitsets. Every accepted state with cost 0 is snapshotted before
# the next growth step, so the printed graph is always valid.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXDEG 64
#define MAXW ((MAXN + 63) / 64)
#define MAXE 40000

static int N, Dd, DIAM;
static int side[MAXN], deg[MAXN];
static int nb[MAXN][MAXDEG];
static unsigned char adjm[MAXN][MAXN];
static uint64_t Rb[2][MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static long long cur_cost;
static int bestN = 0, bestM = 0;
static int bestU[MAXE], bestV[MAXE];

static uint64_t rng_next(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rnd(int k) { return (int)(rng_next() % (uint64_t)k); }
static double urand(void) { return (double)(rng_next() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int a, int b) {
    adjm[a][b] = adjm[b][a] = 1;
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void rm_from(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (nb[a][k] == b) {
            nb[a][k] = nb[a][--deg[a]];
            return;
        }
    }
}

static void del_edge(int a, int b) {
    adjm[a][b] = adjm[b][a] = 0;
    rm_from(a, b);
    rm_from(b, a);
}

/* Number of ordered pairs (v, w) with dist(v, w) > DIAM. Zero means valid. */
static long long cost_eval(void) {
    int Wn = (N + 63) / 64;
    int c = 0;
    for (int v = 0; v < N; v++) {
        memset(Rb[0][v], 0, sizeof(uint64_t) * Wn);
        Rb[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = Rb[1 - c][v];
            memcpy(o, Rb[c][v], sizeof(uint64_t) * Wn);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *s = Rb[c][nb[v][k]];
                for (int w = 0; w < Wn; w++) o[w] |= s[w];
            }
        }
        c = 1 - c;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int cnt = 0;
        for (int w = 0; w < Wn; w++) cnt += popc(Rb[c][v][w]);
        bad += N - cnt;
    }
    return bad;
}

static int pick(int s) {
    int v;
    do { v = rnd(N); } while (side[v] != s);
    return v;
}

static int accept(long long delta, double T) {
    if (delta <= 0) return 1;
    return urand() < exp(-(double)delta / T);
}

static void try_move(double T) {
    int type = rnd(10);
    long long nc;
    if (type < 6) {
        /* degree-preserving 2-switch */
        int a = pick(0), c = pick(0);
        if (a == c || deg[a] == 0 || deg[c] == 0) return;
        int b = nb[a][rnd(deg[a])];
        int e = nb[c][rnd(deg[c])];
        if (b == e || adjm[a][e] || adjm[c][b]) return;
        del_edge(a, b); del_edge(c, e);
        add_edge(a, e); add_edge(c, b);
        nc = cost_eval();
        if (accept(nc - cur_cost, T)) { cur_cost = nc; return; }
        del_edge(a, e); del_edge(c, b);
        add_edge(a, b); add_edge(c, e);
    } else if (type < 8) {
        /* add an edge between two deficient vertices */
        int a = pick(0), b = pick(1);
        if (deg[a] >= Dd || deg[b] >= Dd || adjm[a][b]) return;
        add_edge(a, b);
        nc = cost_eval();
        if (accept(nc - cur_cost, T)) { cur_cost = nc; return; }
        del_edge(a, b);
    } else {
        /* move one endpoint of an edge to a deficient vertex */
        int a = pick(0);
        if (deg[a] == 0) return;
        int b = nb[a][rnd(deg[a])];
        int e = pick(1);
        if (e == b || deg[e] >= Dd || adjm[a][e]) return;
        del_edge(a, b); add_edge(a, e);
        nc = cost_eval();
        if (accept(nc - cur_cost, T)) { cur_cost = nc; return; }
        del_edge(a, e); add_edge(a, b);
    }
}

static void wire(int x) {
    static int cand[MAXN];
    int cnt = 0;
    for (int v = 0; v < N; v++) {
        if (side[v] != side[x] && deg[v] < Dd && !adjm[x][v]) cand[cnt++] = v;
    }
    for (int i = cnt - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    for (int i = 0; i < cnt && deg[x] < Dd; i++) {
        if (deg[cand[i]] < Dd) add_edge(x, cand[i]);
    }
}

static void grow_pair(void) {
    int x = N, y = N + 1;
    side[x] = 0; side[y] = 1;
    deg[x] = deg[y] = 0;
    N += 2;
    wire(x);
    wire(y);
    cur_cost = cost_eval();
}

static void snapshot(void) {
    int m = 0;
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < deg[v]; k++) {
            int u = nb[v][k];
            if (u > v && m < MAXE) {
                bestU[m] = v;
                bestV[m] = u;
                m++;
            }
        }
    }
    bestN = N;
    bestM = m;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    Dd = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    if (Dd < 1 || Dd >= MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 0 || n > MAXN - 2) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (adjm[u][v] || deg[u] >= Dd || deg[v] >= Dd) continue;
        add_edge(u, v);
    }

    /* bipartition by BFS */
    static int q[MAXN];
    int bip = 1;
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N && bip; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt && bip) {
            int u = q[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int w = nb[u][k];
                if (side[w] < 0) {
                    side[w] = 1 - side[u];
                    q[qt++] = w;
                } else if (side[w] == side[u]) {
                    bip = 0;
                    break;
                }
            }
        }
    }
    int n0 = 0, n1 = 0;
    for (int v = 0; v < N; v++) { if (side[v] == 0) n0++; else n1++; }
    if (!bip || n0 == 0 || n1 == 0) {
        printf("0 0\n");
        return 0;
    }

    cur_cost = cost_eval();
    clock_t t0 = clock();
    double limit = budget * (double)CLOCKS_PER_SEC;
    if (cur_cost == 0) snapshot();

    long long phase = 0, it = 0;
    while (1) {
        if ((it & 127) == 0 && (double)(clock() - t0) > limit) break;
        it++;
        if (cur_cost == 0) {
            snapshot();
            if (N + 2 > MAXN) break;
            grow_pair();
            phase = 0;
            continue;
        }
        double T = 0.05 + 1.2 * (1.0 - (double)(phase % 200000) / 200000.0);
        phase++;
        try_move(T);
    }
    if (cur_cost == 0) snapshot();

    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions: arc-extended projective plane incidence graphs.
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). For each point P
# in a set S, add a new point-side vertex joined to the q+1 lines through P. For
# each j in S, add a new line-side vertex joined to the q+1 points on j. The
# load condition keeps every old vertex within degree d.
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
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new point-side and a new line-side vertex per element of S."""
    k = len(S)
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        y = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, y))
    return 2 * m + 2 * k, E


def _arc_extensions(d, deadline, rng):
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q), diameter 4 (used only when D >= 4).
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
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])
    best_n = best[0]

    def consider(cand):
        nonlocal best, best_n
        if cand is None:
            return
        n, e = cand
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Constructions give the starting graph for the C repair search.
    if D >= 3:
        for cand in _arc_extensions(d, t0 + 0.2 * time_limit, random.Random(seed * 7919 + d)):
            consider(cand)
    if D >= 4 and time.monotonic() < t0 + 0.3 * time_limit:
        consider(_best_gq(d))

    # Stop early when the Moore bound is already reached (e.g. calibration cases).
    if d > 60 or lib.moore_bound(d, D) <= best_n:
        return best

    # Bold change: C repair search adds vertex pairs to the best construction.
    elapsed = time.monotonic() - t0
    remaining = 0.9 * time_limit - elapsed
    if remaining > 2.0:
        budget = max(0.5, 0.75 * remaining - 1.0)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=remaining)
            n, e = lib.parse_graph_text(out)
            consider((n, e))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
