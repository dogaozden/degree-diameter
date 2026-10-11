import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bipartite graphs with degree <= d and
# diameter <= D. It starts from a valid parent, adds one vertex at a time when
# the current graph is valid (greedy cover of the opposite side), then repairs
# with degree-preserving swaps and endpoint moves. It keeps the largest valid
# graph seen, restarting from that snapshot when the search stagnates.
# ----------------------------------------------------------------------------

_C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define WMAX 18
#define DMAX 64
#define EMAX (MAXN * DMAX)

static int N, DEG, DD;
static int nbr[MAXN][DMAX];
static int dg[MAXN];
static int col[MAXN];
static unsigned char M[MAXN][MAXN];
static uint64_t bufA[MAXN * WMAX], bufB[MAXN * WMAX];
static uint64_t rs = 88172645463325252ULL;
static int iu[EMAX], iv[EMAX];
static int bu[EMAX], bv[EMAX];
static int cand_buf[MAXN];
static unsigned char usedc[MAXN];
static unsigned char cov[MAXN];
static int chosen[DMAX];
static int stk[MAXN];

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > DD. Zero means valid. */
static long long cost_eval(void) {
    int W = (N + 63) >> 6;
    uint64_t *cur = bufA, *nx = bufB, *t;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) {
        uint64_t *o = cur + (size_t)v * W;
        o[v >> 6] |= 1ULL << (v & 63);
        for (int i = 0; i < dg[v]; i++) {
            int u = nbr[v][i];
            o[u >> 6] |= 1ULL << (u & 63);
        }
    }
    for (int r = 1; r < DD; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nx + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(uint64_t) * W);
            for (int i = 0; i < dg[v]; i++) {
                const uint64_t *cu = cur + (size_t)nbr[v][i] * W;
                for (int w = 0; w < W; w++) o[w] |= cu[w];
            }
        }
        t = cur;
        cur = nx;
        nx = t;
    }
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        int cnt = 0;
        const uint64_t *c = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) cnt += pc64(c[w]);
        tot += N - cnt;
    }
    return tot / 2;
}

static void add_e(int a, int b) {
    nbr[a][dg[a]++] = b;
    nbr[b][dg[b]++] = a;
    M[a][b] = 1;
    M[b][a] = 1;
}

static void del_from(int a, int b) {
    for (int i = 0; i < dg[a]; i++) {
        if (nbr[a][i] == b) {
            nbr[a][i] = nbr[a][--dg[a]];
            return;
        }
    }
}

static void del_e(int a, int b) {
    del_from(a, b);
    del_from(b, a);
    M[a][b] = 0;
    M[b][a] = 0;
}

static int snap(int *su, int *sv) {
    int m = 0;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < dg[v]; i++) {
            int u = nbr[v][i];
            if (v < u && m < EMAX) {
                su[m] = v;
                sv[m] = u;
                m++;
            }
        }
    }
    return m;
}

static void load(int n, int m, const int *su, const int *sv) {
    memset(M, 0, sizeof M);
    for (int i = 0; i < MAXN; i++) dg[i] = 0;
    N = n;
    for (int e = 0; e < m; e++) add_e(su[e], sv[e]);
}

static int bipartite_color(void) {
    for (int i = 0; i < N; i++) col[i] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp) {
            int u = stk[--sp];
            for (int i = 0; i < dg[u]; i++) {
                int w = nbr[u][i];
                if (col[w] == -1) {
                    col[w] = 1 - col[u];
                    stk[sp++] = w;
                } else if (col[w] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Random vertex on side s; spare=1 needs dg < DEG, spare=0 needs dg > 0. -1 if none found. */
static int pick_v(int s, int spare) {
    for (int t = 0; t < 300; t++) {
        int v = rint_(N);
        if (col[v] != s) continue;
        if (spare) {
            if (dg[v] < DEG) return v;
        } else if (dg[v] > 0) {
            return v;
        }
    }
    return -1;
}

/* Add a vertex on a random side. Its neighbours are chosen greedily to cover
   same-side vertices, then filled with arbitrary spare opposite vertices. */
static int grow(void) {
    int c = rint_(2);
    for (int tries = 0; tries < 2; tries++, c ^= 1) {
        int side = 1 - c;
        int nc = 0;
        for (int v = 0; v < N; v++)
            if (col[v] == side && dg[v] < DEG) cand_buf[nc++] = v;
        if (nc == 0) continue;
        for (int v = 0; v < N; v++) cov[v] = 0;
        for (int i = 0; i < nc; i++) usedc[cand_buf[i]] = 0;
        int cn = 0;
        while (cn < DEG && cn < nc) {
            int bestv = -1, bestk = -1;
            for (int i = 0; i < nc; i++) {
                int u = cand_buf[i];
                if (usedc[u] || dg[u] >= DEG) continue;
                int g = 0;
                for (int j = 0; j < dg[u]; j++)
                    if (!cov[nbr[u][j]]) g++;
                int key = g * 4096 + rint_(4096);
                if (key > bestk) {
                    bestk = key;
                    bestv = u;
                }
            }
            if (bestv < 0) break;
            usedc[bestv] = 1;
            chosen[cn++] = bestv;
            for (int j = 0; j < dg[bestv]; j++) cov[nbr[bestv][j]] = 1;
        }
        int v = N;
        col[v] = c;
        dg[v] = 0;
        N++;
        for (int i = 0; i < cn; i++) add_e(v, chosen[i]);
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    int d = argc > 1 ? atoi(argv[1]) : 3;
    int D = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double budget = argc > 4 ? atof(argv[4]) : 5.0;
    DEG = d < 1 ? 1 : (d > DMAX ? DMAX : d);
    DD = D < 1 ? 1 : D;
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double tlim = budget > 1.0 ? budget * 0.9 : budget * 0.5;
    clock_t t0 = clock();

    int n0 = 0, m0 = 0, okin = 1;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
        okin = 0;
    }
    if (okin && (n0 < 1 || n0 > MAXN - 2 || m0 < 0 || m0 > EMAX)) okin = 0;
    for (int e = 0; okin && e < m0; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            okin = 0;
            break;
        }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) {
            okin = 0;
            break;
        }
        iu[e] = u;
        iv[e] = v;
    }
    if (okin) {
        memset(M, 0, sizeof M);
        for (int i = 0; i < MAXN; i++) dg[i] = 0;
        N = n0;
        for (int e = 0; e < m0 && okin; e++) {
            int u = iu[e], v = iv[e];
            if (M[u][v] || dg[u] >= DEG || dg[v] >= DEG) okin = 0;
            else add_e(u, v);
        }
        if (okin) okin = bipartite_color();
    }
    if (!okin) {
        /* Fallback: K_{DEG,DEG}. */
        memset(M, 0, sizeof M);
        for (int i = 0; i < MAXN; i++) dg[i] = 0;
        N = 2 * DEG;
        for (int i = 0; i < N; i++) col[i] = i < DEG ? 0 : 1;
        for (int a = 0; a < DEG; a++)
            for (int b = 0; b < DEG; b++) add_e(a, DEG + b);
    }

    int n_init = N;
    int bm = snap(bu, bv);
    long long cost = cost_eval();
    int bestN = (cost == 0) ? N : -1;

    const long long LIMIT = 40000;
    long long stag = 0;
    long long iter = 0;

    while (1) {
        if ((iter & 63) == 0) {
            if ((double)(clock() - t0) / CLOCKS_PER_SEC > tlim) break;
        }
        iter++;

        if (cost == 0) {
            if (N > bestN) {
                bestN = N;
                bm = snap(bu, bv);
            }
            if (N >= MAXN - 2) break;
            if (!grow()) break;
            cost = cost_eval();
            stag = 0;
            continue;
        }

        stag++;
        if (stag > LIMIT) {
            if (bestN >= 0) {
                load(bestN, bm, bu, bv);
                cost = cost_eval();
            }
            stag = 0;
            continue;
        }

        double T = 0.12 + 0.9 * (1.0 - (double)stag / (double)LIMIT);
        double r = rdbl();
        int s = rint_(2);

        if (r < 0.45) {
            /* Degree-preserving double edge swap on side s. */
            int x1 = pick_v(s, 0), x2 = pick_v(s, 0);
            if (x1 < 0 || x2 < 0 || x1 == x2) continue;
            int y1 = nbr[x1][rint_(dg[x1])];
            int y2 = nbr[x2][rint_(dg[x2])];
            if (y1 == y2 || M[x1][y2] || M[x2][y1]) continue;
            del_e(x1, y1);
            del_e(x2, y2);
            add_e(x1, y2);
            add_e(x2, y1);
            long long nc = cost_eval();
            long long dl = nc - cost;
            if (dl <= 0 || rdbl() < exp(-(double)dl / T)) {
                cost = nc;
            } else {
                del_e(x1, y2);
                del_e(x2, y1);
                add_e(x1, y1);
                add_e(x2, y2);
            }
        } else if (r < 0.9) {
            /* Move one endpoint of an edge to another spare vertex on side s. */
            int x1 = pick_v(s, 0), x2 = pick_v(s, 1);
            if (x1 < 0 || x2 < 0 || x1 == x2) continue;
            int y1 = nbr[x1][rint_(dg[x1])];
            if (M[x2][y1]) continue;
            del_e(x1, y1);
            add_e(x2, y1);
            long long nc = cost_eval();
            long long dl = nc - cost;
            if (dl <= 0 || rdbl() < exp(-(double)dl / T)) {
                cost = nc;
            } else {
                del_e(x2, y1);
                add_e(x1, y1);
            }
        } else {
            /* Add an edge between spare vertices on opposite sides. */
            int x1 = pick_v(s, 1), y1 = pick_v(1 - s, 1);
            if (x1 < 0 || y1 < 0 || M[x1][y1]) continue;
            add_e(x1, y1);
            long long nc = cost_eval();
            long long dl = nc - cost;
            if (dl <= 0 || rdbl() < exp(-(double)dl / T)) {
                cost = nc;
            } else {
                del_e(x1, y1);
            }
        }
    }

    int pn = bestN >= 0 ? bestN : n_init;
    printf("%d %d\n", pn, bm);
    for (int e = 0; e < bm; e++) printf("%d %d\n", bu[e], bv[e]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence. Each old vertex has degree q+1, so with
# d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S such that
# every line holds at most s points of S and every point lies on at most s
# lines indexed by S. For each P in S add a new A-vertex joined to the q+1
# lines through P; for each j in S add a new B-vertex joined to the q+1 points
# on line j. Diameter stays 3.
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


def _arc_graph(m, edges, point_lines, S, line_points):
    """Build the extended graph: old PG incidence plus a new A and a new B vertex per element of S."""
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
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, S, line_points)
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
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured parents: arc-extended projective planes (D >= 3), W(q) (D >= 4).
    if D >= 3:
        cands = _arc_extensions(d, t_start + 0.15 * time_limit,
                                random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Bold step: C annealing that grows the best parent by adding vertices and
    # repairing the distance constraint. Output is re-checked before use.
    if best[0] < lib.moore_bound(d, D):
        elapsed = time.monotonic() - t_start
        budget = max(1.0, 0.8 * time_limit - elapsed - 1.0)
        timeout = max(5.0, 0.92 * time_limit - elapsed)
        try:
            out = lib.run_c(_C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=timeout)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
