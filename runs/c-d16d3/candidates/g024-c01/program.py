import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: "grow-and-repair" annealing on bipartite graphs.
#
# Input: a valid start graph (or "0 0" for K_{d,d}). The engine grows the graph
# by pairs of vertices (one new vertex per colour class), wires each new vertex
# into spare degree on the opposite side, and then repairs the graph with
# simulated annealing. Cost = number of unordered vertex pairs at distance > D.
# Moves are degree-preserving 2-switches on cross edges, plus rare add/remove
# of cross edges. Bipartiteness and the degree cap hold by construction.
# Distance balls are bitsets, so one cost evaluation is D rounds of OR-sweeps.
# The best valid graph seen is printed at the end.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXW 32
#define MAXDEG 128
#define MAXE (MAXN * MAXDEG / 2)
#define CYCLE 20000L

static int N, DIAM, DEG;
static int dg[MAXN];
static int nbr[MAXN][MAXDEG];
static unsigned char M[MAXN][MAXN];
static int side[MAXN];
static int lst[2][MAXN];
static int cnt[2];
static uint64_t RA[MAXN][MAXW];
static uint64_t RB[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static clock_t dl_cpu;
static time_t w0;
static double tl_wall;

static int bestN = -1, bestM = 0;
static int BU[MAXE], BV[MAXE];

static int mt, mu1, mv1, mu2, mv2;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int out_of_time(void) {
    return clock() > dl_cpu || (double)(time(NULL) - w0) >= tl_wall;
}

static void add_edge(int a, int b) {
    M[a][b] = M[b][a] = 1;
    nbr[a][dg[a]++] = b;
    nbr[b][dg[b]++] = a;
}

static void rem_half(int a, int b) {
    for (int k = 0; k < dg[a]; k++) {
        if (nbr[a][k] == b) {
            nbr[a][k] = nbr[a][--dg[a]];
            return;
        }
    }
}

static void del_edge(int a, int b) {
    M[a][b] = M[b][a] = 0;
    rem_half(a, b);
    rem_half(b, a);
}

/* Number of unordered pairs at distance > DIAM. Zero means valid. */
static long long cost_eval(void) {
    int n = N, w = (n + 63) / 64;
    uint64_t (*cur)[MAXW] = RA, (*nxt)[MAXW] = RB, (*tmp)[MAXW];
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * (size_t)w);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *x = nxt[v];
            memcpy(x, cur[v], sizeof(uint64_t) * (size_t)w);
            for (int k = 0; k < dg[v]; k++) {
                const uint64_t *y = cur[nbr[v][k]];
                for (int t = 0; t < w; t++) x[t] |= y[t];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long unreached = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int t = 0; t < w; t++) c += pc64(cur[v][t]);
        unreached += n - c;
    }
    return unreached / 2;
}

/* Random vertex of side s: need==1 -> spare degree, need==2 -> degree > 0. */
static int pick_from(int s, int need) {
    if (cnt[s] <= 0) return -1;
    for (int t = 0; t < 60; t++) {
        int v = lst[s][rndint(cnt[s])];
        if (need == 1 && dg[v] < DEG) return v;
        if (need == 2 && dg[v] > 0) return v;
    }
    return -1;
}

static void shuffle(int *x, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

/* Grow by one vertex on each side; wire each into spare capacity of the other side. */
static void add_pair(void) {
    int a = N, b = N + 1;
    N += 2;
    side[a] = 0;
    side[b] = 1;
    dg[a] = 0;
    dg[b] = 0;
    lst[0][cnt[0]++] = a;
    lst[1][cnt[1]++] = b;
    static int cand[MAXN];
    int nc = 0;
    for (int i = 0; i < cnt[1]; i++) {
        int v = lst[1][i];
        if (v != b && dg[v] < DEG) cand[nc++] = v;
    }
    shuffle(cand, nc);
    for (int i = 0; i < nc && dg[a] < DEG; i++) add_edge(a, cand[i]);
    nc = 0;
    for (int i = 0; i < cnt[0]; i++) {
        int v = lst[0][i];
        if (v != a && dg[v] < DEG) cand[nc++] = v;
    }
    shuffle(cand, nc);
    for (int i = 0; i < nc && dg[b] < DEG; i++) add_edge(b, cand[i]);
}

/* Propose a move and apply it. Returns 0 if nothing was applied. */
static int propose(void) {
    int r = rndint(100);
    mt = 0;
    if (r < 85) {
        int a1 = pick_from(0, 2), a2 = pick_from(0, 2);
        if (a1 < 0 || a2 < 0 || a1 == a2) return 0;
        int b1 = nbr[a1][rndint(dg[a1])];
        int b2 = nbr[a2][rndint(dg[a2])];
        if (b1 == b2 || M[a1][b2] || M[a2][b1]) return 0;
        del_edge(a1, b1);
        del_edge(a2, b2);
        add_edge(a1, b2);
        add_edge(a2, b1);
        mt = 1;
        mu1 = a1; mv1 = b1; mu2 = a2; mv2 = b2;
        return 1;
    } else if (r < 95) {
        int a = pick_from(0, 1), b = pick_from(1, 1);
        if (a < 0 || b < 0 || M[a][b]) return 0;
        add_edge(a, b);
        mt = 2;
        mu1 = a; mv1 = b;
        return 1;
    } else {
        int a = pick_from(0, 2);
        if (a < 0) return 0;
        int b = nbr[a][rndint(dg[a])];
        del_edge(a, b);
        mt = 3;
        mu1 = a; mv1 = b;
        return 1;
    }
}

static void undo_move(void) {
    if (mt == 1) {
        del_edge(mu1, mv2);
        del_edge(mu2, mv1);
        add_edge(mu1, mv1);
        add_edge(mu2, mv2);
    } else if (mt == 2) {
        del_edge(mu1, mv1);
    } else if (mt == 3) {
        add_edge(mu1, mv1);
    }
    mt = 0;
}

/* Simulated annealing on the bad-pair count. Returns 1 when cost reaches 0. */
static int anneal(void) {
    long long c = cost_eval();
    long it = 0;
    for (;;) {
        if (c == 0) return 1;
        if ((it & 63) == 0 && out_of_time()) return 0;
        double T = 1.5 * pow(0.15 / 1.5, (double)(it % CYCLE) / (double)CYCLE);
        it++;
        if (!propose()) continue;
        long long c2 = cost_eval();
        long long delta = c2 - c;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            c = c2;
        } else {
            undo_move();
        }
    }
}

static void save_best(void) {
    int m = 0;
    for (int v = 0; v < N; v++) {
        if (side[v] != 0) continue;
        for (int k = 0; k < dg[v] && m < MAXE; k++) {
            BU[m] = v;
            BV[m] = nbr[v][k];
            m++;
        }
    }
    bestN = N;
    bestM = m;
}

static void print_best(void) {
    if (bestN < 0) {
        printf("0 0\n");
        return;
    }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", BU[i], BV[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    dl_cpu = clock() + (clock_t)(tl * CLOCKS_PER_SEC);
    w0 = time(NULL);
    tl_wall = tl - 2.0;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    DEG = d;
    DIAM = D;
    if (d < 1 || d > MAXDEG || D < 2) {
        printf("0 0\n");
        return 0;
    }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    if (n0 == 0) {
        if (2 * d > MAXN - 4) {
            printf("0 0\n");
            return 0;
        }
        N = 2 * d;
        for (int i = 0; i < d; i++)
            for (int j = 0; j < d; j++) add_edge(i, d + j);
    } else {
        if (n0 < 1 || n0 > MAXN - 4) {
            printf("0 0\n");
            return 0;
        }
        N = n0;
        for (int i = 0; i < m0; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) break;
            if (u < 0 || v < 0 || u >= N || v >= N || u == v || M[u][v]) continue;
            if (dg[u] >= DEG || dg[v] >= DEG) continue;
            add_edge(u, v);
        }
    }

    /* Bipartition by BFS; odd cycle means we cannot continue. */
    static int col[MAXN], q[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        int h = 0, t = 0;
        col[s] = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int k = 0; k < dg[u]; k++) {
                int v = nbr[u][k];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    q[t++] = v;
                } else if (col[v] == col[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    cnt[0] = cnt[1] = 0;
    for (int v = 0; v < N; v++) {
        side[v] = col[v];
        lst[side[v]][cnt[side[v]]++] = v;
    }

    if (cost_eval() == 0) {
        save_best();
    } else if (anneal()) {
        save_best();
    }

    if (bestN >= 0) {
        while (!out_of_time() && N + 2 <= MAXN - 2) {
            add_pair();
            if (anneal()) {
                save_best();
            } else {
                break;
            }
        }
    }

    print_best();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions: arc-extended projective plane incidence graphs
# (diameter 3) and the generalized quadrangle W(q) (diameter 4).
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


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
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
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        arcs = _arc_extensions(d, t0 + 0.12 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:2]:
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Calibration cases already at the Moore bound return at once.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Grow-and-repair in C, starting from the best valid graph found above.
    budget_end = t0 + 0.85 * time_limit - 1.0
    remaining = budget_end - time.monotonic()
    if remaining > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best,
                             timeout=remaining + 0.1 * time_limit + 1.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
