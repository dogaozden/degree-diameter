"""Diameter-D bipartite search: arc/GQ starts plus simulated annealing on edge rewiring.

Starts are valid graphs (arc-extended PG(2,q) incidence for D >= 3, the generalized quadrangle
for D >= 4, or K_{d,d}). The C engine works on a fixed bipartition and minimizes the number of
vertex pairs at distance > D, using degree-preserving 2-switches and simulated annealing. Once
the count reaches zero, it records the valid graph and grows by one vertex per side (a
degree-preserving split of a matching of d edges), then anneals again. Every snapshot is valid
by construction and Python re-checks it with lib.is_valid before returning. If the search finds
nothing larger, the start graph is returned.
"""
import itertools
import random
import time

import lib

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXW 16
#define MAXDEG 64
#define MAXE 40000
#define EPOCH 20000
#define THI 2.0
#define TLO 0.10

static int N, Dd, Dist, WW;
static int side[MAXN];
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static uint64_t nbr[MAXN][MAXW];
static uint64_t BUF0[MAXN][MAXW], BUF1[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static int inU[MAXE], inV[MAXE], inM = 0;
static int bestU[MAXE], bestV[MAXE], bestM = 0, bestN = -1;
static int stA[MAXN], stB[MAXN], gst = 0;
static int qbuf[MAXN];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double wall(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int isadj(int u, int v) {
    return (int)((nbr[u][v >> 6] >> (v & 63)) & 1ULL);
}

static void addedge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
    nbr[u][v >> 6] |= 1ULL << (v & 63);
    nbr[v][u >> 6] |= 1ULL << (u & 63);
}

static void deledge_one(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adj[u][k] == v) {
            adj[u][k] = adj[u][--deg[u]];
            break;
        }
    }
}

static void remedge(int u, int v) {
    deledge_one(u, v);
    deledge_one(v, u);
    nbr[u][v >> 6] &= ~(1ULL << (v & 63));
    nbr[v][u >> 6] &= ~(1ULL << (u & 63));
}

/* Number of unordered pairs at distance > Dist. */
static int evalbad(void) {
    int W = WW;
    uint64_t (*cur)[MAXW] = BUF0;
    uint64_t (*nx)[MAXW] = BUF1;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = nbr[v][w];
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 1; r < Dist; r++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) nx[v][w] = cur[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int w = 0; w < W; w++) nx[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nx;
        nx = t;
    }
    long cnt = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        cnt += N - c;
    }
    return (int)(cnt / 2);
}

static int pick0(void) {
    for (int t = 0; t < 4000; t++) {
        int a = rndint(N);
        if (side[a] == 0 && deg[a] > 0) return a;
    }
    return -1;
}

/* Degree-preserving 2-switch on a random pair of edges, accepted by Metropolis rule. */
static void try_switch(double T, int *cur) {
    int a1 = pick0();
    if (a1 < 0) return;
    int a2 = pick0();
    if (a2 < 0 || a1 == a2) return;
    int b1 = adj[a1][rndint(deg[a1])];
    int b2 = adj[a2][rndint(deg[a2])];
    if (b1 == b2 || isadj(a1, b2) || isadj(a2, b1)) return;
    remedge(a1, b1);
    remedge(a2, b2);
    addedge(a1, b2);
    addedge(a2, b1);
    int nb = evalbad();
    int delta = nb - *cur;
    if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
        *cur = nb;
        return;
    }
    remedge(a1, b2);
    remedge(a2, b1);
    addedge(a1, b1);
    addedge(a2, b2);
}

/* Add edges between non-adjacent spare vertices on opposite sides (never hurts distances). */
static void fill(void) {
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int a = 0; a < N; a++) {
            if (side[a] != 0) continue;
            for (int b = 0; b < N && deg[a] < Dd; b++) {
                if (side[b] != 1 || deg[b] >= Dd || isadj(a, b)) continue;
                addedge(a, b);
                changed = 1;
            }
        }
    }
}

/* Add two vertices x (side 0) and y (side 1), each of degree Dd, by splitting a matching
   of Dd edges (a_i, b_i): x joins b_i, y joins a_i. Degrees of old vertices are unchanged. */
static int grow(void) {
    if (N + 2 > MAXN - 2) return 0;
    gst++;
    int A[MAXDEG], B[MAXDEG], k = 0;
    int start = rndint(N);
    for (int t = 0; t < N && k < Dd; t++) {
        int a = (start + t) % N;
        if (side[a] != 0 || deg[a] == 0 || stA[a] == gst) continue;
        int off = rndint(deg[a]);
        for (int j = 0; j < deg[a]; j++) {
            int b = adj[a][(off + j) % deg[a]];
            if (stB[b] == gst) continue;
            stA[a] = gst;
            stB[b] = gst;
            A[k] = a;
            B[k] = b;
            k++;
            break;
        }
    }
    if (k < Dd) return 0;
    int x = N, y = N + 1;
    N += 2;
    WW = (N + 63) / 64;
    side[x] = 0;
    side[y] = 1;
    deg[x] = 0;
    deg[y] = 0;
    for (int i = 0; i < k; i++) {
        remedge(A[i], B[i]);
        addedge(x, B[i]);
        addedge(A[i], y);
    }
    return 1;
}

static int collect(int *U, int *V) {
    int M = 0;
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < deg[v]; k++) {
            int u = adj[v][k];
            if (u > v && M < MAXE) {
                U[M] = v;
                V[M] = u;
                M++;
            }
        }
    }
    return M;
}

static void snapshot(void) {
    bestM = collect(bestU, bestV);
    bestN = N;
}

static int assign_sides(void) {
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        qbuf[t++] = s;
        while (h < t) {
            int u = qbuf[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    qbuf[t++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    if (Dd < 1) Dd = 1;
    if (Dd > MAXDEG - 2) Dd = MAXDEG - 2;
    Dist = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) n0 = 0;
    if (n0 <= 0 || n0 > MAXN - 4 || Dist < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= Dd || deg[v] >= Dd || isadj(u, v)) continue;
        addedge(u, v);
    }
    WW = (N + 63) / 64;
    inM = collect(inU, inV);

    if (!assign_sides()) {
        printf("%d %d\n", n0, inM);
        for (int i = 0; i < inM; i++) printf("%d %d\n", inU[i], inV[i]);
        return 0;
    }

    fill();
    int cur = evalbad();
    if (cur == 0) snapshot();

    double t_end = wall() + budget;
    while (wall() < t_end) {
        if (cur == 0) {
            if (N > bestN) snapshot();
            if (!grow()) break;
            fill();
            cur = evalbad();
            continue;
        }
        for (int it = 0; it < EPOCH && cur > 0; it++) {
            double T = THI * pow(TLO / THI, (double)it / (double)EPOCH);
            try_switch(T, &cur);
            if ((it & 31) == 0 && wall() >= t_end) break;
        }
    }
    if (cur == 0 && N > bestN) snapshot();

    if (bestN < 0) {
        printf("%d %d\n", n0, inM);
        for (int i = 0; i < inM; i++) printf("%d %d\n", inU[i], inV[i]);
    } else {
        printf("%d %d\n", bestN, bestM);
        for (int i = 0; i < bestM; i++) printf("%d %d\n", bestU[i], bestV[i]);
    }
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
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4), used for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
# Annealing driver.
# ----------------------------------------------------------------------------

def _anneal(n0, e0, d, D, seed, budget, timeout):
    """Run the C annealer from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=timeout)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.80 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))

    starts = []
    if D >= 3:
        starts.extend(_arc_extensions(d, t0 + 0.20 * time_limit, rng))
    if D >= 4 and time.monotonic() < t0 + 0.25 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    starts = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    if lib.is_valid(fallback[0], fallback[1], d, D):
        starts.append(fallback)
    if not starts:
        return 1, []
    best = max(starts, key=lambda g: g[0])

    # Known optimum reached: nothing to search for.
    if best[0] >= lib.moore_bound(d, D):
        return best

    remaining = hard_end - time.monotonic()
    if remaining >= 3.0 and d >= 2:
        budget = remaining - 1.5
        try:
            n1, e1 = _anneal(best[0], best[1], d, D, seed * 31 + 1, budget, budget + 4.0)
            if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                best = (n1, e1)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
