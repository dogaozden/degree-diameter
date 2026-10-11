import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). With d >= q+1 each old vertex has
# spare capacity s = d - q - 1. Choose a point set S in which every line holds
# at most s points of S. For each P in S add a new A-vertex joined to the q+1
# lines through P, and for each j in S add a new B-vertex joined to the q+1
# points on line j. Order is 2(q^2+q+1) + 2|S|.
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
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
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
# C engine: grow a valid bipartite graph one vertex at a time.
#
# Starting from the input graph, each stage adds one vertex on a random side,
# joins it to free vertices on the other side, then runs simulated annealing
# on rewiring moves (replace one endpoint of an edge, or add an edge between
# two free vertices). Cost = number of ordered vertex pairs at distance > D,
# computed with bitsets. Degrees never exceed d and the graph stays bipartite
# by construction. When cost reaches 0 the graph is saved and the next stage
# grows it again. Otherwise the search restores the last saved graph and retries.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1600
#define MAXW ((MAXN + 63) / 64)
#define STAGE_ITERS 20000

static int dd = 1, DD = 1;
static int n = 0;
static int side[MAXN];
static int deg[MAXN];
static int *nb = NULL;
static uint64_t R[2][MAXN][MAXW];
static int bn = 0;
static int bside[MAXN], bdeg[MAXN];
static int *bnb = NULL;
static int mt = 0, ma = 0, mb = 0, mc = 0;
static uint64_t rs = 88172645463325252ULL;
static double t0c = 0.0;
static int cand[MAXN];

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)clock() / CLOCKS_PER_SEC - t0c; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    const int *row = nb + (size_t)a * dd;
    for (int i = 0; i < deg[a]; i++) if (row[i] == b) return 1;
    return 0;
}
static void add_edge(int a, int b) {
    nb[(size_t)a * dd + deg[a]++] = b;
    nb[(size_t)b * dd + deg[b]++] = a;
}
static void del_one(int a, int b) {
    int *row = nb + (size_t)a * dd;
    for (int i = 0; i < deg[a]; i++) {
        if (row[i] == b) { row[i] = row[deg[a] - 1]; deg[a]--; return; }
    }
}
static void remove_edge(int a, int b) { del_one(a, b); del_one(b, a); }

static long long cost_eval(void) {
    int W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) R[0][v][w] = 0;
        R[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    int cur = 0;
    for (int s = 0; s < DD; s++) {
        int nx = cur ^ 1;
        for (int v = 0; v < n; v++) {
            uint64_t *out = R[nx][v];
            const uint64_t *in = R[cur][v];
            for (int w = 0; w < W; w++) out[w] = in[w];
            const int *row = nb + (size_t)v * dd;
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = R[cur][row[i]];
                for (int w = 0; w < W; w++) out[w] |= src[w];
            }
        }
        cur = nx;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc(R[cur][v][w]);
        bad += n - pc;
    }
    return bad;
}

static int pick_partner(int a) {
    for (int t = 0; t < 100; t++) {
        int c = rint_(n);
        if (c != a && side[c] != side[a] && deg[c] < dd && !has_edge(a, c)) return c;
    }
    return -1;
}

static int random_move(void) {
    int a = rint_(n);
    if (deg[a] > 0 && (rnd64() & 1)) {
        int b = nb[(size_t)a * dd + rint_(deg[a])];
        int c = pick_partner(a);
        if (c < 0) return 0;
        remove_edge(a, b);
        add_edge(a, c);
        mt = 1; ma = a; mb = b; mc = c;
        return 1;
    }
    if (deg[a] >= dd) return 0;
    int c = pick_partner(a);
    if (c < 0) return 0;
    add_edge(a, c);
    mt = 2; ma = a; mc = c;
    return 1;
}

static void undo_move(void) {
    if (mt == 1) { remove_edge(ma, mc); add_edge(ma, mb); }
    else if (mt == 2) remove_edge(ma, mc);
}

static int color_graph(void) {
    int *q = malloc(sizeof(int) * (size_t)(n > 0 ? n : 1));
    for (int v = 0; v < n; v++) side[v] = -1;
    int ok = 1;
    for (int s = 0; s < n && ok; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail && ok) {
            int u = q[head++];
            for (int i = 0; i < deg[u]; i++) {
                int w = nb[(size_t)u * dd + i];
                if (side[w] < 0) { side[w] = 1 - side[u]; q[tail++] = w; }
                else if (side[w] == side[u]) { ok = 0; break; }
            }
        }
    }
    free(q);
    return ok;
}

static void save_best(void) {
    bn = n;
    for (int v = 0; v < n; v++) {
        bside[v] = side[v];
        bdeg[v] = deg[v];
        memcpy(bnb + (size_t)v * dd, nb + (size_t)v * dd, sizeof(int) * (size_t)dd);
    }
}

static void restore_best(void) {
    n = bn;
    for (int v = 0; v < n; v++) {
        side[v] = bside[v];
        deg[v] = bdeg[v];
        memcpy(nb + (size_t)v * dd, bnb + (size_t)v * dd, sizeof(int) * (size_t)dd);
    }
}

static void grow_vertex(void) {
    int x = n;
    n++;
    side[x] = (int)(rnd64() & 1);
    deg[x] = 0;
    int cnt = 0;
    for (int v = 0; v < x; v++)
        if (side[v] != side[x] && deg[v] < dd) cand[cnt++] = v;
    for (int i = cnt - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    for (int i = 0; i < cnt && deg[x] < dd; i++) add_edge(x, cand[i]);
}

static int sa_stage(long long iters, double deadline) {
    long long cur = cost_eval();
    const double T0 = 3.0, T1 = 0.05;
    for (long long it = 0; it < iters && cur > 0; it++) {
        if ((it & 127) == 0 && elapsed() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        if (!random_move()) continue;
        long long c2 = cost_eval();
        long long delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = c2;
        else undo_move();
    }
    return cur == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    dd = d; DD = D;
    if (dd < 1 || DD < 1) { printf("0 0\n"); return 0; }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || n0 >= MAXN || m0 < 0) {
        printf("0 0\n"); return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *cnt = calloc((size_t)n0, sizeof(int));
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { printf("0 0\n"); return 0; }
        if (eu[i] < 0 || eu[i] >= n0 || ev[i] < 0 || ev[i] >= n0 || eu[i] == ev[i]) {
            printf("0 0\n"); return 0;
        }
        cnt[eu[i]]++; cnt[ev[i]]++;
    }
    for (int v = 0; v < n0; v++) if (cnt[v] > dd) { printf("0 0\n"); return 0; }

    nb = malloc(sizeof(int) * (size_t)MAXN * dd);
    bnb = malloc(sizeof(int) * (size_t)MAXN * dd);
    n = n0;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m0; i++) if (!has_edge(eu[i], ev[i])) add_edge(eu[i], ev[i]);
    if (!color_graph()) { printf("0 0\n"); return 0; }

    t0c = (double)clock() / CLOCKS_PER_SEC;
    double budget = tl * 0.9 - 0.2;
    if (budget < 0.1) budget = 0.1;

    save_best();
    while (elapsed() < budget && bn + 1 < MAXN) {
        restore_best();
        grow_vertex();
        if (sa_stage(STAGE_ITERS, budget)) save_best();
    }

    long long mo = 0;
    for (int v = 0; v < bn; v++)
        for (int i = 0; i < bdeg[v]; i++)
            if (bnb[(size_t)v * dd + i] > v) mo++;
    printf("%d %lld\n", bn, mo);
    for (int v = 0; v < bn; v++)
        for (int i = 0; i < bdeg[v]; i++) {
            int u = bnb[(size_t)v * dd + i];
            if (u > v) printf("%d %d\n", v, u);
        }
    return 0;
}
"""


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

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

    # Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        for n_c, e_c in sorted(_arc_extensions(d, start + 0.2 * time_limit,
                                               random.Random(seed * 7919 + d)),
                               key=lambda t: -t[0]):
            consider(n_c, e_c)

    # Generalized quadrangle baseline (diameter 4).
    if D >= 4 and time.monotonic() < start + 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Grow the best graph with the C engine, using most of the remaining time.
    elapsed = time.monotonic() - start
    c_budget = time_limit * 0.8 - elapsed
    if c_budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                             stdin_graph=best, timeout=time_limit * 0.9 - elapsed)
            n_c, e_c = lib.parse_graph_text(text)
            consider(n_c, e_c)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
