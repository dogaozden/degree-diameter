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
#         q+1 lines through P. Every line holds <= s points of SA.
# B-side: a set SB of lines. Each j in SB gets a new vertex joined to all
#         q+1 points on j. Every point lies on <= s lines of SB.
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
# C engine: greedy vertex insertion with an exact local diameter check.
#
# Adding a vertex v never increases an old distance, so a graph stays valid
# iff the new vertex reaches everything within D. For a new vertex on side s,
# v chooses neighbours N among spare vertices of the opposite side. The C
# code grows N greedily by coverage (bitset BFS from v), with randomized
# tie-breaking and score noise, and keeps trying until time runs out.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 1024
#define W 16
#define MAXD 128

typedef uint64_t u64;

static int n, d, D;
static int side_[MAXN];
static int deg_[MAXN];
static int nb[MAXN][MAXD];
static u64 adjb[MAXN][W];
static u64 rs = 88172645463325252ULL;
static int cand_buf[MAXN];
static char used_buf[MAXN];

static u64 rnd(void)
{
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double rnd01(void)
{
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static int popc64(u64 x)
{
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int bs_count(const u64 *b)
{
    int c = 0;
    for (int i = 0; i < W; i++) c += popc64(b[i]);
    return c;
}

static int bs_get(const u64 *b, int i) { return (int)((b[i >> 6] >> (i & 63)) & 1ULL); }
static void bs_set(u64 *b, int i) { b[i >> 6] |= 1ULL << (i & 63); }

/* Number of graph vertices within distance D of a new vertex whose neighbours are N. */
static int reach_count(const u64 *N)
{
    u64 seen[W], frontier[W], nxt[W];
    memcpy(seen, N, sizeof seen);
    memcpy(frontier, N, sizeof frontier);
    for (int t = 2; t <= D; t++) {
        int any = 0;
        memset(nxt, 0, sizeof nxt);
        for (int w = 0; w < W; w++) {
            u64 x = frontier[w];
            if (!x) continue;
            for (int b = 0; b < 64; b++) {
                if (!((x >> b) & 1ULL)) continue;
                int v = w * 64 + b;
                for (int j = 0; j < W; j++) nxt[j] |= adjb[v][j];
            }
        }
        for (int j = 0; j < W; j++) {
            nxt[j] &= ~seen[j];
            seen[j] |= nxt[j];
            if (nxt[j]) any = 1;
        }
        if (!any) break;
        memcpy(frontier, nxt, sizeof frontier);
    }
    return bs_count(seen);
}

/* Try to choose up to d spare vertices on side 1-s that cover the whole graph within D. */
static int try_insert(int s, int *chosen, int *nch)
{
    int nc = 0;
    for (int v = 0; v < n; v++)
        if (side_[v] != s && deg_[v] < d) cand_buf[nc++] = v;
    *nch = 0;
    if (nc == 0) return 0;
    memset(used_buf, 0, sizeof used_buf);
    double amp = (rnd() & 1ULL) ? 0.9 : 2.5;
    u64 N[W];
    memset(N, 0, sizeof N);
    int k = 0, cov = 0;
    while (k < d) {
        int best = -1, bestcov = -1;
        double bestsc = -1e300;
        for (int i = 0; i < nc; i++) {
            int c = cand_buf[i];
            if (used_buf[c]) continue;
            u64 T[W];
            memcpy(T, N, sizeof T);
            bs_set(T, c);
            int cv = reach_count(T);
            double sc = cv + amp * rnd01();
            if (sc > bestsc) { bestsc = sc; best = c; bestcov = cv; }
        }
        if (best < 0) break;
        used_buf[best] = 1;
        bs_set(N, best);
        chosen[k++] = best;
        cov = bestcov;
        if (cov == n) break;
    }
    *nch = k;
    return cov == n;
}

static void insert_vertex(int s, const int *chosen, int k)
{
    int v = n;
    side_[v] = s;
    deg_[v] = 0;
    memset(adjb[v], 0, sizeof adjb[v]);
    for (int i = 0; i < k; i++) {
        int c = chosen[i];
        nb[v][deg_[v]++] = c;
        nb[c][deg_[c]++] = v;
        bs_set(adjb[v], c);
        bs_set(adjb[c], v);
    }
    n++;
}

static int read_input(void)
{
    int m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 0 || n >= MAXN || m < 0) return 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (bs_get(adjb[u], v)) return 0;
        if (deg_[u] >= d || deg_[v] >= d) return 0;
        nb[u][deg_[u]++] = v;
        nb[v][deg_[v]++] = u;
        bs_set(adjb[u], v);
        bs_set(adjb[v], u);
    }
    return 1;
}

static int color_graph(void)
{
    static int queue[MAXN];
    for (int v = 0; v < n; v++) side_[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side_[s] >= 0) continue;
        int qh = 0, qt = 0;
        side_[s] = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg_[u]; i++) {
                int v = nb[u][i];
                if (side_[v] < 0) {
                    side_[v] = 1 - side_[u];
                    queue[qt++] = v;
                } else if (side_[v] == side_[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

int main(int argc, char **argv)
{
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    n = 0;
    if (!read_input() || n < 1 || !color_graph()) { printf("0 0\n"); return 0; }

    clock_t t0 = clock();
    while (n < MAXN) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (el >= budget) break;
        int sp[2] = {0, 0};
        for (int v = 0; v < n; v++)
            if (deg_[v] < d) sp[side_[v]]++;
        if (!sp[0] && !sp[1]) break;
        int s;
        if (sp[0] && sp[1]) s = (int)(rnd() & 1ULL);
        else s = sp[0] ? 1 : 0;   /* new vertex on side s needs spare on side 1-s */
        int chosen[MAXD];
        int k = 0;
        if (try_insert(s, chosen, &k)) insert_vertex(s, chosen, k);
    }

    int m2 = 0;
    for (int u = 0; u < n; u++) m2 += deg_[u];
    m2 /= 2;
    printf("%d %d\n", n, m2);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg_[u]; i++)
            if (u < nb[u][i]) printf("%d %d\n", u, nb[u][i]);
    return 0;
}
"""


def _insert_search(graph, d, D, seed, budget):
    """Run the C insertion search from `graph` for about `budget` seconds of CPU time."""
    out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                    stdin_graph=graph, timeout=budget + 5.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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

    rng = random.Random(seed * 7919 + d)
    if D >= 3:
        arc_deadline = t0 + 0.2 * time_limit
        for n_c, e_c in _arc_extensions(d, arc_deadline, rng):
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < t0 + 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Greedy vertex insertion in C, seeded with the best valid graph found so far.
    remaining = 0.72 * time_limit - (time.monotonic() - t0)
    if remaining >= 1.0 and best_n >= 2:
        try:
            n2, e2 = _insert_search(best, d, D, seed, remaining - 0.5)
            consider(n2, e2)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
