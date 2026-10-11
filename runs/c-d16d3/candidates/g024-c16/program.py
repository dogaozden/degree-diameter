import random
import time

import lib


# Idea: edge-switch annealing with vertex insertion, run in C.
#
# The C engine keeps a valid bipartite graph with max degree d and tries to
# insert one more vertex at a time. Its moves are: add a cross edge (never
# hurts), switch two edges (a1,b1),(a2,b2) -> (a1,b2),(a2,b1) (keeps degrees),
# and re-attach one edge endpoint to a vertex with spare degree. The cost is
# the number of unordered pairs at distance > D, computed with bitset balls.
# On success the graph is saved and one more vertex is inserted. On failure
# the search restarts from the best saved graph with a fresh vertex.

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static int dg, DD;
static int MAXN, MAXE, MAXW;
static int n, m;
static int *ea, *eb, *col, *deg;
static unsigned char *mat;
static u64 *R, *T;
static u64 st = 0x9E3779B97F4A7C15ULL;
static double g_t0, g_budget;
static int bn, bm;
static int *bA, *bB, *bcol;
static long long cur;

#define MATI(a, b) ((size_t)(a) * MAXN + (b))

static u64 rnd64(void) { st ^= st << 13; st ^= st >> 7; st ^= st << 17; return st; }
static int rndint(int k) { return (int)(rnd64() % (u64)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static double clock_now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static long long eval_cost(void) {
    int W = (n + 63) >> 6;
    size_t sz = (size_t)n * W;
    memset(R, 0, sizeof(u64) * sz);
    for (int v = 0; v < n; v++) R[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DD; r++) {
        memcpy(T, R, sizeof(u64) * sz);
        for (int e = 0; e < m; e++) {
            size_t x = (size_t)ea[e] * W, y = (size_t)eb[e] * W;
            for (int w = 0; w < W; w++) {
                T[x + w] |= R[y + w];
                T[y + w] |= R[x + w];
            }
        }
        u64 *tmp = R; R = T; T = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(R[(size_t)v * W + w]);
        bad += n - c;
    }
    return bad / 2;
}

static void edge_replace(int i, int a, int b) {
    mat[MATI(ea[i], eb[i])] = 0;
    deg[ea[i]]--; deg[eb[i]]--;
    ea[i] = a; eb[i] = b;
    mat[MATI(a, b)] = 1;
    deg[a]++; deg[b]++;
}

static void edge_append(int a, int b) {
    ea[m] = a; eb[m] = b; m++;
    mat[MATI(a, b)] = 1;
    deg[a]++; deg[b]++;
}

static void clear_graph(void) {
    for (int e = 0; e < m; e++) mat[MATI(ea[e], eb[e])] = 0;
    m = 0;
    memset(deg, 0, sizeof(int) * MAXN);
}

static void save_best(void) {
    bn = n; bm = m;
    memcpy(bA, ea, sizeof(int) * m);
    memcpy(bB, eb, sizeof(int) * m);
    memcpy(bcol, col, sizeof(int) * n);
}

static void restore_best(void) {
    clear_graph();
    n = bn;
    memcpy(col, bcol, sizeof(int) * n);
    for (int e = 0; e < bm; e++) edge_append(bA[e], bB[e]);
}

static void set_default_best(void) {
    bn = 2; bm = 1;
    bA[0] = 0; bB[0] = 1;
    bcol[0] = 0; bcol[1] = 1;
}

static int accept(long long delta, double Tt) {
    if (delta <= 0) return 1;
    return rnd01() < exp(-(double)delta / Tt);
}

static int anneal(long long iters, double T0, double T1) {
    for (long long it = 0; it < iters && cur > 0; it++) {
        if ((it & 255) == 0 && clock_now() - g_t0 > g_budget) break;
        double Tt = T0 * pow(T1 / T0, (double)it / (double)iters);
        int r = rndint(100);
        if (r < 30) {
            int a = -1, b = -1;
            for (int t = 0; t < 60 && a < 0; t++) {
                int x = rndint(n), y = rndint(n);
                if (col[x] != 0 || col[y] != 1) continue;
                if (deg[x] >= dg || deg[y] >= dg) continue;
                if (mat[MATI(x, y)]) continue;
                a = x; b = y;
            }
            if (a >= 0 && m < MAXE) {
                edge_append(a, b);
                cur = eval_cost();
            }
        } else if (r < 70) {
            if (m < 2) continue;
            int i = rndint(m), j = rndint(m);
            if (i == j) continue;
            int a1 = ea[i], b1 = eb[i], a2 = ea[j], b2 = eb[j];
            if (a1 == a2 || b1 == b2) continue;
            if (mat[MATI(a1, b2)] || mat[MATI(a2, b1)]) continue;
            edge_replace(i, a1, b2);
            edge_replace(j, a2, b1);
            long long c2 = eval_cost();
            if (accept(c2 - cur, Tt)) cur = c2;
            else {
                edge_replace(i, a1, b1);
                edge_replace(j, a2, b2);
            }
        } else {
            if (m < 1) continue;
            int i = rndint(m), a = ea[i], b = eb[i];
            int na = a, nb = b, ok = 0;
            if (rndint(2) == 0) {
                for (int t = 0; t < 60 && !ok; t++) {
                    int x = rndint(n);
                    if (col[x] == 0 && deg[x] < dg && x != a && !mat[MATI(x, b)]) { na = x; ok = 1; }
                }
            } else {
                for (int t = 0; t < 60 && !ok; t++) {
                    int y = rndint(n);
                    if (col[y] == 1 && deg[y] < dg && y != b && !mat[MATI(a, y)]) { nb = y; ok = 1; }
                }
            }
            if (!ok) continue;
            edge_replace(i, na, nb);
            long long c2 = eval_cost();
            if (accept(c2 - cur, Tt)) cur = c2;
            else edge_replace(i, a, b);
        }
    }
    return cur == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dg = atoi(argv[1]);
    DD = atoi(argv[2]);
    st = (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (st == 0) st = 1;
    g_budget = atof(argv[4]);
    g_t0 = clock_now();
    if (dg < 1) dg = 1;
    if (DD < 2) DD = 2;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 0 || m0 < 0 || n0 > 1000000 || m0 > 20000000) { n0 = 0; m0 = 0; }
    int *tu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *tv = malloc(sizeof(int) * (size_t)(m0 + 1));
    int readok = 1;
    for (int e = 0; e < m0; e++) {
        if (scanf("%d %d", &tu[e], &tv[e]) != 2) { readok = 0; break; }
    }

    int base = n0 > 2 ? n0 : 2;
    MAXN = base + 3000;
    MAXE = MAXN * dg + 16;
    MAXW = (MAXN + 63) >> 6;
    ea = malloc(sizeof(int) * MAXE);
    eb = malloc(sizeof(int) * MAXE);
    bA = malloc(sizeof(int) * MAXE);
    bB = malloc(sizeof(int) * MAXE);
    col = calloc(MAXN, sizeof(int));
    bcol = calloc(MAXN, sizeof(int));
    deg = calloc(MAXN, sizeof(int));
    mat = calloc((size_t)MAXN * MAXN, 1);
    R = malloc(sizeof(u64) * (size_t)MAXN * MAXW);
    T = malloc(sizeof(u64) * (size_t)MAXN * MAXW);
    n = 0; m = 0;

    /* Validate the input graph: labels, no loops, degree <= dg, bipartite, no duplicates. */
    int ok = readok && n0 >= 2;
    if (ok) {
        for (int e = 0; e < m0 && ok; e++) {
            if (tu[e] < 0 || tu[e] >= n0 || tv[e] < 0 || tv[e] >= n0 || tu[e] == tv[e]) ok = 0;
        }
    }
    if (ok) {
        for (int e = 0; e < m0 && ok; e++) {
            deg[tu[e]]++; deg[tv[e]]++;
            if (deg[tu[e]] > dg || deg[tv[e]] > dg) ok = 0;
        }
        memset(deg, 0, sizeof(int) * MAXN);
    }
    if (ok) {
        for (int v = 0; v < n0; v++) col[v] = -1;
        for (int s = 0; s < n0; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int changed = 1;
            while (changed) {
                changed = 0;
                for (int e = 0; e < m0; e++) {
                    int u = tu[e], v = tv[e];
                    if (col[u] >= 0 && col[v] < 0) { col[v] = 1 - col[u]; changed = 1; }
                    else if (col[v] >= 0 && col[u] < 0) { col[u] = 1 - col[v]; changed = 1; }
                }
            }
        }
        for (int e = 0; e < m0 && ok; e++) if (col[tu[e]] == col[tv[e]]) ok = 0;
    }

    set_default_best();
    if (ok) {
        n = n0;
        for (int e = 0; e < m0 && ok; e++) {
            int a, b;
            if (col[tu[e]] == 0) { a = tu[e]; b = tv[e]; }
            else { a = tv[e]; b = tu[e]; }
            if (mat[MATI(a, b)]) { ok = 0; break; }
            edge_append(a, b);
        }
    }
    if (!ok) {
        clear_graph();
        n = 2;
        col[0] = 0; col[1] = 1;
        edge_append(0, 1);
    }

    cur = eval_cost();
    if (cur == 0) save_best();
    if (cur > 0) {
        anneal(20000, 2.5, 0.08);
        if (cur == 0) save_best();
    }

    /* Main loop: restore best, insert one vertex, anneal. */
    while (clock_now() - g_t0 < g_budget) {
        restore_best();
        if (n + 1 >= MAXN) break;
        int side = rndint(2);
        col[n] = side;
        deg[n] = 0;
        n++;
        cur = eval_cost();
        if (anneal(4000, 2.5, 0.08)) save_best();
    }

    printf("%d %d\n", bn, bm);
    for (int e = 0; e < bm; e++) printf("%d %d\n", bA[e], bB[e]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), used as the
# starting point for the C search.
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


def build(d, D, seed, time_limit):
    start = time.monotonic()

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

    if D >= 3:
        arcs = _arc_extensions(d, start + 0.10 * time_limit,
                               random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)

    # Edge-switch annealing with vertex insertion in C, starting from the best graph.
    if D >= 2:
        left = 0.80 * time_limit - (time.monotonic() - start) - 1.5
        if left > 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(left, 2)],
                                stdin_graph=best, timeout=left + 10.0)
                consider(*lib.parse_graph_text(out))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
