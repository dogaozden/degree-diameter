import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bit-parallel simulated annealing that grows a valid bipartite graph.
#
# State: a bipartite graph with max degree d and a fixed side for every vertex.
# Cost = number of vertex pairs at distance > D (bitset BFS). Moves: add a free
# edge, rewire one endpoint of an edge onto a same-side vertex with spare degree,
# or double-swap two edges. When cost reaches 0 the graph is saved and one new
# vertex is added on the smaller side. The last zero-cost graph is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1200
#define MAXD 64
#define MAXW ((MAXN + 63) / 64)
#define T_HI 4.0
#define T_LO 0.5
#define STAG 200000L

static int d, D, cap, n;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t bufA[MAXN][MAXW];
static uint64_t bufB[MAXN][MAXW];
static int bu_best[MAXN * MAXD];
static int bv_best[MAXN * MAXD];
static int best_n = 0, best_m = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu_now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pop64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void reset_graph(void) {
    for (int v = 0; v < MAXN; v++) deg[v] = 0;
    n = 0;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adj[a][i] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void rem_one(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a][i] == b) {
            adj[a][i] = adj[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void del_edge(int a, int b) {
    rem_one(a, b);
    rem_one(b, a);
}

static int color_graph(void) {
    static int stk[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    stk[sp++] = v;
                } else if (col[v] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static int read_input(void) {
    int m = 0;
    reset_graph();
    if (scanf("%d %d", &n, &m) != 2) { reset_graph(); return 0; }
    if (n <= 0 || m <= 0 || n > cap) { reset_graph(); return 0; }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { reset_graph(); return 0; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { reset_graph(); return 0; }
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) { reset_graph(); return 0; }
        add_edge(u, v);
    }
    if (!color_graph()) { reset_graph(); return 0; }
    return 1;
}

static int build_kdd(void) {
    reset_graph();
    if (2 * d > cap) return 0;
    n = 2 * d;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            add_edge(i, d + j);
    color_graph();
    return 1;
}

static long eval_cost(void) {
    int W = (n + 63) / 64;
    uint64_t (*cur)[MAXW] = bufA;
    uint64_t (*nxt)[MAXW] = bufB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int step = 0; step < D; step++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pop64(cur[v][w]);
        tot += n - c;
    }
    return tot / 2;
}

static void save_best(void) {
    best_n = n;
    best_m = 0;
    for (int v = 0; v < n; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v][i];
            if (v < u) {
                bu_best[best_m] = v;
                bv_best[best_m] = u;
                best_m++;
            }
        }
    }
}

static void grow(void) {
    int a = 0, b = 0;
    for (int v = 0; v < n; v++) {
        if (col[v] == 0) a++;
        else b++;
    }
    int c;
    if (a < b) c = 0;
    else if (b < a) c = 1;
    else c = rndint(2);
    col[n] = c;
    deg[n] = 0;
    n++;
}

static int rand_deg_vertex(void) {
    for (int t = 0; t < 64; t++) {
        int v = rndint(n);
        if (deg[v] > 0) return v;
    }
    return -1;
}

static int accept(long delta, double T) {
    if (delta <= 0) return 1;
    return rnd01() < exp(-(double)delta / T);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    cap = (argc > 5) ? atoi(argv[5]) : MAXN;
    if (cap > MAXN) cap = MAXN;
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (D < 2 || d < 1 || d > MAXD) { printf("0 0\n"); return 0; }
    if (!read_input()) {
        if (!build_kdd()) { printf("0 0\n"); return 0; }
    }

    long cost = eval_cost();
    if (cost == 0) save_best();

    double tstart = cpu_now();
    double T = T_HI;
    long best_here = cost, stagn = 0, it = 0;

    while (1) {
        if ((it & 127) == 0 && cpu_now() - tstart > budget) break;
        it++;

        if (cost == 0) {
            save_best();
            if (n >= cap) break;
            grow();
            cost = eval_cost();
            best_here = cost;
            stagn = 0;
            T = T_HI;
            continue;
        }

        int r = rndint(100);
        if (r < 8) {
            /* free edge between opposite sides: never increases cost */
            int a = rndint(n), b = rndint(n);
            if (col[a] != col[b] && deg[a] < d && deg[b] < d && !has_edge(a, b)) {
                add_edge(a, b);
                cost = eval_cost();
            }
        } else if (r < 60) {
            /* rewire: edge (a,b) becomes (a,x), x on the same side as b */
            int a = rand_deg_vertex();
            if (a >= 0) {
                int b = adj[a][rndint(deg[a])];
                int x = -1;
                for (int t = 0; t < 30; t++) {
                    int c = rndint(n);
                    if (c != b && col[c] == col[b] && deg[c] < d && !has_edge(a, c)) {
                        x = c;
                        break;
                    }
                }
                if (x >= 0) {
                    del_edge(a, b);
                    add_edge(a, x);
                    long nc = eval_cost();
                    if (accept(nc - cost, T)) cost = nc;
                    else {
                        del_edge(a, x);
                        add_edge(a, b);
                    }
                }
            }
        } else {
            /* double swap: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), degrees preserved */
            int a1 = rand_deg_vertex();
            int a2 = rand_deg_vertex();
            if (a1 >= 0 && a2 >= 0 && a1 != a2 && col[a1] == col[a2]) {
                int b1 = adj[a1][rndint(deg[a1])];
                int b2 = adj[a2][rndint(deg[a2])];
                if (b1 != b2 && !has_edge(a1, b2) && !has_edge(a2, b1)) {
                    del_edge(a1, b1);
                    del_edge(a2, b2);
                    add_edge(a1, b2);
                    add_edge(a2, b1);
                    long nc = eval_cost();
                    if (accept(nc - cost, T)) cost = nc;
                    else {
                        del_edge(a1, b2);
                        del_edge(a2, b1);
                        add_edge(a1, b1);
                        add_edge(a2, b2);
                    }
                }
            }
        }

        T *= 0.99995;
        if (T < T_LO) T = T_LO;
        if (cost < best_here) {
            best_here = cost;
            stagn = 0;
        } else if (++stagn > STAG) {
            T = T_HI;
            stagn = 0;
        }
    }

    if (cost == 0) save_best();
    if (best_n <= 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bu_best[i], bv_best[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: arc-extended projective plane starts (diameter 3).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q)."""
    m2, edges = lib.projective_plane_incidence(q)
    m = m2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _loads_ok(S, s, m, point_lines, line_points):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy point set S with every line and point load at most s."""
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


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A-vertex per point of S and a new B-vertex per line of S."""
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


def _arc_candidates(d, rng, deadline):
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points = _pg_data(q)
        if s < 1:
            out.append((2 * m, list(edges)))
            continue
        S = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, optimal for D = 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2 or d == 1:
        return fallback

    rng = random.Random(seed * 7919 + d)
    try:
        cands = _arc_candidates(d, rng, t0 + 0.15 * time_limit)
    except Exception:
        cands = []
    cands = [c for c in cands if c[0] > 2 * d and lib.is_valid(c[0], c[1], d, D)]
    cands.sort(key=lambda t: -t[0])

    best = cands[0] if cands else fallback
    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback

    # Start for the C growth engine: alternate between the largest and the
    # second-largest arc graph so different seeds explore different growth paths.
    start = None
    if cands:
        start = cands[0]
        if seed % 2 == 1 and len(cands) > 1:
            start = cands[1]

    cap = min(lib.moore_bound(d, D), 1100)
    elapsed = time.monotonic() - t0
    budget = min(0.72 * time_limit - elapsed, time_limit - elapsed - 3.0)
    budget = max(0.3, budget)

    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", cap],
                        stdin_graph=start, timeout=budget + 4.0)
        n_o, e_o = lib.parse_graph_text(out)
        if n_o > best[0] and lib.is_valid(n_o, e_o, d, D):
            best = (n_o, e_o)
    except (RuntimeError, ValueError):
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
