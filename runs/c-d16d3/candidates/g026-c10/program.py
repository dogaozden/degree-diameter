import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: grow-and-repair vertex insertion for bipartite graphs of
# max degree d and diameter D.
#
# State: a bipartite graph (colours fixed per vertex). Cost = number of ordered
# vertex pairs at distance > D (bitset ball computation, cheap for n ~ 500).
# Loop:
#   * a valid state is snapshotted, then a new vertex is inserted on one side,
#     joined to d vertices of the other side (evicting one edge at each full
#     target so its partner gets spare capacity), then spare slots are filled;
#   * simulated annealing repairs the state with degree-preserving edge swaps
#     (a-b, c-e -> a-e, c-b) and with greedy edge additions (never raise cost);
#   * if repair stalls, the best valid snapshot is restored and a new vertex is tried.
# The output is always the largest valid snapshot, so it never gets worse than the start.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXV 2048
#define MAXD 48
#define MAXW (MAXV / 64)
#define STALL 3000

static int DEG, DIAM, N;
static int deg[MAXV], adj[MAXV][MAXD], col[MAXV];
static uint64_t bufA[MAXV][MAXW], bufB[MAXV][MAXW];
static int snapN, sdeg[MAXV], sadj[MAXV][MAXD];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) / 9007199254740992.0; }

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static void shuffle(int *x, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = x[i]; x[i] = x[j]; x[j] = t;
    }
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) return 1;
    return 0;
}
static void drop(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a][i] == b) { adj[a][i] = adj[a][--deg[a]]; return; }
    }
}
static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}
static void remove_edge(int a, int b) { drop(a, b); drop(b, a); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of ordered pairs (v,w) with dist(v,w) > DIAM (unreachable counts). 0 = valid. */
static long long eval_bad(void) {
    int nw = (N + 63) >> 6;
    uint64_t (*A)[MAXW] = bufA, (*B)[MAXW] = bufB, (*T)[MAXW];
    for (int v = 0; v < N; v++) {
        memset(A[v], 0, sizeof(uint64_t) * (size_t)nw);
        A[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            memcpy(B[v], A[v], sizeof(uint64_t) * (size_t)nw);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = A[adj[v][i]];
                for (int w = 0; w < nw; w++) B[v][w] |= src[w];
            }
        }
        T = A; A = B; B = T;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += popc(A[v][w]);
        bad += N - c;
    }
    return bad;
}

/* Proper 2-colouring by BFS. Returns 0 if the graph is not bipartite. */
static int colour_all(void) {
    static int q[MAXV];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) { col[v] = 1 - col[u]; q[t++] = v; }
                else if (col[v] == col[u]) return 0;
            }
        }
    }
    return 1;
}

static void save_state(void) {
    snapN = N;
    memcpy(sdeg, deg, sizeof(int) * (size_t)N);
    memcpy(sadj, adj, sizeof(int) * (size_t)MAXD * (size_t)N);
}
static void restore_state(void) {
    N = snapN;
    memcpy(deg, sdeg, sizeof(int) * (size_t)N);
    memcpy(adj, sadj, sizeof(int) * (size_t)MAXD * (size_t)N);
}

/* Greedy saturation: add any missing opposite-colour edge between vertices with spare degree.
   Never increases the distance between any pair, so validity is preserved. */
static void fill_spare(void) {
    static int s0[MAXV], s1[MAXV];
    int n0 = 0, n1 = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < DEG) {
            if (col[v] == 0) s0[n0++] = v; else s1[n1++] = v;
        }
    }
    shuffle(s0, n0);
    shuffle(s1, n1);
    for (int i = 0; i < n0; i++) {
        int a = s0[i];
        for (int j = 0; j < n1 && deg[a] < DEG; j++) {
            int b = s1[j];
            if (deg[b] < DEG && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* Insert a new vertex on a random side, joined to DEG vertices of the other side.
   A full target first gives up one random edge (its partner gets spare capacity). */
static void grow_vertex(void) {
    static int cand[MAXV];
    if (N >= MAXV - 2) return;
    int c = rndint(2);
    int z = N;
    N++;
    deg[z] = 0;
    col[z] = c;
    int nc = 0;
    for (int v = 0; v < z; v++) if (col[v] == 1 - c) cand[nc++] = v;
    int need = DEG < nc ? DEG : nc;
    for (int i = 0; i < need; i++) {
        int j = i + rndint(nc - i);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
        int tv = cand[i];
        if (deg[tv] >= DEG) {
            int s = adj[tv][rndint(deg[tv])];
            remove_edge(tv, s);
        }
        add_edge(z, tv);
    }
}

/* Degree-preserving swap: (a,b),(c,e) -> (a,e),(c,b), a,c on colour 0. */
static int move_swap(int *o) {
    int x = rndint(N);
    if (!deg[x]) return 0;
    int y = adj[x][rndint(deg[x])];
    int a = (col[x] == 0) ? x : y;
    int b = (col[x] == 0) ? y : x;
    int z = rndint(N);
    if (!deg[z]) return 0;
    int w = adj[z][rndint(deg[z])];
    int c = (col[z] == 0) ? z : w;
    int e = (col[z] == 0) ? w : z;
    if (a == c || b == e) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    remove_edge(a, b);
    remove_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    o[0] = a; o[1] = b; o[2] = c; o[3] = e;
    return 1;
}
static void undo_swap(const int *o) {
    int a = o[0], b = o[1], c = o[2], e = o[3];
    remove_edge(a, e);
    remove_edge(c, b);
    add_edge(a, b);
    add_edge(c, e);
}

/* Random edge addition between spare vertices of opposite colour (cost never rises). */
static int move_fill(void) {
    int x = rndint(N), y = rndint(N);
    if (col[x] == col[y] || deg[x] >= DEG || deg[y] >= DEG || has_edge(x, y)) return 0;
    add_edge(x, y);
    return 1;
}

static void build_kdd(int d) {
    N = 2 * d;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) add_edge(i, d + j);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (d < 1 || d >= MAXD || DIAM < 2) {
        printf("1 0\n");
        return 0;
    }
    DEG = d;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    double t0 = now_sec();

    int n = 0, m = 0, ok = 1;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n <= 0 || n > MAXV - 400 || m < 0) ok = 0;
    if (ok) {
        N = n;
        for (int v = 0; v < n; v++) deg[v] = 0;
        for (int i = 0; i < m && ok; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
            if (u < 0 || u >= n || v < 0 || v >= n || u == v ||
                deg[u] >= DEG || deg[v] >= DEG || has_edge(u, v)) ok = 0;
            else add_edge(u, v);
        }
        if (ok && !colour_all()) ok = 0;
    }
    if (!ok) build_kdd(d);
    colour_all();

    fill_spare();
    long long cost = eval_bad();
    if (cost != 0) {
        /* Start is unusable: fall back to K_{d,d}, valid for DIAM >= 2. */
        build_kdd(d);
        colour_all();
        fill_spare();
        cost = eval_bad();
    }
    save_state();

    double T = 1.0;
    long long steps = 0, last_imp = 0, best_try = cost;
    while (now_sec() - t0 < budget) {
        if (cost == 0) {
            if (N > snapN) save_state();
            if (N >= MAXV - 2) break;
            grow_vertex();
            fill_spare();
            cost = eval_bad();
            T = 1.0;
            best_try = cost;
            last_imp = steps;
            continue;
        }
        steps++;
        int o[4];
        if (rndint(10) < 8) {
            if (!move_swap(o)) continue;
            long long nc = eval_bad();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) cost = nc;
            else undo_swap(o);
        } else {
            if (!move_fill()) continue;
            cost = eval_bad();
        }
        if (cost < best_try) { best_try = cost; last_imp = steps; }
        if (steps - last_imp > STALL) {
            restore_state();
            colour_all();
            cost = eval_bad();
            T = 1.0;
            best_try = cost;
            last_imp = steps;
        }
        if (T > 0.2) T *= 0.9995;
    }

    int sm = 0;
    for (int v = 0; v < snapN; v++) sm += sdeg[v];
    printf("%d %d\n", snapN, sm / 2);
    for (int v = 0; v < snapN; v++)
        for (int i = 0; i < sdeg[v]; i++)
            if (v < sadj[v][i]) printf("%d %d\n", v, sadj[v][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python construction: arc-extended projective plane incidence graphs (D = 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has spare capacity
# s = d - q - 1. Pick a point set S with every line holding <= s points of S
# (and, by polarity, every point on <= s lines of S). For each P in S add a new
# A-vertex joined to the q+1 lines through P; for each j in S add a new B-vertex
# joined to the q+1 points on line j. Order 2(q^2+q+1) + 2|S|. A conic (plus the
# nucleus for even q) gives |S| = q+1 for s = 2, which is 394 for d = 16.
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
    """True if every line holds <= s points of S and every point lies on <= s lines of S."""
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
    """Conic (plus nucleus for even q): an arc in which no three points are collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex for each element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        y = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, y))
    return n, E


def _arc_candidates(d, deadline, rng):
    """Return (n, edges) for each prime power q with q + 1 <= d (diameter 3)."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q) or time.monotonic() > deadline:
            continue
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    hard = t0 + 0.9 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])

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
        for n_c, e_c in sorted(_arc_candidates(d, t0 + 0.25 * time_limit, rng),
                               key=lambda t: -t[0]):
            if n_c > best_n:
                consider(n_c, e_c)

    # C search: grow-and-repair insertion starting from the best valid graph.
    if time.monotonic() < hard - 2.0:
        budget = hard - time.monotonic() - 1.0
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)], stdin_graph=best,
                            timeout=max(5.0, time_limit - (time.monotonic() - t0) - 1.0))
            consider(*lib.parse_graph_text(out))
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
