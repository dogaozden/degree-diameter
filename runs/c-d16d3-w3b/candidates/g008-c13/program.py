import random
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1: arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S
# such that every line holds <= s points of S and every point lies on <= s
# lines indexed by S. For each P in S add a new A-vertex joined to the q+1
# lines through P, and for each j in S add a new B-vertex joined to the q+1
# points on line j. Diameter stays 3.
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
        out.append(_arc_graph(m, edges, point_lines, S, line_points))
    return out


# ----------------------------------------------------------------------------
# Stage 2 (new, bold): C local search that grows the start graph by one vertex
# at a time. Each growth attempt inserts a vertex, then runs simulated
# annealing on the number of vertex pairs at distance > D. Moves are
# degree-preserving 2-switches (which keep the graph bipartite) and cross-edge
# additions between spare-degree vertices. On success the state is saved and
# growth continues. On failure the saved state is restored, perturbed, and retried.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXDEG 64
#define WORDS 16

typedef struct {
    int n;
    int side[MAXN];
    int deg[MAXN];
    int adj[MAXN][MAXDEG];
} Snap;

static int N, D, DEG;
static int side[MAXN];
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static uint64_t rs = 88172645463325252ULL;
static clock_t t_end;
static int sw_a, sw_b, sw_c, sw_e;
static Snap snap;
static uint64_t bufA[MAXN][WORDS], bufB[MAXN][WORDS];

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double runif(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int time_up(void) { return clock() >= t_end; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) return 1;
    return 0;
}
static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}
static void del_arc(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a][i] == b) { adj[a][i] = adj[a][--deg[a]]; return; }
    }
}
static void del_edge(int a, int b) { del_arc(a, b); del_arc(b, a); }

/* Number of ordered pairs at distance > D, divided by 2 (unordered bad pairs). */
static long long bad_count(void) {
    int W = (N + 63) / 64;
    uint64_t (*cur)[WORDS] = bufA;
    uint64_t (*nxt)[WORDS] = bufB;
    for (int v = 0; v < N; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * WORDS);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < N; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * W);
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*tmp)[WORDS] = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long total = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        total += N - c;
    }
    return total / 2;
}

/* Degree-preserving 2-switch: (a,b),(c,e) -> (a,e),(c,b) with a,c on the same side. */
static int try_switch(void) {
    for (int tries = 0; tries < 50; tries++) {
        int a = rint_(N);
        if (deg[a] == 0) continue;
        int b = adj[a][rint_(deg[a])];
        int c = rint_(N);
        if (c == a || deg[c] == 0 || side[c] != side[a]) continue;
        int e = adj[c][rint_(deg[c])];
        if (e == b) continue;
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        sw_a = a; sw_b = b; sw_c = c; sw_e = e;
        return 1;
    }
    return 0;
}

static void undo_switch(void) {
    del_edge(sw_a, sw_e);
    del_edge(sw_c, sw_b);
    add_edge(sw_a, sw_b);
    add_edge(sw_c, sw_e);
}

/* Add an edge between spare-degree vertices on opposite sides. Never increases bad pairs. */
static int try_cross(void) {
    for (int tries = 0; tries < 100; tries++) {
        int u = rint_(N);
        if (deg[u] >= DEG) continue;
        int v = rint_(N);
        if (side[v] == side[u] || deg[v] >= DEG) continue;
        if (has_edge(u, v)) continue;
        add_edge(u, v);
        return 1;
    }
    return 0;
}

/* Append a vertex on a random side and join it to DEG opposite-side vertices,
   stealing an edge from a saturated neighbour when necessary. */
static int insert_vertex(void) {
    if (N >= MAXN - 1) return 0;
    int x = N++;
    side[x] = rint_(2);
    deg[x] = 0;
    int tries = 0;
    while (deg[x] < DEG && tries < 20000) {
        tries++;
        int w = rint_(N - 1);
        if (side[w] == side[x] || has_edge(x, w)) continue;
        if (deg[w] < DEG) { add_edge(x, w); continue; }
        if (deg[w] == 0) continue;
        int z = adj[w][rint_(deg[w])];
        del_edge(w, z);
        add_edge(x, w);
    }
    return 1;
}

static long long anneal(long long cur, long long iters, double T0) {
    for (long long it = 0; it < iters && cur > 0; it++) {
        if ((it & 15) == 0 && time_up()) break;
        if (runif() < 0.25) {
            if (try_cross()) cur = bad_count();
            continue;
        }
        if (!try_switch()) continue;
        long long c2 = bad_count();
        long long delta = c2 - cur;
        double T = T0 * (1.0 - (double)it / (double)iters) + 0.02;
        if (delta <= 0 || runif() < exp(-(double)delta / T)) cur = c2;
        else undo_switch();
    }
    return cur;
}

static void take(Snap *s) {
    s->n = N;
    memcpy(s->side, side, sizeof side);
    memcpy(s->deg, deg, sizeof deg);
    memcpy(s->adj, adj, sizeof adj);
}

static void restore(const Snap *s) {
    N = s->n;
    memcpy(side, s->side, sizeof side);
    memcpy(deg, s->deg, sizeof deg);
    memcpy(adj, s->adj, sizeof adj);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    t_end = clock() + (clock_t)(tl * CLOCKS_PER_SEC);

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || d < 1 || d > MAXDEG - 1 || D < 1 ||
        n < 1 || n > MAXN - 64 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    DEG = d;
    N = n;
    memset(deg, 0, sizeof deg);
    int bad = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { bad = 1; break; }
        if (u < 0 || u >= n || v < 0 || v >= n || u == v ||
            deg[u] >= DEG || deg[v] >= DEG || has_edge(u, v)) {
            bad = 1;
            break;
        }
        add_edge(u, v);
    }
    if (!bad) {
        /* 2-colour the start graph; conflict means it is not bipartite. */
        for (int i = 0; i < N; i++) side[i] = -1;
        static int stack[MAXN];
        for (int s = 0; s < N && !bad; s++) {
            if (side[s] >= 0) continue;
            side[s] = 0;
            int sp = 0;
            stack[sp++] = s;
            while (sp > 0 && !bad) {
                int x = stack[--sp];
                for (int i = 0; i < deg[x]; i++) {
                    int y = adj[x][i];
                    if (side[y] < 0) { side[y] = 1 - side[x]; stack[sp++] = y; }
                    else if (side[y] == side[x]) { bad = 1; break; }
                }
            }
        }
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    long long cur = bad_count();
    if (cur != 0) cur = anneal(cur, 300000, 1.0);
    if (cur != 0) {
        printf("0 0\n");
        return 0;
    }
    take(&snap);

    while (!time_up()) {
        restore(&snap);
        int k = rint_(4) == 0 ? 0 : 1 + rint_(12);
        for (int i = 0; i < k; i++) try_switch();
        if (!insert_vertex()) break;
        cur = bad_count();
        double T0 = 0.2 + 1.0 * runif();
        cur = anneal(cur, 6000, T0);
        if (cur == 0) take(&snap);
    }

    restore(&snap);
    int M = 0;
    for (int v = 0; v < N; v++)
        for (int i = 0; i < deg[v]; i++)
            if (adj[v][i] > v) M++;
    printf("%d %d\n", N, M);
    for (int v = 0; v < N; v++)
        for (int i = 0; i < deg[v]; i++)
            if (adj[v][i] > v) printf("%d %d\n", v, adj[v][i]);
    return 0;
}
"""


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite with max degree d.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    # Stage 1: arc-extended projective plane graphs (diameter 3, valid for D >= 3).
    if D >= 3:
        for n_c, e_c in _arc_extensions(d, t0 + 0.15 * time_limit,
                                        random.Random(seed * 7919 + d)):
            if n_c > best_n and lib.is_valid(n_c, e_c, d, D):
                best, best_n = (n_c, e_c), n_c

    # Stage 2: C growth search from the best valid graph, unless already at the Moore bound.
    if best_n < lib.moore_bound(d, D) and d <= 60:
        elapsed = time.monotonic() - t0
        budget = 0.75 * time_limit - elapsed
        if budget > 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=best, timeout=0.9 * time_limit - elapsed)
                n_s, e_s = lib.parse_graph_text(out)
                if n_s > best_n and lib.is_valid(n_s, e_s, d, D):
                    best, best_n = (n_s, e_s), n_s
            except Exception:
                pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
