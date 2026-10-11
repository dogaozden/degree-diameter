import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: certificate-based vertex insertion with spare-edge perturbation.
#
# State is always valid. A new vertex w on side s is joined to a set of
# opposite-side vertices with spare degree whose radius-(D-1) balls cover all
# vertices, so every x is within distance D of w. Adding a vertex never
# lengthens an old path. Perturbation adds a spare cross edge between opposite
# colour classes, which keeps the graph bipartite and only shortens paths.
# Balls are bitsets, and the greedy cover is randomized, with many restarts.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 1536
#define WMAX ((MAXN + 63) / 64)
#define MAXD 40

static int n, d, D;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int color[MAXN];
static uint64_t ball[MAXN][WMAX];
static uint64_t nxtb[MAXN][WMAX];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }

static int pc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void color_graph(void) {
    static int stack[MAXN];
    for (int v = 0; v < n; v++) color[v] = -1;
    for (int s = 0; s < n; s++) {
        if (color[s] != -1) continue;
        color[s] = 0;
        int sp = 0;
        stack[sp++] = s;
        while (sp) {
            int u = stack[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (color[v] == -1) { color[v] = 1 - color[u]; stack[sp++] = v; }
            }
        }
    }
}

static void compute_balls(void) {
    int words = (n + 63) / 64;
    int R = D - 1;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < words; w++) ball[v][w] = 0;
        ball[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < words; w++) nxtb[v][w] = ball[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < words; w++) nxtb[v][w] |= ball[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < words; w++) ball[v][w] = nxtb[v][w];
    }
}

/* Try to insert one new vertex on the given side. Returns 1 on success. */
static int try_insert(int side) {
    int words = (n + 63) / 64;
    uint64_t full[WMAX], cov[WMAX];
    static int taken[MAXN];
    static int cand[MAXN];
    int nc = 0;
    for (int w = 0; w < words; w++) full[w] = 0;
    for (int v = 0; v < n; v++) full[v >> 6] |= 1ULL << (v & 63);
    for (int u = 0; u < n; u++)
        if (color[u] == 1 - side && deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    for (int u = 0; u < n; u++) taken[u] = 0;
    for (int w = 0; w < words; w++) cov[w] = 0;
    int chosen[MAXD], nch = 0;
    for (;;) {
        int done = 1;
        for (int w = 0; w < words; w++)
            if ((cov[w] & full[w]) != full[w]) { done = 0; break; }
        if (done) break;
        if (nch >= d) return 0;
        int best = -1, bg = 0;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (taken[u]) continue;
            int g = 0;
            for (int w = 0; w < words; w++) g += pc(ball[u][w] & ~cov[w]);
            if (g > bg) { bg = g; best = u; }
        }
        if (best < 0) return 0;
        taken[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < words; w++) cov[w] |= ball[best][w];
    }
    if (n >= MAXN) return 0;
    int wid = n;
    n++;
    deg[wid] = 0;
    color[wid] = side;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], wid);
    return 1;
}

/* Add one random spare cross edge (opposite colours, not yet adjacent). */
static void perturb(void) {
    static int A[MAXN], B[MAXN];
    int na = 0, nb = 0;
    for (int u = 0; u < n; u++) {
        if (deg[u] < d) {
            if (color[u] == 0) A[na++] = u; else B[nb++] = u;
        }
    }
    if (!na || !nb) return;
    for (int t = 0; t < 60; t++) {
        int u = A[rndi(na)], v = B[rndi(nb)];
        if (!has_edge(u, v)) { add_edge(u, v); return; }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (!rs) rs = 1;

    int nin = 0, min_ = 0;
    if (scanf("%d %d", &nin, &min_) != 2 || nin < 1 || nin > MAXN || d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    n = nin;
    for (int i = 0; i < min_; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || deg[u] >= d || deg[v] >= d) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }
    color_graph();

    clock_t t0 = clock();
    int fails = 0;
    const int MAXFAILS = 400;
    while (fails < MAXFAILS && (double)(clock() - t0) / CLOCKS_PER_SEC < tl) {
        compute_balls();
        int first = rndi(2);
        int ok = 0;
        for (int k = 0; k < 2 && !ok; k++) {
            int side = (k == 0) ? first : 1 - first;
            for (int at = 0; at < 3 && !ok; at++) ok = try_insert(side);
        }
        if (ok) { fails = 0; continue; }
        fails++;
        perturb();
    }

    int m = 0;
    for (int v = 0; v < n; v++) m += deg[v];
    m /= 2;
    printf("%d %d\n", n, m);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) printf("%d %d\n", u, adj[u][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q). Every old vertex has degree q+1, so with d >= q+1 it has
# spare capacity s = d - q - 1. Choose a point set S with every line holding at
# most s points of S. For each P in S add an A-vertex joined to the q+1 lines
# through P; for each j in S add a B-vertex joined to the q+1 points on j.
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
    """Conic (plus nucleus for even q): an arc with no three collinear."""
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


# ----------------------------------------------------------------------------
# Glue: run the C insertion engine on a valid start graph.
# ----------------------------------------------------------------------------

def _c_augment(n, edges, d, D, seed, budget, timeout):
    """Run the C engine; return a validated (n, edges) or None on any failure."""
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                         stdin_graph=(n, edges), timeout=timeout)
        n2, e2 = lib.parse_graph_text(text)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard_end = start + 0.95 * time_limit

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

    if D < 3:
        return best

    # Arc-extended projective plane graphs (diameter 3).
    arcs = _arc_extensions(d, start + 0.15 * time_limit, random.Random(seed * 7919 + d))
    arcs.sort(key=lambda t: -t[0])
    for n_c, e_c in arcs[:3]:
        consider(n_c, e_c)

    # C insertion with ball certificates and spare-edge perturbation.
    if arcs:
        n_a, e_a = arcs[0]
        now = time.monotonic()
        budget = max(0.5, (hard_end - now) * 0.9)
        timeout = max(1.0, hard_end - now + 0.5 * time_limit * 0.0 + 1.0)
        res = _c_augment(n_a, e_a, d, D, seed + 1, budget, timeout)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
