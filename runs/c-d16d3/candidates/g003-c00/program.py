import itertools
import random
import time

import lib

START_CAP = 1200  # largest start graph the C engine accepts

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

/*
 * Vertex-insertion annealing for bipartite graphs with max degree d and diameter D.
 *
 * State: a bipartite graph (colour classes col[v] in {0,1}) with degrees <= d.
 * Cost: number of unordered vertex pairs at distance > D (computed exactly with
 * bitset ball expansion). Cost 0 means the graph is valid.
 *
 * Moves: degree-preserving 2-switches (keep bipartiteness), edge additions between
 * free vertices, rare edge removals. When the cost reaches 0 the current graph is
 * recorded and a new vertex is inserted, attached to free vertices of the opposite
 * colour (best of several random attachments), and annealing resumes. Stuck runs
 * restart from the best valid graph with a fresh random insertion.
 */

#define MAXN 1600
#define MAXW 25
#define MAXD 64
#define START_CAP 1200
#define RESTART 60000

typedef uint64_t row_t[MAXW];

static int d, D, n;
static int deg[MAXN];
static int col[MAXN];
static int adj[MAXN][MAXD];
static row_t bufA[MAXN], bufB[MAXN];

static int sn;
static int sdeg[MAXN];
static int sadj[MAXN][MAXD];

static int bn;
static int bdeg[MAXN];
static int bcol[MAXN];
static int badj[MAXN][MAXD];

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int irand(int k) { return (int)(rnd64() % (uint64_t)k); }

static double urand(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (adj[u][i] == v) return 1;
    return 0;
}

static void arc_del(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void edge_add(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void edge_del(int u, int v) {
    arc_del(u, v);
    arc_del(v, u);
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > D (unreachable pairs included). */
static long long bad_pairs(void) {
    int W = (n + 63) >> 6;
    row_t *cur = bufA, *nxt = bufB, *tmp;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = cur[adj[v][i]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static void snapshot(void) {
    sn = n;
    for (int v = 0; v < n; v++) {
        sdeg[v] = deg[v];
        memcpy(sadj[v], adj[v], sizeof(int) * (size_t)deg[v]);
    }
}

static void restore(void) {
    n = sn;
    for (int v = 0; v < n; v++) {
        deg[v] = sdeg[v];
        memcpy(adj[v], sadj[v], sizeof(int) * (size_t)deg[v]);
    }
}

static void save_best(void) {
    bn = n;
    for (int v = 0; v < n; v++) {
        bdeg[v] = deg[v];
        bcol[v] = col[v];
        memcpy(badj[v], adj[v], sizeof(int) * (size_t)deg[v]);
    }
}

static void load_best(void) {
    n = bn;
    for (int v = 0; v < n; v++) {
        deg[v] = bdeg[v];
        col[v] = bcol[v];
        memcpy(adj[v], badj[v], sizeof(int) * (size_t)deg[v]);
    }
}

/* Degree-preserving switch (a,b),(c,e) -> (a,e),(c,b) with col[a]==col[c]. */
static int move_2switch(void) {
    for (int tries = 0; tries < 20; tries++) {
        int a = irand(n);
        if (deg[a] == 0) continue;
        int b = adj[a][irand(deg[a])];
        int c = irand(n);
        if (c == a || col[c] != col[a] || deg[c] == 0) continue;
        int e = adj[c][irand(deg[c])];
        if (e == b) continue;
        if (has_edge(a, e) || has_edge(c, b)) continue;
        edge_del(a, b);
        edge_del(c, e);
        edge_add(a, e);
        edge_add(c, b);
        return 1;
    }
    return 0;
}

static int move_add(void) {
    for (int tries = 0; tries < 30; tries++) {
        int u = irand(n);
        if (deg[u] >= d) continue;
        int v = irand(n);
        if (v == u || col[v] == col[u] || deg[v] >= d) continue;
        if (has_edge(u, v)) continue;
        edge_add(u, v);
        return 1;
    }
    return 0;
}

static int move_remove(void) {
    for (int tries = 0; tries < 20; tries++) {
        int u = irand(n);
        if (deg[u] == 0) continue;
        int v = adj[u][irand(deg[u])];
        edge_del(u, v);
        return 1;
    }
    return 0;
}

static int collect_free(int c, int *cand) {
    int nc = 0;
    for (int v = 0; v < n; v++)
        if (col[v] != c && deg[v] < d) cand[nc++] = v;
    return nc;
}

/* Append one vertex and attach it to free opposite-colour vertices. */
static void insert_vertex(void) {
    static int cand[MAXN];
    static int bestpick[MAXD];
    int c = irand(2);
    int nc = collect_free(c, cand);
    if (nc == 0) {
        c = 1 - c;
        nc = collect_free(c, cand);
    }
    int nn = n;
    col[nn] = c;
    deg[nn] = 0;
    n = nn + 1;
    int k = nc < d ? nc : d;
    int trials = (nc <= d) ? 1 : 6;
    long long bestc = -1;
    for (int t = 0; t < trials; t++) {
        for (int i = 0; i < k; i++) {
            int j = i + irand(nc - i);
            int tmp = cand[i];
            cand[i] = cand[j];
            cand[j] = tmp;
        }
        for (int i = 0; i < k; i++) edge_add(nn, cand[i]);
        long long cc = bad_pairs();
        for (int i = 0; i < k; i++) edge_del(nn, cand[i]);
        if (bestc < 0 || cc < bestc) {
            bestc = cc;
            for (int i = 0; i < k; i++) bestpick[i] = cand[i];
        }
    }
    for (int i = 0; i < k; i++) edge_add(nn, bestpick[i]);
}

static int colour_graph(void) {
    static int q[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] == -1) {
                    col[v] = 1 - col[u];
                    q[t++] = v;
                } else if (col[v] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static int read_start(void) {
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) return 0;
    if (n0 <= 0 || n0 > START_CAP || m0 < 0) return 0;
    n = n0;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        edge_add(u, v);
    }
    if (!colour_graph()) {
        for (int v = 0; v < n; v++) deg[v] = 0;
        return 0;
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d < 1 || D < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL ^ 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    clock_t c0 = clock();
    if (!read_start()) {
        n = 2;
        deg[0] = deg[1] = 0;
        col[0] = 0;
        col[1] = 1;
        edge_add(0, 1);
    }

    bn = 0;
    long long cur = bad_pairs();
    if (cur == 0) save_best();

    long long it = 0, last_restart = 0;
    while (1) {
        if ((it & 31) == 0 && (double)(clock() - c0) / CLOCKS_PER_SEC > tl) break;
        it++;

        if (cur == 0) {
            if (n > bn) save_best();
            if (n + 2 >= MAXN) break;
            insert_vertex();
            cur = bad_pairs();
            last_restart = it;
            continue;
        }
        if (bn > 0 && it - last_restart > RESTART) {
            load_best();
            cur = 0;
            last_restart = it;
            continue;
        }

        double T = 0.25 + 1.5 * (1.0 - (double)(it % 30000) / 30000.0);
        snapshot();
        double r = urand();
        int ok;
        if (r < 0.80) ok = move_2switch();
        else if (r < 0.97) ok = move_add();
        else ok = move_remove();
        if (!ok) continue;

        long long nc = bad_pairs();
        long long delta = nc - cur;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) cur = nc;
        else restore();
    }

    if (bn == 0) {
        printf("0 0\n");
        return 0;
    }
    long long m = 0;
    for (int v = 0; v < bn; v++) m += bdeg[v];
    m /= 2;
    printf("%d %lld\n", bn, m);
    for (int u = 0; u < bn; u++)
        for (int i = 0; i < bdeg[u]; i++) {
            int v = badj[u][i];
            if (u < v) printf("%d %d\n", u, v);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1, so spare s = d - q - 1. Add an A-vertex per point in SA (joined
# to the lines through it) and a B-vertex per line in SB (joined to its points),
# where every line meets <= s points of SA and every point lies on <= s lines of SB.
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
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements so that every target is hit by <= s chosen elements."""
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
# Generalized quadrangle W(q) incidence graph (diameter 4).
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
# Build: best algebraic start, then C vertex-insertion annealing from it.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(cand):
        nonlocal best, best_n
        n_c, e_c = cand
        if n_c > best_n and lib.is_valid(n_c, e_c, d, D):
            best = (n_c, e_c)
            best_n = n_c

    if D >= 3:
        rng = random.Random(seed * 7919 + d)
        for cand in _arc_extensions(d, t0 + 0.2 * time_limit, rng):
            consider(cand)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # Insertion annealing in C, seeded with the best valid graph found so far.
    # Skip when already at the Moore bound or the start is too large for the engine.
    if (D >= 3 and best_n < lib.moore_bound(d, D) and best_n <= START_CAP):
        remaining = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        if remaining >= 2.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                                 stdin_graph=best, timeout=remaining + 15.0)
                consider(lib.parse_graph_text(text))
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
