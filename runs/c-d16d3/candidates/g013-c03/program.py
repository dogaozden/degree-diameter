"""Arc-extended projective plane seeds, Python greedy vertex insertion, and a C
grow-and-repair search. The C engine keeps a bipartite graph with bitset
R-ball coverage. When the graph is valid it adds a vertex whose neighbourhood
covers all old vertices within D-1, then runs simulated annealing with
degree-preserving 2-switches, targeted pair-fixing rewires and capacity-adding
edges to repair the uncovered pairs. It restarts from the best valid snapshot
after a stall.
"""
import itertools
import random
import time

import lib


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
# Python greedy vertex insertion with ball-cover certificates (used as a seed).
# ----------------------------------------------------------------------------

def _side_colors(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _ball_masks(n, adj, R):
    """Bitmask of all vertices within distance R of each vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return reach


def _augment(n, edges, d, D, rng, deadline, max_fails=60):
    """Greedily insert vertices whose neighbourhoods cover the graph within D. Returns (n, edges)."""
    if n == 0 or D < 2:
        return n, list(edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _side_colors(n, adj)
    R = D - 1
    fails = 0
    while time.monotonic() < deadline and fails < max_fails:
        balls = _ball_masks(n, adj, R)
        full = (1 << n) - 1
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for side in sides:
            base_cand = [u for u in range(n) if color[u] == 1 - side and len(adj[u]) < d]
            if not base_cand:
                continue
            for _attempt in range(4):
                cand = base_cand[:]
                rng.shuffle(cand)
                covered = 0
                chosen = []
                pool = cand
                while covered != full and len(chosen) < d and pool:
                    best_gain, bu, bi = 0, None, -1
                    for i, u in enumerate(pool):
                        g = (balls[u] & ~covered).bit_count()
                        if g > best_gain:
                            best_gain, bu, bi = g, u, i
                    if bu is None:
                        break
                    chosen.append(bu)
                    covered |= balls[bu]
                    pool = pool[:bi] + pool[bi + 1:]
                if covered == full:
                    w = n
                    n += 1
                    adj.append(set())
                    color.append(side)
                    for u in chosen:
                        adj[u].add(w)
                        adj[w].add(u)
                    added = True
                    break
            if added:
                break
        if added:
            fails = 0
            continue
        fails += 1
        spare_a = [u for u in range(n) if len(adj[u]) < d and color[u] == 0]
        spare_b = [u for u in range(n) if len(adj[u]) < d and color[u] == 1]
        if spare_a and spare_b:
            for _ in range(20):
                u = rng.choice(spare_a)
                v = rng.choice(spare_b)
                if u != v and v not in adj[u]:
                    adj[u].add(v)
                    adj[v].add(u)
                    break
    out = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, out


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
# C engine: bitset grow-and-repair annealing.
#
# State: bipartite graph (every edge joins the two sides), max degree DEG.
# cost = number of unordered vertex pairs at distance > D (bitset R-balls).
# When cost == 0 the graph is valid: remember it and insert a new vertex whose
# greedy neighbourhood covers every old vertex within D-1 (ball-cover rule).
# Otherwise repair with simulated annealing using:
#   - 2-switches (degree preserving),
#   - pair-fixing rewires aimed at a currently uncovered pair (x, u),
#   - capacity-adding cross edges (never increase cost),
#   - rare edge removals for diversification.
# After STALL non-improving steps the search restores the best valid snapshot.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXD 64
#define MAXW (MAXN / 64)
#define STALL 40000

typedef struct {
    int n;
    int side[MAXN];
    int deg[MAXN];
    int adj[MAXN][MAXD];
} Graph;

static Graph G;
static Graph BEST;
static int best_n = 0;
static int D = 2;
static int DEG = 3;
static int bvalid = 0;
static uint64_t rs = 88172645463325252ULL;
static uint64_t bufB[MAXN * MAXW];
static uint64_t ballR[MAXN * MAXW];
static uint64_t ballG[MAXN * MAXW];
static clock_t t_start;
static time_t w_start;
static double budget = 1.0;
static int nops = 0;
static int opt[8], opa[8], opb[8];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int m) { return (int)(rnd64() % (uint64_t)m); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int time_up(void) {
    double el = (double)(clock() - t_start) / CLOCKS_PER_SEC;
    if (el >= budget) return 1;
    if (difftime(time(NULL), w_start) >= budget + 1.0) return 1;
    return 0;
}

static int is_adj(int a, int b) {
    for (int k = 0; k < G.deg[a]; k++)
        if (G.adj[a][k] == b) return 1;
    return 0;
}

static void add_e(int a, int b) {
    G.adj[a][G.deg[a]++] = b;
    G.adj[b][G.deg[b]++] = a;
}

static void del_one(int a, int b) {
    for (int k = 0; k < G.deg[a]; k++) {
        if (G.adj[a][k] == b) {
            G.adj[a][k] = G.adj[a][G.deg[a] - 1];
            G.deg[a]--;
            return;
        }
    }
}

static void del_e(int a, int b) {
    del_one(a, b);
    del_one(b, a);
}

static void do_add(int a, int b) {
    add_e(a, b);
    opt[nops] = 1; opa[nops] = a; opb[nops] = b;
    nops++;
}

static void do_del(int a, int b) {
    del_e(a, b);
    opt[nops] = 0; opa[nops] = a; opb[nops] = b;
    nops++;
}

static void undo_all(void) {
    while (nops > 0) {
        nops--;
        if (opt[nops]) del_e(opa[nops], opb[nops]);
        else add_e(opa[nops], opb[nops]);
    }
}

/* out[v] = bitmask of vertices within distance R of v. */
static void compute_balls(int R, uint64_t *out) {
    int n = G.n, W = (n + 63) / 64;
    uint64_t *cur = out, *nxt = bufB;
    memset(out, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int k = 0; k < G.deg[v]; k++) {
                const uint64_t *s2 = cur + (size_t)G.adj[v][k] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    if (cur != out) memcpy(out, cur, sizeof(uint64_t) * (size_t)n * W);
}

/* Cost = number of unordered pairs at distance > D. Leaves ballR valid. */
static long long eval_cost(void) {
    int n = G.n, W = (n + 63) / 64;
    compute_balls(D, ballR);
    bvalid = 1;
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int pop = 0;
        for (int w = 0; w < W; w++) pop += pc64(ballR[(size_t)v * W + w]);
        tot += n - pop;
    }
    return tot / 2;
}

static int reached(int x, int u) {
    int W = (G.n + 63) / 64;
    return (int)((ballR[(size_t)x * W + (u >> 6)] >> (u & 63)) & 1ULL);
}

/* Degree-preserving 2-switch: (a,b),(c,e) -> (a,e),(c,b), a and c on one side. */
static int move_switch(void) {
    int n = G.n;
    int a = rndint(n);
    if (G.deg[a] == 0) return 0;
    int b = G.adj[a][rndint(G.deg[a])];
    int c = rndint(n);
    if (c == a || G.side[c] != G.side[a] || G.deg[c] == 0) return 0;
    int e = G.adj[c][rndint(G.deg[c])];
    if (e == b) return 0;
    if (is_adj(a, e) || is_adj(c, b)) return 0;
    do_del(a, b);
    do_del(c, e);
    do_add(a, e);
    do_add(c, b);
    return 1;
}

/* Pair-fixing rewire: pick an uncovered pair (x,u), move one edge of x to z
   so that z lies within the right distance of u. */
static int move_fix(void) {
    int n = G.n;
    int x = -1, u = -1;
    for (int t = 0; t < 60 && u < 0; t++) {
        int cx = rndint(n);
        if (G.deg[cx] == 0) continue;
        for (int s = 0; s < 40; s++) {
            int cu = rndint(n);
            if (cu != cx && !reached(cx, cu)) {
                x = cx;
                u = cu;
                break;
            }
        }
    }
    if (u < 0) return 0;
    if (G.deg[u] == 0) return 0;
    int y = G.adj[x][rndint(G.deg[x])];
    int z;
    if (G.side[x] == G.side[u]) {
        z = G.adj[u][rndint(G.deg[u])];
    } else {
        int a = G.adj[u][rndint(G.deg[u])];
        if (G.deg[a] == 0) return 0;
        z = G.adj[a][rndint(G.deg[a])];
    }
    if (z == y || z == x || G.deg[z] >= DEG) return 0;
    if (G.side[z] == G.side[x]) return 0;
    if (is_adj(x, z)) return 0;
    do_del(x, y);
    do_add(x, z);
    return 1;
}

/* Add a cross edge between two spare-capacity vertices (never raises cost). */
static int move_add(void) {
    int n = G.n;
    int a = rndint(n);
    if (G.deg[a] >= DEG) return 0;
    for (int t = 0; t < 30; t++) {
        int c = rndint(n);
        if (G.side[c] != G.side[a] && G.deg[c] < DEG && !is_adj(a, c)) {
            do_add(a, c);
            return 1;
        }
    }
    return 0;
}

/* Diversification: delete a random edge. */
static int move_remove(void) {
    int a = rndint(G.n);
    if (G.deg[a] == 0) return 0;
    int b = G.adj[a][rndint(G.deg[a])];
    do_del(a, b);
    return 1;
}

/* Insert a vertex on one side joined to a greedy cover of the other side's
   (D-1)-balls. Returns 1 if a vertex was added. */
static int grow(void) {
    int n = G.n;
    if (n >= MAXN - 1) return 0;
    int W = (n + 63) / 64;
    compute_balls(D - 1, ballG);
    int bestside = -1, bestk = 0;
    long long bestunc = 0;
    int bestch[MAXD];
    int order[2] = {0, 1};
    if (rndint(2)) {
        order[0] = 1;
        order[1] = 0;
    }
    for (int oi = 0; oi < 2; oi++) {
        int s = order[oi];
        uint64_t covered[MAXW];
        memset(covered, 0, sizeof(covered));
        int chosen[MAXD];
        int k = 0;
        for (int step = 0; step < DEG; step++) {
            int bu = -1, bg = 0, ties = 0;
            for (int u = 0; u < n; u++) {
                if (G.side[u] == s || G.deg[u] >= DEG) continue;
                int g = 0;
                const uint64_t *bl = ballG + (size_t)u * W;
                for (int w = 0; w < W; w++) g += pc64(bl[w] & ~covered[w]);
                if (g > bg) {
                    bg = g;
                    bu = u;
                    ties = 1;
                } else if (g == bg && g > 0) {
                    ties++;
                    if (rndint(ties) == 0) bu = u;
                }
            }
            if (bu < 0) break;
            chosen[k++] = bu;
            for (int w = 0; w < W; w++) covered[w] |= ballG[(size_t)bu * W + w];
        }
        if (k == 0) continue;
        int cov = 0;
        for (int w = 0; w < W; w++) cov += pc64(covered[w]);
        long long unc = (long long)n - cov;
        if (bestside < 0 || unc < bestunc) {
            bestside = s;
            bestunc = unc;
            bestk = k;
            for (int j = 0; j < k; j++) bestch[j] = chosen[j];
        }
    }
    if (bestside < 0) return 0;
    int w = n;
    G.n = n + 1;
    G.side[w] = bestside;
    G.deg[w] = 0;
    for (int j = 0; j < bestk; j++) add_e(w, bestch[j]);
    return 1;
}

static void save_best(void) {
    BEST = G;
    best_n = G.n;
}

static void restore_best(void) {
    G = BEST;
}

static void output_best(void) {
    if (best_n <= 0) {
        printf("0 0\n");
        return;
    }
    int m = 0;
    for (int v = 0; v < BEST.n; v++)
        for (int k = 0; k < BEST.deg[v]; k++)
            if (BEST.adj[v][k] > v) m++;
    printf("%d %d\n", BEST.n, m);
    for (int v = 0; v < BEST.n; v++)
        for (int k = 0; k < BEST.deg[v]; k++)
            if (BEST.adj[v][k] > v) printf("%d %d\n", v, BEST.adj[v][k]);
}

static void load_input(void) {
    int n0 = 0, m0 = 0;
    int ok = 1;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    if (n0 < 1 || n0 > MAXN || m0 < 0) ok = 0;
    memset(&G, 0, sizeof(G));
    if (ok) {
        G.n = n0;
        for (int i = 0; i < m0 && ok; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) {
                ok = 0;
                break;
            }
            if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) {
                ok = 0;
                break;
            }
            if (is_adj(u, v)) continue;
            if (G.deg[u] >= DEG || G.deg[v] >= DEG) {
                ok = 0;
                break;
            }
            add_e(u, v);
        }
    }
    if (ok) {
        static int col[MAXN], q[MAXN];
        for (int i = 0; i < n0; i++) col[i] = -1;
        for (int s = 0; s < n0 && ok; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int qh = 0, qt = 0;
            q[qt++] = s;
            while (qh < qt && ok) {
                int u = q[qh++];
                for (int k = 0; k < G.deg[u]; k++) {
                    int v = G.adj[u][k];
                    if (col[v] < 0) {
                        col[v] = 1 - col[u];
                        q[qt++] = v;
                    } else if (col[v] == col[u]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
        if (ok)
            for (int i = 0; i < n0; i++) G.side[i] = col[i];
    }
    if (!ok) {
        memset(&G, 0, sizeof(G));
        G.n = 2;
        G.side[0] = 0;
        G.side[1] = 1;
        add_e(0, 1);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    int d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    budget = atof(argv[4]);
    DEG = d;
    if (DEG > MAXD) DEG = MAXD;
    if (DEG < 1 || D < 2) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    t_start = clock();
    w_start = time(NULL);

    load_input();

    long long cost = eval_cost();
    long long phase_best = cost;
    int stall = 0;
    double T = 0.3 + 0.7 * rnd01();
    if (cost == 0 && G.n > best_n) save_best();

    while (!time_up()) {
        if (!bvalid) {
            compute_balls(D, ballR);
            bvalid = 1;
        }
        if (cost == 0) {
            if (G.n > best_n) save_best();
            if (G.n >= MAXN - 1) break;
            if (!grow()) {
                /* No room to grow: free some capacity by removing an edge. */
                int a = rndint(G.n);
                if (G.deg[a] > 0) {
                    int b = G.adj[a][rndint(G.deg[a])];
                    nops = 0;
                    do_del(a, b);
                }
                nops = 0;
            }
            cost = eval_cost();
            phase_best = cost;
            stall = 0;
            T = 0.3 + 0.7 * rnd01();
            continue;
        }

        int ok;
        double r = rnd01();
        if (r < 0.35) ok = move_switch();
        else if (r < 0.90) ok = move_fix();
        else if (r < 0.99) ok = move_add();
        else ok = move_remove();
        if (!ok) {
            nops = 0;
            continue;
        }
        long long nc = eval_cost();
        long long delta = nc - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cost = nc;
            nops = 0;
            if (cost == 0 && G.n > best_n) save_best();
        } else {
            undo_all();
            bvalid = 0;
        }

        if (cost < phase_best) {
            phase_best = cost;
            stall = 0;
        } else if (++stall > STALL) {
            if (best_n > 0) restore_best();
            cost = eval_cost();
            phase_best = cost;
            stall = 0;
            T = 0.3 + 0.7 * rnd01();
        }
    }

    if (cost == 0 && G.n > best_n) save_best();
    output_best();
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

    # Arc-extended projective plane seeds (diameter 3), then Python insertion.
    if D >= 3:
        arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)
        if arcs:
            n_a, e_a = arcs[0]
            n2, e2 = _augment(n_a, e_a, d, D, rng, start + 0.25 * time_limit)
            consider(n2, e2)

    if D >= 4 and time.monotonic() < start + 0.25 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # C grow-and-repair search from the best valid graph found so far.
    elapsed = time.monotonic() - start
    c_budget = 0.82 * time_limit - elapsed - 1.0
    if D >= 3 and c_budget >= 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}"],
                             stdin_graph=best, timeout=c_budget + 3.0)
            n_c, e_c = lib.parse_graph_text(text)
            consider(n_c, e_c)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
