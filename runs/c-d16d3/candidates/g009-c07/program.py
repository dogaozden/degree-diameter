import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing on bipartite graphs with max degree d.
# Cost = number of vertex pairs at distance > D (bitset BFS). Moves keep
# degrees and bipartiteness: degree-preserving 2-switches, endpoint shifts
# onto spare vertices, and spare cross edges. New vertices are added whenever
# the current graph is valid, so the program grows the graph while it can.
# ----------------------------------------------------------------------------
C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXD 64
#define MAXW ((MAXN + 63) / 64)
#define MAXE (MAXN * MAXD)

static int N = 0, DEG = 3, DIST = 3;
static int deg[MAXN];
static int nb[MAXN][MAXD];
static unsigned char A[MAXN][MAXN];
static int side[MAXN];
static uint64_t RA[MAXN][MAXW], RB[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static int snapN = 0, snapM = 0;
static int snapU[MAXE], snapV[MAXE];

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
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int bad_pairs(void) {
    int W = (N + 63) >> 6;
    uint64_t (*cur)[MAXW] = RA;
    uint64_t (*nxt)[MAXW] = RB;
    for (int v = 0; v < N; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * (size_t)W);
        cur[v][v >> 6] |= 1ULL << (v & 63);
        for (int i = 0; i < deg[v]; i++) {
            int u = nb[v][i];
            cur[v][u >> 6] |= 1ULL << (u & 63);
        }
    }
    for (int k = 2; k <= DIST; k++) {
        for (int v = 0; v < N; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                int u = nb[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long miss = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(cur[v][w]);
        miss += N - c;
    }
    return (int)(miss / 2);
}

static int find_nb(int v, int u) {
    for (int i = 0; i < deg[v]; i++)
        if (nb[v][i] == u) return i;
    return -1;
}
static void add_e(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
    A[u][v] = 1;
    A[v][u] = 1;
}
static void del_e(int u, int v) {
    int i = find_nb(u, v);
    nb[u][i] = nb[u][--deg[u]];
    int j = find_nb(v, u);
    nb[v][j] = nb[v][--deg[v]];
    A[u][v] = 0;
    A[v][u] = 0;
}

static int color_graph(void) {
    static int stk[MAXN];
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    stk[sp++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static int mt, ma, mb, mc, me;

static int propose(void) {
    int r = rndint(100);
    if (r < 70) {
        int a = rndint(N), c = rndint(N);
        if (a == c || side[a] != 0 || side[c] != 0 || deg[a] == 0 || deg[c] == 0) return 0;
        int b = nb[a][rndint(deg[a])];
        int e = nb[c][rndint(deg[c])];
        if (b == e || A[a][e] || A[c][b]) return 0;
        del_e(a, b);
        del_e(c, e);
        add_e(a, e);
        add_e(c, b);
        mt = 0; ma = a; mb = b; mc = c; me = e;
        return 1;
    }
    if (r < 95) {
        int a = rndint(N), e = rndint(N);
        if (side[a] != 0 || deg[a] == 0 || side[e] != 1 || deg[e] >= DEG) return 0;
        int b = nb[a][rndint(deg[a])];
        if (e == b || A[a][e]) return 0;
        del_e(a, b);
        add_e(a, e);
        mt = 1; ma = a; mb = b; me = e;
        return 1;
    }
    {
        int a = rndint(N), e = rndint(N);
        if (side[a] != 0 || side[e] != 1 || deg[a] >= DEG || deg[e] >= DEG || A[a][e]) return 0;
        add_e(a, e);
        mt = 2; ma = a; me = e;
        return 1;
    }
}

static void undo(void) {
    if (mt == 0) {
        del_e(ma, me);
        del_e(mc, mb);
        add_e(ma, mb);
        add_e(mc, me);
    } else if (mt == 1) {
        del_e(ma, me);
        add_e(ma, mb);
    } else {
        del_e(ma, me);
    }
}

/* Add one vertex on side s joined to up to DEG random spare vertices of the other side.
   Leaves the graph unchanged and returns 0 if there is no spare vertex. */
static int grow(int s) {
    static int cand[MAXN];
    if (N >= MAXN - 2) return 0;
    int nc = 0;
    for (int x = 0; x < N; x++)
        if (side[x] != s && deg[x] < DEG) cand[nc++] = x;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    int k = nc < DEG ? nc : DEG;
    int w = N;
    N++;
    side[w] = s;
    deg[w] = 0;
    for (int i = 0; i < k; i++) add_e(w, cand[i]);
    return 1;
}

static void snapshot(void) {
    snapN = N;
    snapM = 0;
    for (int v = 0; v < N; v++)
        for (int i = 0; i < deg[v]; i++) {
            int u = nb[v][i];
            if (u > v && snapM < MAXE) {
                snapU[snapM] = v;
                snapV[snapM] = u;
                snapM++;
            }
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (d < 1 || d > MAXD - 1 || D < 2) {
        printf("0 0\n");
        return 0;
    }
    DEG = d;
    DIST = D;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || n0 > MAXN - 200 || m0 < 0 || m0 > MAXE) {
        printf("0 0\n");
        return 0;
    }
    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v || A[u][v] || deg[u] >= DEG || deg[v] >= DEG) {
            printf("0 0\n");
            return 0;
        }
        add_e(u, v);
    }
    if (!color_graph()) {
        printf("0 0\n");
        return 0;
    }

    snapshot();
    int cost = bad_pairs();
    clock_t t_end = clock() + (clock_t)(budget * (double)CLOCKS_PER_SEC);
    const double T0 = 4.0, TEND = 0.3;
    const int CYCLE = 3000;
    int cyc = 0, next_side = 0;
    long long loops = 0;

    while (1) {
        if ((loops & 127) == 0 && clock() >= t_end) break;
        loops++;
        if (cost == 0) {
            snapshot();
            if (!grow(next_side)) break;
            next_side ^= 1;
            cost = bad_pairs();
            cyc = 0;
            continue;
        }
        if (cyc >= CYCLE) cyc = 0;
        double T = T0 * pow(TEND / T0, (double)cyc / CYCLE);
        cyc++;
        if (!propose()) continue;
        int nc = bad_pairs();
        int delta = nc - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cost = nc;
        } else {
            undo();
        }
    }
    if (cost == 0) snapshot();

    printf("%d %d\n", snapN, snapM);
    for (int i = 0; i < snapM; i++) printf("%d %d\n", snapU[i], snapV[i]);
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
    """Conic (plus nucleus for even q) as a point-index set."""
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
# Greedy vertex insertion with ball-cover certificates (D >= 3 base).
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
# Build: arc-extended base, then C annealing that grows the best valid graph.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    bound = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3 and best_n < bound:
        arcs = _arc_extensions(d, t0 + 0.08 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)
        if best_n < bound and time.monotonic() < t0 + 0.20 * time_limit:
            n2, e2 = _augment(best[0], best[1], d, D, rng, t0 + 0.20 * time_limit)
            consider(n2, e2)

    if D >= 4 and best_n < bound and time.monotonic() < t0 + 0.20 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # C annealing: grow the best valid graph, leaving margin for compile and output.
    if best_n < bound and D >= 2:
        budget = 0.80 * time_limit - (time.monotonic() - t0) - 2.0
        if budget >= 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=best, timeout=budget + 6.0)
                n_c, e_c = lib.parse_graph_text(out)
                consider(n_c, e_c)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
