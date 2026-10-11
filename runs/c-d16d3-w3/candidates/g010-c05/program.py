import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3). Unchanged helpers.
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
    """True if every target t is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice of elements with per-target load <= s."""
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


def _local_side(m, s, nbr, S0, rng, deadline, iters=6000):
    """Plateau local search (insert or swap) on a feasible set."""
    if s < 1:
        return list(S0)
    inS = [False] * m
    load = [0] * m
    S = list(S0)
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            load[t] += 1
    best = list(S)
    for it in range(iters):
        if it % 256 == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        over = {t for t in nbr[x] if load[t] >= s}
        if not over:
            S.append(x)
            inS[x] = True
            for t in nbr[x]:
                load[t] += 1
            if len(S) > len(best):
                best = list(S)
            continue
        cand = [y for y in S if any(t in over for t in nbr[y])]
        if not cand:
            continue
        y = rng.choice(cand)
        for t in nbr[y]:
            load[t] -= 1
        if all(load[t] < s for t in nbr[x]):
            S.remove(y)
            inS[y] = False
            S.append(x)
            inS[x] = True
            for t in nbr[x]:
                load[t] += 1
        else:
            for t in nbr[y]:
                load[t] += 1
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
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
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
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

        SA = _local_side(m, s, point_lines, SA, rng, deadline)
        SB = _local_side(m, s, line_points, SB, rng, deadline)

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4). Unchanged.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q); diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW (bold): C engine that grows ANY valid start graph by vertex insertion.
#
# Each round inserts one vertex on a random side, saturates spare degree with
# edges (adding edges never hurts distances), then runs simulated annealing
# over degree-preserving double edge swaps and spare-transfer moves to drive
# the number of pairs at distance > D to zero. On failure the state is
# restored and a plateau walk (only moves that keep the graph valid) mixes it.
# The output is always a valid graph (the input if nothing better is found).
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXD 64
#define MAXW (MAXN / 64)
#define ITER 1500
#define MIX 300

typedef struct {
    int n;
    int side[MAXN];
    int deg[MAXN];
    int adj[MAXN][MAXD];
} Graph;

static Graph G, good;
static int d, D;
static double tlimit;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static uint64_t bits[2][MAXN][MAXW];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static int timeup(void) {
    return (double)clock() / CLOCKS_PER_SEC > tlimit;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of ordered pairs (v,w) with dist(v,w) > D. Zero iff valid (connected, diameter <= D). */
static long long cost_of(const Graph *g) {
    int n = g->n;
    int W = (n + 63) / 64;
    int c = 0;
    for (int v = 0; v < n; v++) {
        uint64_t *b = bits[0][v];
        for (int w = 0; w < W; w++) b[w] = 0;
        b[v >> 6] |= 1ULL << (v & 63);
        for (int k = 0; k < g->deg[v]; k++) {
            int u = g->adj[v][k];
            b[u >> 6] |= 1ULL << (u & 63);
        }
    }
    for (int r = 1; r < D; r++) {
        int nx = 1 - c;
        for (int v = 0; v < n; v++) {
            uint64_t *o = bits[nx][v];
            uint64_t *s = bits[c][v];
            for (int w = 0; w < W; w++) o[w] = s[w];
            for (int k = 0; k < g->deg[v]; k++) {
                uint64_t *t = bits[c][g->adj[v][k]];
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        c = nx;
    }
    long long reach = 0;
    for (int v = 0; v < n; v++)
        for (int w = 0; w < W; w++)
            reach += popc(bits[c][v][w]);
    return (long long)n * n - reach;
}

static int find_nb(int v, int u) {
    for (int k = 0; k < G.deg[v]; k++)
        if (G.adj[v][k] == u) return k;
    return -1;
}

static int adjq(int a, int b) {
    return find_nb(a, b) >= 0;
}

static void g_add(int a, int b) {
    G.adj[a][G.deg[a]++] = b;
    G.adj[b][G.deg[b]++] = a;
}

static void g_del(int a, int b) {
    int i = find_nb(a, b);
    int j = find_nb(b, a);
    G.adj[a][i] = G.adj[a][--G.deg[a]];
    G.adj[b][j] = G.adj[b][--G.deg[b]];
}

/* Greedily add edges between opposite-side vertices with spare degree. */
static void saturate(void) {
    int n = G.n;
    int off = rndint(n);
    for (int ii = 0; ii < n; ii++) {
        int a = (ii + off) % n;
        if (G.deg[a] >= d) continue;
        int off2 = rndint(n);
        for (int jj = 0; jj < n && G.deg[a] < d; jj++) {
            int b = (jj + off2) % n;
            if (G.side[b] == G.side[a] || G.deg[b] >= d) continue;
            if (adjq(a, b)) continue;
            g_add(a, b);
        }
    }
}

/* Double edge swap: edges (a1,c1),(a2,c2) -> (a1,c2),(a2,c1). a's on side 0. */
static int pick_swap(int *p) {
    int n = G.n;
    for (int tries = 0; tries < 50; tries++) {
        int x = rndint(n), y = rndint(n);
        if (G.deg[x] == 0 || G.deg[y] == 0) continue;
        int bx = G.adj[x][rndint(G.deg[x])];
        int by = G.adj[y][rndint(G.deg[y])];
        int a1 = (G.side[x] == 0) ? x : bx;
        int c1 = (G.side[x] == 0) ? bx : x;
        int a2 = (G.side[y] == 0) ? y : by;
        int c2 = (G.side[y] == 0) ? by : y;
        if (a1 == a2 || c1 == c2) continue;
        if (adjq(a1, c2) || adjq(a2, c1)) continue;
        p[0] = a1; p[1] = c1; p[2] = a2; p[3] = c2;
        return 1;
    }
    return 0;
}

/* Spare transfer: remove (a,b), add (v,b), where v has spare degree. */
static int pick_transfer(int *p) {
    int n = G.n;
    static int defi[MAXN];
    int cnt = 0;
    for (int v = 0; v < n; v++)
        if (G.deg[v] < d) defi[cnt++] = v;
    if (cnt == 0) return 0;
    for (int tries = 0; tries < 30; tries++) {
        int v = defi[rndint(cnt)];
        int b = rndint(n);
        if (G.side[b] == G.side[v] || G.deg[b] == 0 || adjq(v, b)) continue;
        int a = G.adj[b][rndint(G.deg[b])];
        p[0] = v; p[1] = b; p[2] = a;
        return 2;
    }
    return 0;
}

static void apply_move(int typ, const int *p) {
    if (typ == 1) {
        g_del(p[0], p[1]);
        g_del(p[2], p[3]);
        g_add(p[0], p[3]);
        g_add(p[2], p[1]);
    } else {
        g_del(p[2], p[1]);
        g_add(p[0], p[1]);
    }
}

static void undo_move(int typ, const int *p) {
    if (typ == 1) {
        g_del(p[0], p[3]);
        g_del(p[2], p[1]);
        g_add(p[0], p[1]);
        g_add(p[2], p[3]);
    } else {
        g_del(p[0], p[1]);
        g_add(p[2], p[1]);
    }
}

static int random_move(int *typ, int *p) {
    if (rnd64() & 1) {
        if (!pick_swap(p)) return 0;
        *typ = 1;
        return 1;
    }
    if (!pick_transfer(p)) return 0;
    *typ = 2;
    return 1;
}

/* Insert one vertex and try to repair with annealing. Returns 1 on success (G valid). */
static int try_grow(int iters) {
    int v = G.n;
    G.side[v] = rndint(2);
    G.deg[v] = 0;
    G.n++;
    saturate();
    long long c = cost_of(&G);
    for (int it = 0; it < iters && c > 0; it++) {
        if ((it & 31) == 0 && timeup()) break;
        double T = 2.0 * (1.0 - (double)it / iters) + 0.05;
        int typ = 0, p[4];
        if (!random_move(&typ, p)) continue;
        apply_move(typ, p);
        long long c2 = cost_of(&G);
        long long delta = c2 - c;
        double u = (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
        if (delta <= 0 || u < exp(-(double)delta / T)) {
            c = c2;
        } else {
            undo_move(typ, p);
        }
    }
    return c == 0;
}

/* Plateau walk: accept only moves that keep the graph valid. */
static void mix(int steps) {
    for (int s = 0; s < steps && !timeup(); s++) {
        int typ = 0, p[4];
        if (!random_move(&typ, p)) continue;
        apply_move(typ, p);
        if (cost_of(&G) != 0) undo_move(typ, p);
    }
}

static void print_graph(const Graph *g) {
    int m = 0;
    for (int v = 0; v < g->n; v++) m += g->deg[v];
    m /= 2;
    printf("%d %d\n", g->n, m);
    for (int v = 0; v < g->n; v++)
        for (int k = 0; k < g->deg[v]; k++) {
            int u = g->adj[v][k];
            if (v < u) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x2545F4914F6CDD1DULL + 0x51ED27ULL;
    if (rs == 0) rs = 1;
    tlimit = atof(argv[4]);

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        printf("0 0\n");
        return 0;
    }
    if (m < 0) m = 0;
    int *eu = malloc(sizeof(int) * (size_t)(m + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m + 1));
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) {
            m = i;
            break;
        }
    }

    int ok = (d >= 1 && d <= MAXD - 1 && D >= 2 && n >= 1 && n <= MAXN - 3);
    if (ok) {
        memset(&G, 0, sizeof(G));
        G.n = n;
        for (int i = 0; i < m && ok; i++) {
            int u = eu[i], v = ev[i];
            if (u < 0 || u >= n || v < 0 || v >= n || u == v) ok = 0;
            else if (G.deg[u] >= d || G.deg[v] >= d) ok = 0;
            else if (find_nb(u, v) >= 0) ok = 0;
            else g_add(u, v);
        }
    }
    if (ok) {
        static int col[MAXN], qu[MAXN];
        for (int i = 0; i < n; i++) col[i] = -1;
        for (int s = 0; s < n && ok; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int h = 0, t = 0;
            qu[t++] = s;
            while (h < t && ok) {
                int x = qu[h++];
                for (int k = 0; k < G.deg[x]; k++) {
                    int y = G.adj[x][k];
                    if (col[y] < 0) {
                        col[y] = 1 - col[x];
                        qu[t++] = y;
                    } else if (col[y] == col[x]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
        if (ok)
            for (int i = 0; i < n; i++) G.side[i] = col[i];
    }
    if (ok && cost_of(&G) != 0) ok = 0;

    if (!ok) {
        printf("%d %d\n", n, m);
        for (int i = 0; i < m; i++) printf("%d %d\n", eu[i], ev[i]);
        return 0;
    }

    saturate();
    while (!timeup() && G.n < MAXN - 2) {
        memcpy(&good, &G, sizeof(Graph));
        if (!try_grow(ITER)) {
            memcpy(&G, &good, sizeof(Graph));
            mix(MIX);
        }
    }
    print_graph(&G);
    return 0;
}
'''


def _grow_in_c(d, D, seed, graph, timeout, budget):
    """Run the C growth engine on a valid start graph; returns (n, edges) or None."""
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 3)],
                         stdin_graph=graph, timeout=timeout)
        return lib.parse_graph_text(text)
    except (RuntimeError, ValueError):
        return None


def build(d, D, seed, time_limit):
    start = time.monotonic()

    def left():
        return time_limit - (time.monotonic() - start)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured starts.
    if D >= 3:
        deadline = start + 0.2 * time_limit
        cands = _arc_extensions(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)
    if D >= 4 and time.monotonic() - start < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Bold main phase: C vertex-insertion growth from the best valid start.
    if D >= 3:
        avail = left() - 3.0
        if avail > 2.0:
            timeout = avail * 0.9
            budget = timeout * 0.85
            res = _grow_in_c(d, D, seed, best, timeout, budget)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
