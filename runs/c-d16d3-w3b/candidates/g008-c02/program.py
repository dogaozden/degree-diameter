import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: grow-and-repair annealing on bipartite graphs of diameter <= D.
#
# State: a bipartite graph with max degree d. Cost = number of ordered pairs
# at distance > D (bitset BFS). Moves: add an edge between spare vertices of
# opposite colour, or rewire one edge endpoint to another spare vertex of the
# same colour. When cost reaches 0 the graph is recorded and a new vertex is
# grown onto spare degree; the annealer then repairs the diameter. After a
# stall the best valid graph is restored and growth is retried.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1536
#define MAXW 24
#define MAXDEG 64
#define MAXE (MAXN * MAXDEG / 2)

typedef struct { int kind, a, b, c, f; } Mv;

static int d, D, N;
static int col[MAXN];
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static unsigned char am[MAXN][MAXN];
static uint64_t RA[MAXN][MAXW];
static uint64_t RB[MAXN][MAXW];

static int bestN = 0, bm = 0;
static int bcol[MAXN];
static int bu[MAXE], bv[MAXE];
static int eu[MAXE], ev[MAXE];

static uint64_t rs = 1;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rnd_int(int n) { return (int)(rnd() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int pop64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long cost(void) {
    int w = (N + 63) / 64;
    uint64_t (*cu)[MAXW] = RA;
    uint64_t (*nx)[MAXW] = RB;
    uint64_t (*tmp)[MAXW];
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < w; k++) cu[v][k] = 0;
        cu[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < D; s++) {
        for (int v = 0; v < N; v++) {
            for (int k = 0; k < w; k++) nx[v][k] = cu[v][k];
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = cu[adj[v][i]];
                for (int k = 0; k < w; k++) nx[v][k] |= src[k];
            }
        }
        tmp = cu; cu = nx; nx = tmp;
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int k = 0; k < w; k++) c += pop64(cu[v][k]);
        bad += N - c;
    }
    return bad;
}

static void rem_from(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a][i] == b) {
            adj[a][i] = adj[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void add_edge(int a, int b) {
    if (deg[a] >= MAXDEG || deg[b] >= MAXDEG) return;
    am[a][b] = 1;
    am[b][a] = 1;
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void del_edge(int a, int b) {
    am[a][b] = 0;
    am[b][a] = 0;
    rem_from(a, b);
    rem_from(b, a);
}

static void clear_graph(void) {
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg[v]; i++) am[v][adj[v][i]] = 0;
        deg[v] = 0;
    }
    N = 0;
}

static void save_best(void) {
    bestN = N;
    bm = 0;
    for (int v = 0; v < N; v++) {
        bcol[v] = col[v];
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v][i];
            if (v < u && bm < MAXE) {
                bu[bm] = v;
                bv[bm] = u;
                bm++;
            }
        }
    }
}

static void restore_best(void) {
    clear_graph();
    N = bestN;
    for (int v = 0; v < N; v++) {
        col[v] = bcol[v];
        deg[v] = 0;
    }
    for (int i = 0; i < bm; i++) add_edge(bu[i], bv[i]);
}

static int grow(void) {
    static int cand[MAXN];
    if (N >= MAXN - 1) return 0;
    int c0 = rnd_int(2);
    for (int t = 0; t < 2; t++) {
        int c = (t == 0) ? c0 : 1 - c0;
        int nc = 0;
        for (int v = 0; v < N; v++)
            if (col[v] != c && deg[v] < d) cand[nc++] = v;
        if (nc == 0) continue;
        for (int i = nc - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int tt = cand[i];
            cand[i] = cand[j];
            cand[j] = tt;
        }
        int v = N;
        col[v] = c;
        deg[v] = 0;
        int k = d < nc ? d : nc;
        for (int i = 0; i < k; i++) add_edge(v, cand[i]);
        N++;
        return 1;
    }
    return 0;
}

static int mv_add(Mv *m) {
    int a = rnd_int(N);
    if (deg[a] >= d) return 0;
    int st = rnd_int(N);
    for (int i = 0; i < N; i++) {
        int b = (st + i) % N;
        if (col[b] != col[a] && deg[b] < d && !am[a][b]) {
            add_edge(a, b);
            m->kind = 1;
            m->a = a;
            m->b = b;
            return 1;
        }
    }
    return 0;
}

static int mv_rewire(Mv *m) {
    int x = rnd_int(N);
    if (deg[x] == 0) return 0;
    int y = adj[x][rnd_int(deg[x])];
    int e = x, f = y;
    if (rnd_int(2)) {
        e = y;
        f = x;
    }
    int st = rnd_int(N), nw = -1;
    for (int i = 0; i < N; i++) {
        int v = (st + i) % N;
        if (v != e && col[v] == col[e] && deg[v] < d && !am[v][f]) {
            nw = v;
            break;
        }
    }
    if (nw < 0) return 0;
    del_edge(x, y);
    add_edge(nw, f);
    m->kind = 2;
    m->a = x;
    m->b = y;
    m->c = nw;
    m->f = f;
    return 1;
}

static void undo(const Mv *m) {
    if (m->kind == 1) {
        del_edge(m->a, m->b);
    } else if (m->kind == 2) {
        del_edge(m->c, m->f);
        add_edge(m->a, m->b);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tlim = atof(argv[4]);
    if (d < 1) d = 1;
    if (d > MAXDEG) d = MAXDEG;
    if (D < 1) D = 1;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        n = 0;
        m = 0;
    }
    if (n < 0 || n > MAXN - 2) n = 0;
    int ne = 0;
    for (int i = 0; i < m; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (ne < MAXE) {
            eu[ne] = a;
            ev[ne] = b;
            ne++;
        }
    }
    N = n;
    for (int i = 0; i < ne; i++) {
        int a = eu[i], b = ev[i];
        if (a < 0 || b < 0 || a >= N || b >= N || a == b) continue;
        if (am[a][b] || deg[a] >= d || deg[b] >= d) continue;
        add_edge(a, b);
    }
    if (N == 0) {
        N = 2;
        col[0] = 0;
        col[1] = 1;
        deg[0] = deg[1] = 0;
        add_edge(0, 1);
    } else {
        static int q[MAXN];
        for (int v = 0; v < N; v++) col[v] = -1;
        for (int s = 0; s < N; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int hd = 0, tq = 0;
            q[tq++] = s;
            while (hd < tq) {
                int u = q[hd++];
                for (int i = 0; i < deg[u]; i++) {
                    int w = adj[u][i];
                    if (col[w] < 0) {
                        col[w] = 1 - col[u];
                        q[tq++] = w;
                    }
                }
            }
        }
        for (int v = 0; v < N; v++) {
            int i = 0;
            while (i < deg[v]) {
                int u = adj[v][i];
                if (col[u] == col[v]) del_edge(v, u);
                else i++;
            }
        }
    }

    double t0 = now_s();
    double deadline = t0 + tlim;
    long cur = cost();
    if (cur == 0) save_best();
    double T = 0.6;
    long stall = 0;
    const long STALL = 12000;
    long idle = 0;

    while (now_s() < deadline) {
        if (cur == 0) {
            if (N > bestN) save_best();
            if (grow()) {
                cur = cost();
                stall = 0;
                T = 0.25 + 0.9 * rnd_unit();
                continue;
            }
            Mv mv;
            int ok = rnd_int(2) ? mv_rewire(&mv) : mv_add(&mv);
            if (!ok) {
                if (++idle > 300000) break;
                continue;
            }
            if (cost() != 0) undo(&mv);
            continue;
        }
        Mv mv;
        int ok = (rnd_unit() < 0.3) ? mv_add(&mv) : mv_rewire(&mv);
        if (ok) {
            long c2 = cost();
            if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / T)) cur = c2;
            else undo(&mv);
        }
        if (++stall > STALL) {
            stall = 0;
            if (bestN > 0) {
                restore_best();
                cur = cost();
            }
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bm);
    for (int i = 0; i < bm; i++) printf("%d %d\n", bu[i], bv[i]);
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, S, line_points):
    """Build the extended graph: old PG incidence plus a new A and a new B vertex per element of S."""
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
        n_c, e_c = _arc_graph(m, edges, point_lines, S, line_points)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Spare-capacity fill (diameter 3), exact-checked.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """2-colouring of a bipartite graph given by adjacency lists."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _fill(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover the opposite side; return (n, edges)."""
    edges = list(edges)
    fails = 0
    while time.monotonic() < deadline and fails < 400:
        adj = [[] for _ in range(n)]
        for u, v in edges:
            adj[u].append(v)
            adj[v].append(u)
        deg = [len(a) for a in adj]
        col = _bipartition(n, adj)
        c = rng.randrange(2)
        uncovered = {v for v in range(n) if col[v] == 1 - c}
        cand = [v for v in range(n) if col[v] == c and deg[v] < d]
        chosen = []
        chosen_set = set()
        while uncovered and len(chosen) < d:
            best_v = None
            best_key = None
            for v in cand:
                if v in chosen_set:
                    continue
                g = 0
                for u in adj[v]:
                    if u in uncovered:
                        g += 1
                if g == 0:
                    continue
                key = (g, rng.random())
                if best_key is None or key > best_key:
                    best_key = key
                    best_v = v
            if best_v is None:
                break
            chosen.append(best_v)
            chosen_set.add(best_v)
            for u in adj[best_v]:
                uncovered.discard(u)
        if uncovered:
            fails += 1
            continue
        new_edges = edges + [(v, n) for v in chosen]
        if lib.is_valid(n + 1, new_edges, d, D):
            edges = new_edges
            n += 1
            fails = 0
        else:
            fails += 1
    return n, edges


# ----------------------------------------------------------------------------
# Glue for the C engine.
# ----------------------------------------------------------------------------

def _has_spare(n, edges, d):
    """True if some vertex has degree below d (room for the C engine to grow or rewire)."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return any(x < d for x in deg)


def _c_search(d, D, graph, seed, budget):
    """Run the C grow-and-repair annealer from graph; return (n, edges) or None."""
    n, edges = graph
    if budget < 1.0 or not (1 <= d <= 60) or not edges or n > 1400:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed % 1000003, round(budget, 2)],
                        stdin_graph=(n, edges),
                        timeout=budget + 2.0 + min(3.0, 0.2 * budget))
        return lib.parse_graph_text(out)
    except (RuntimeError, ValueError):
        return None


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    tl = float(time_limit)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.12 * tl, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)
        if best_n > 2:
            n_f, e_f = _fill(best_n, best[1], d, D, t0 + 0.25 * tl,
                             random.Random(seed * 104729 + d))
            consider(n_f, e_f)

    # Main stage: C grow-and-repair annealing from the best valid graph so far.
    if D >= 3 and _has_spare(best_n, best[1], d):
        budget = t0 + 0.75 * tl - time.monotonic() - 2.0
        res = _c_search(d, D, best, seed, budget)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
