import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: grows a valid bipartite graph one vertex at a time.
#
# Starting from a valid start graph, each growth step adds a vertex on a random
# side, fills its free degree greedily, and runs simulated annealing over edge
# moves (add, remove, move an endpoint, switch two edges). The cost is the
# number of ordered vertex pairs at distance > D, computed by bitset balls.
# Bipartiteness is kept by only ever joining opposite sides. The last valid
# graph is always kept as a snapshot and printed.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXW 16
#define MAXDEG 64
#define MAXE (MAXN * MAXDEG / 2)

typedef uint64_t Row[MAXW];

static int d, D, n, m_edges;
static int side[MAXN], deg[MAXN];
static int adj[MAXN][MAXDEG];
static unsigned char am[MAXN][MAXN];
static Row bufA[MAXN], bufB[MAXN];
static uint64_t rs = 88172645463325252ULL;
static clock_t t0c;
static time_t t0w;
static double budget;
static int eu[MAXE], ev[MAXE];
static int queue_[MAXN];

typedef struct { int op, u, v; } Op;
static Op logv[16];
static int nlog;

static int snap_n, snap_m;
static int snap_side[MAXN];
static int snap_eu[MAXE], snap_ev[MAXE];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int time_up(void) {
    double cpu = (double)(clock() - t0c) / CLOCKS_PER_SEC;
    double wall = difftime(time(NULL), t0w);
    return cpu >= budget || wall >= budget + 1.0;
}

/* Number of ordered pairs (v, w) with dist(v, w) > D. Zero means valid. */
static long cost_full(void) {
    int W = (n + 63) / 64;
    Row *cur = bufA, *nxt = bufB;
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, sizeof(Row));
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt[v];
            memcpy(o, cur[v], (size_t)W * sizeof(uint64_t));
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s = cur[adj[v][i]];
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        Row *t = cur;
        cur = nxt;
        nxt = t;
    }
    long c = 0;
    for (int v = 0; v < n; v++) {
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(cur[v][w]);
        c += n - cnt;
    }
    return c;
}

static void add_edge(int u, int v) {
    am[u][v] = 1;
    am[v][u] = 1;
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
    m_edges++;
}

static void del_nb(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][--deg[u]];
            return;
        }
    }
}

static void rem_edge(int u, int v) {
    am[u][v] = 0;
    am[v][u] = 0;
    del_nb(u, v);
    del_nb(v, u);
    m_edges--;
}

static void do_add(int u, int v) {
    add_edge(u, v);
    logv[nlog].op = 0;
    logv[nlog].u = u;
    logv[nlog].v = v;
    nlog++;
}

static void do_rem(int u, int v) {
    rem_edge(u, v);
    logv[nlog].op = 1;
    logv[nlog].u = u;
    logv[nlog].v = v;
    nlog++;
}

static void undo_all(void) {
    while (nlog > 0) {
        nlog--;
        if (logv[nlog].op == 0) rem_edge(logv[nlog].u, logv[nlog].v);
        else add_edge(logv[nlog].u, logv[nlog].v);
    }
}

static int rand_edge(int *pu, int *pv) {
    if (m_edges <= 0) return 0;
    for (int t = 0; t < 200; t++) {
        int u = rndint(n);
        if (deg[u] > 0) {
            *pu = u;
            *pv = adj[u][rndint(deg[u])];
            return 1;
        }
    }
    return 0;
}

/* Propose one move and apply it (logged). Returns 0 if nothing was applied. */
static int propose(void) {
    nlog = 0;
    double r = rnd01();
    if (r < 0.25) {  /* add an edge between two free vertices of opposite sides */
        for (int t = 0; t < 60; t++) {
            int x = rndint(n), y = rndint(n);
            if (x == y || side[x] == side[y] || deg[x] >= d || deg[y] >= d || am[x][y]) continue;
            do_add(x, y);
            return 1;
        }
        return 0;
    }
    if (r < 0.35) {  /* remove a random edge */
        int u, v;
        if (!rand_edge(&u, &v)) return 0;
        do_rem(u, v);
        return 1;
    }
    int a, b;
    if (!rand_edge(&a, &b)) return 0;
    if (r < 0.65) {  /* move endpoint a of edge (a,b) to a free c on a's side */
        for (int t = 0; t < 60; t++) {
            int c = rndint(n);
            if (c == a || side[c] != side[a] || deg[c] >= d || am[c][b]) continue;
            do_rem(a, b);
            do_add(c, b);
            return 1;
        }
        return 0;
    }
    /* switch: (a,b),(c,e) -> (a,e),(c,b) keeps all degrees */
    for (int t = 0; t < 60; t++) {
        int c, e;
        if (!rand_edge(&c, &e)) return 0;
        if (side[c] != side[a]) {
            int tmp = c;
            c = e;
            e = tmp;
        }
        if (side[c] != side[a] || c == a || e == b) continue;
        if (am[a][e] || am[c][b]) continue;
        do_rem(a, b);
        do_rem(c, e);
        do_add(a, e);
        do_add(c, b);
        return 1;
    }
    return 0;
}

static long anneal(long iters, double T0, double T1, long cur) {
    double lr = log(T1 / T0);
    for (long it = 0; it < iters; it++) {
        if (cur == 0) break;
        if ((it & 1023) == 0 && time_up()) break;
        double T = T0 * exp(lr * (double)it / (double)iters);
        if (!propose()) {
            nlog = 0;
            continue;
        }
        long c2 = cost_full();
        long delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = c2;
            nlog = 0;
        } else {
            undo_all();
        }
    }
    return cur;
}

static void take_snapshot(void) {
    snap_n = n;
    snap_m = 0;
    memcpy(snap_side, side, sizeof(int) * (size_t)n);
    for (int u = 0; u < n; u++) {
        for (int i = 0; i < deg[u]; i++) {
            int v = adj[u][i];
            if (u < v) {
                snap_eu[snap_m] = u;
                snap_ev[snap_m] = v;
                snap_m++;
            }
        }
    }
}

static void clear_graph(void) {
    for (int u = 0; u < n; u++) {
        for (int i = 0; i < deg[u]; i++) am[u][adj[u][i]] = 0;
        deg[u] = 0;
    }
    m_edges = 0;
    nlog = 0;
}

static void load_snapshot(void) {
    clear_graph();
    n = snap_n;
    memcpy(side, snap_side, sizeof(int) * (size_t)n);
    for (int i = 0; i < snap_m; i++) add_edge(snap_eu[i], snap_ev[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    budget = atof(argv[4]);
    t0c = clock();
    t0w = time(NULL);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || n0 > MAXN - 2 || m0 < 0 || m0 > MAXE ||
        d < 1 || d > MAXDEG - 4 || D < 1) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) {
            printf("0 0\n");
            return 0;
        }
    }
    n = n0;
    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || deg[u] >= d || deg[v] >= d || am[u][v]) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    /* Two-colour the graph. */
    for (int v = 0; v < n; v++) side[v] = -1;
    int bad = 0;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        queue_[t++] = s;
        while (h < t) {
            int u = queue_[h++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    queue_[t++] = v;
                } else if (side[v] == side[u]) {
                    bad = 1;
                }
            }
        }
    }
    if (bad || cost_full() != 0) {
        printf("0 0\n");
        return 0;
    }

    take_snapshot();
    const long ITERS = 12000;
    while (!time_up()) {
        if (snap_n + 2 >= MAXN) break;
        load_snapshot();
        int x = n++;
        side[x] = rndint(2);
        deg[x] = 0;
        int added = 0;
        for (int t = 0; t < 400 && added < d; t++) {
            int y = rndint(n);
            if (y == x || side[y] == side[x] || deg[y] >= d || am[x][y]) continue;
            add_edge(x, y);
            added++;
        }
        long c = cost_full();
        c = anneal(ITERS, 1.5, 0.08, c);
        if (c == 0) take_snapshot();
    }

    printf("%d %d\n", snap_n, snap_m);
    for (int i = 0; i < snap_m; i++) printf("%d %d\n", snap_eu[i], snap_ev[i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions (seeds for the C engine).
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


def _arc_graph(m, edges, S, point_lines, line_points):
    """Old PG(2,q) incidence plus a new A and a new B vertex for each element of S. Diameter 3."""
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
        if not cands:
            continue
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, S, point_lines, line_points))
    return out


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


def _grow_in_c(d, D, seed, n, edges, budget):
    """Run the C growth engine from a valid start graph; return (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                    stdin_graph=(n, edges), timeout=budget + 10.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    def left():
        return time_limit - (time.monotonic() - t0)

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
        cands = _arc_extensions(d, t0 + 0.15 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

    if D >= 4 and left() > 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Bold change: grow the best seed with the C annealing engine instead of
    # searching voltage lifts in Python. Skip when the seed already meets the
    # Moore bound (for example the d=3, D=3 calibration case).
    if D >= 3 and d <= 60 and best_n < lib.moore_bound(d, D):
        budget = min(0.6 * time_limit, left() - 4.0)
        if budget >= 1.0:
            try:
                n_c, e_c = _grow_in_c(d, D, seed, best_n, best[1], budget)
                consider(n_c, e_c)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
