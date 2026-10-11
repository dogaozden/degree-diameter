import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine.
#
# Works on a bipartite graph with max degree d and diameter <= D. It grows the
# graph one vertex at a time: attach a new vertex greedily (covering the other
# side), then run simulated annealing with degree-preserving edge moves to
# minimise the number of vertex pairs at distance > D. Any state with zero
# cost is a valid graph and becomes the new snapshot. The snapshot is printed
# at the end, so the output is always valid (or "1 0" if the input was bad).
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 1024
#define WMAX 16
#define MAXDEG 64
#define MAXIN 40000
#define ATTEMPT_ITERS 8000

static int d_, D_, n;
static int col[NMAX];
static int deg[NMAX];
static int adj[NMAX][MAXDEG];
static uint64_t R[2][NMAX][WMAX];
static uint64_t rs = 88172645463325252ULL;

static int sn;
static int scol[NMAX];
static int sdeg[NMAX];
static int sadj[NMAX][MAXDEG];

static double t_limit;
static clock_t t_start;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int timeup(void) {
    return (double)(clock() - t_start) / CLOCKS_PER_SEC > t_limit;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adj[a][i] == b) return 1;
    return 0;
}
static void del_arc(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a][i] == b) {
            adj[a][i] = adj[a][--deg[a]];
            return;
        }
    }
}
static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}
static void del_edge(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
}

/* Number of unordered vertex pairs at distance > D_. Zero means valid. */
static long long cost_eval(void) {
    int W = (n + 63) >> 6;
    int cur = 0;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) R[0][v][w] = 0;
        R[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D_; t++) {
        int nx = cur ^ 1;
        for (int v = 0; v < n; v++) {
            uint64_t *dst = R[nx][v];
            const uint64_t *src = R[cur][v];
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s2 = R[cur][adj[v][i]];
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        cur = nx;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(R[cur][v][w]);
        bad += n - c;
    }
    return bad / 2;
}

/* Greedy attach of new vertex x: pick opposite-colour neighbours that cover
   the most not-yet-covered vertices of x's colour class. */
static void greedy_attach(int x) {
    static int covered[NMAX];
    int cx = col[x];
    memset(covered, 0, sizeof(int) * (size_t)n);
    while (deg[x] < d_) {
        int best = -1;
        long long bestkey = -1;
        int bestg = 0;
        for (int y = 0; y < n; y++) {
            if (y == x || col[y] == cx || deg[y] >= d_ || has_edge(x, y)) continue;
            int g = 0;
            for (int i = 0; i < deg[y]; i++) {
                int u = adj[y][i];
                if (col[u] == cx && !covered[u]) g++;
            }
            long long key = (long long)g * 100000LL + rndint(100000);
            if (key > bestkey) {
                bestkey = key;
                best = y;
                bestg = g;
            }
        }
        if (best < 0 || bestg == 0) break;
        add_edge(x, best);
        for (int i = 0; i < deg[best]; i++) {
            int u = adj[best][i];
            if (col[u] == cx) covered[u] = 1;
        }
    }
}

/* Moves: remove list (ra,rb) and add list (aa,ab). */
typedef struct {
    int nr, na;
    int ra[2], rb[2], aa[2], ab[2];
} Move;

static void do_move(const Move *m, int undo) {
    const int *ra = undo ? m->aa : m->ra;
    const int *rb = undo ? m->ab : m->rb;
    const int *aa = undo ? m->ra : m->aa;
    const int *ab = undo ? m->rb : m->ab;
    int nr = undo ? m->na : m->nr;
    int na = undo ? m->nr : m->na;
    for (int i = 0; i < nr; i++) del_edge(ra[i], rb[i]);
    for (int i = 0; i < na; i++) add_edge(aa[i], ab[i]);
}

static int rand_edge(int *a, int *b) {
    for (int t = 0; t < 100; t++) {
        int v = rndint(n);
        if (deg[v] > 0) {
            *a = v;
            *b = adj[v][rndint(deg[v])];
            return 1;
        }
    }
    return 0;
}

static int find_spare(int c) {
    for (int t = 0; t < 200; t++) {
        int v = rndint(n);
        if (col[v] == c && deg[v] < d_) return v;
    }
    return -1;
}

/* Move one endpoint of an edge to another vertex of the same colour. */
static int mk_end(Move *m, int side) {
    int a, b;
    if (!rand_edge(&a, &b)) return 0;
    if (side == 1) {
        int b2 = find_spare(col[b]);
        if (b2 < 0 || b2 == b || has_edge(a, b2)) return 0;
        m->nr = 1; m->na = 1;
        m->ra[0] = a; m->rb[0] = b;
        m->aa[0] = a; m->ab[0] = b2;
    } else {
        int a2 = find_spare(col[a]);
        if (a2 < 0 || a2 == a || has_edge(a2, b)) return 0;
        m->nr = 1; m->na = 1;
        m->ra[0] = a; m->rb[0] = b;
        m->aa[0] = a2; m->ab[0] = b;
    }
    return 1;
}

/* Degree-preserving swap of two edges. */
static int mk_swap(Move *m) {
    int a1, b1, a2, b2;
    if (!rand_edge(&a1, &b1) || !rand_edge(&a2, &b2)) return 0;
    if (col[a1] != col[a2] || a1 == a2 || b1 == b2) return 0;
    if (has_edge(a1, b2) || has_edge(a2, b1)) return 0;
    m->nr = 2; m->na = 2;
    m->ra[0] = a1; m->rb[0] = b1;
    m->ra[1] = a2; m->rb[1] = b2;
    m->aa[0] = a1; m->ab[0] = b2;
    m->aa[1] = a2; m->ab[1] = b1;
    return 1;
}

/* Add a new edge between spare vertices of opposite colours. */
static int mk_add(Move *m) {
    int a = find_spare(0);
    int b = find_spare(1);
    if (a < 0 || b < 0 || has_edge(a, b)) return 0;
    m->nr = 0; m->na = 1;
    m->aa[0] = a; m->ab[0] = b;
    return 1;
}

static long long sa_run(long long maxit) {
    long long cost = cost_eval();
    const double T0 = 2.5, T1 = 0.12;
    for (long long it = 0; it < maxit && cost > 0; it++) {
        if ((it & 15) == 0 && timeup()) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)maxit);
        Move m;
        int ok;
        double r = rnd01();
        if (r < 0.40) ok = mk_end(&m, 1);
        else if (r < 0.80) ok = mk_end(&m, 2);
        else if (r < 0.92) ok = mk_swap(&m);
        else ok = mk_add(&m);
        if (!ok) continue;
        do_move(&m, 0);
        long long c2 = cost_eval();
        long long delta = c2 - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cost = c2;
        } else {
            do_move(&m, 1);
        }
    }
    return cost;
}

static void save_state(void) {
    sn = n;
    memcpy(scol, col, sizeof(int) * (size_t)n);
    memcpy(sdeg, deg, sizeof(int) * (size_t)n);
    memcpy(sadj, adj, sizeof(adj));
}

static void restore_state(void) {
    n = sn;
    memcpy(col, scol, sizeof(int) * (size_t)sn);
    memcpy(deg, sdeg, sizeof(int) * (size_t)sn);
    memcpy(adj, sadj, sizeof(adj));
}

static void print_snapshot(void) {
    int m = 0;
    for (int v = 0; v < sn; v++)
        for (int i = 0; i < sdeg[v]; i++)
            if (sadj[v][i] > v) m++;
    printf("%d %d\n", sn, m);
    for (int v = 0; v < sn; v++)
        for (int i = 0; i < sdeg[v]; i++)
            if (sadj[v][i] > v) printf("%d %d\n", v, sadj[v][i]);
}

static int stackv[NMAX];
static int eu[MAXIN], ev[MAXIN];

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("1 0\n");
        return 0;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    t_limit = atof(argv[4]);
    t_start = clock();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        printf("1 0\n");
        return 0;
    }
    if (n0 < 1 || n0 > NMAX - 2 || m0 < 0 || m0 > MAXIN ||
        d_ < 1 || d_ > MAXDEG - 4 || D_ < 1) {
        printf("1 0\n");
        return 0;
    }
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) {
            printf("1 0\n");
            return 0;
        }
    }

    n = n0;
    int ok = 1;
    for (int v = 0; v < n; v++) {
        deg[v] = 0;
        col[v] = -1;
    }
    for (int i = 0; i < m0 && ok; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) ok = 0;
        else if (has_edge(u, v)) ok = 0;
        else if (deg[u] >= d_ || deg[v] >= d_) ok = 0;
        else add_edge(u, v);
    }
    /* bipartition check */
    for (int s = 0; s < n && ok; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        stackv[sp++] = s;
        while (sp > 0 && ok) {
            int u = stackv[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[u][i];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    stackv[sp++] = w;
                } else if (col[w] == col[u]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    if (ok) ok = (cost_eval() == 0);
    if (!ok) {
        printf("1 0\n");
        return 0;
    }

    save_state();
    while (!timeup() && n < NMAX - 1) {
        restore_state();
        int x = n;
        n++;
        col[x] = rndint(2);
        deg[x] = 0;
        greedy_attach(x);
        long long c = sa_run(ATTEMPT_ITERS);
        if (c == 0) save_state();
    }
    print_snapshot();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3). Used as the
# starting point for the C search.
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
    """Extended graph: old PG incidence plus a new A and a new B vertex per element of S."""
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
# Greedy spare-capacity fill (diameter 3), checked exactly.
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
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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
        cands = _arc_extensions(d, t0 + 0.15 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)
        if best_n > 2:
            n_f, e_f = _fill(best_n, best[1], d, D, t0 + 0.05 * time_limit,
                             random.Random(seed * 104729 + d))
            consider(n_f, e_f)

    # Strong new stage: C annealing that grows the best graph one vertex at a time.
    moore = lib.moore_bound(d, D)
    if D >= 3 and best_n < moore:
        remaining = time_limit - (time.monotonic() - t0)
        budget = max(0.0, remaining * 0.88 - 2.0)
        if budget >= 1.0 and d <= 60 and best_n < 1000:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=best,
                                timeout=budget + 2.0 + 0.02 * remaining)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
