"""Combined program: Python builds the strongest closed-form or arc-extended construction it can
(projective planes, Araujo-Pardo-Lopez, independent A/B arc extensions with extra A-B edges, and
W(q) for D >= 4). The C engine then runs dominating-set insertion (exact cover of all vertices by
radius-(D-1) balls of spare neighbours, which keeps the diameter by construction) and falls back to
annealed two-vertex growth with degree-preserving edge swaps whenever insertion stalls. It only
ever keeps valid graphs."""
import itertools
import random
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1024
#define MAXD 32
#define MAXW (MAXN / 64)
#define INF 100

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static uint64_t rng_state = 88172645463325252ULL;

static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        if (s > 1000000L) break;
        p *= (d - 1);
    }
    return 2 * s;
}

/* ------------------------------------------------------------ graph basics */

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void del_half(Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][--g->deg[u]];
            return;
        }
}

static void del_edge(Graph *g, int u, int v) {
    del_half(g, u, v);
    del_half(g, v, u);
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * (size_t)src->deg[v]);
    }
}

/* ------------------------------------------------------------ diameter check */

static uint64_t RA[MAXN][MAXW], RB[MAXN][MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D; fills badv[v] = bad partners of v. */
static long bad_pairs(const Graph *g) {
    int n = g->n, nw = (n + 63) / 64;
    uint64_t (*cur)[MAXW] = RA, (*nxt)[MAXW] = RB, (*tmp)[MAXW];
    memset(RA, 0, sizeof(uint64_t) * MAXW * (size_t)n);
    for (int v = 0; v < n; v++) cur[v][v >> 6] |= 1ULL << (v & 63);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < nw; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                for (int w = 0; w < nw; w++) nxt[v][w] |= cur[u][w];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += pc64(cur[v][w]);
        badv[v] = n - c;
        total += n - c;
    }
    return total / 2;
}

static int valid_graph(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            if (!has_edge(g, u, v)) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

/* ------------------------------------------------------------ distances */

static unsigned char dist[MAXN][MAXN];
static int qbuf[MAXN];

static void compute_dist(const Graph *g) {
    int n = g->n;
    for (int s = 0; s < n; s++) {
        unsigned char *row = dist[s];
        for (int x = 0; x < n; x++) row[x] = INF;
        row[s] = 0;
        int h = 0, t = 0;
        qbuf[t++] = s;
        while (h < t) {
            int u = qbuf[h++];
            for (int k = 0; k < g->deg[u]; k++) {
                int v = g->adj[u][k];
                if (row[v] == INF) {
                    row[v] = (unsigned char)(row[u] + 1);
                    qbuf[t++] = v;
                }
            }
        }
    }
}

/* ------------------------------------------------------------ dominating insertion */

static uint64_t ball[MAXN][MAXW];
static int cand_[MAXN], used_[MAXN], sel_[MAXD + 1], bestsel_[MAXD + 1];

static void build_balls(int n) {
    int nw = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < nw; w++) ball[v][w] = 0;
        for (int x = 0; x < n; x++)
            if (dist[v][x] <= D - 1) ball[v][x >> 6] |= 1ULL << (x & 63);
    }
}

/* Greedy cover of all vertices by balls of spare vertices on side c.
   On success writes the chosen neighbours to bestsel_ and returns their count. */
static int try_insert(const Graph *g, int c, int restarts) {
    int n = g->n, nw = (n + 63) / 64, nc = 0;
    for (int v = 0; v < n; v++)
        if (g->side[v] == c && g->deg[v] < d) cand_[nc++] = v;
    if (nc == 0) return -1;
    uint64_t unc[MAXW];
    for (int r = 0; r < restarts; r++) {
        for (int w = 0; w < nw; w++) unc[w] = 0;
        for (int x = 0; x < n; x++) unc[x >> 6] |= 1ULL << (x & 63);
        int uncount = n, ns = 0;
        for (int i = 0; i < nc; i++) used_[i] = 0;
        while (uncount > 0 && ns < d) {
            int bi = -1;
            long long bkey = -1;
            for (int i = 0; i < nc; i++) {
                if (used_[i]) continue;
                const uint64_t *b = ball[cand_[i]];
                int gain = 0;
                for (int w = 0; w < nw; w++) gain += pc64(b[w] & unc[w]);
                if (gain == 0) continue;
                long long key = (long long)gain * 4096 + rndint(4096);
                if (key > bkey) { bkey = key; bi = i; }
            }
            if (bi < 0) break;
            used_[bi] = 1;
            sel_[ns++] = cand_[bi];
            uncount = 0;
            for (int w = 0; w < nw; w++) {
                unc[w] &= ~ball[cand_[bi]][w];
                uncount += pc64(unc[w]);
            }
        }
        if (uncount == 0 && ns > 0) {
            for (int k = 0; k < ns; k++) bestsel_[k] = sel_[k];
            return ns;
        }
    }
    return -1;
}

/* Add a vertex on side 1-c adjacent to bestsel_[0..ns-1]; dist stays exact. */
static void insert_vertex(Graph *g, int c, int ns) {
    int v = g->n++;
    g->side[v] = (unsigned char)(1 - c);
    g->deg[v] = 0;
    for (int k = 0; k < ns; k++) add_edge(g, v, bestsel_[k]);
    static int dv[MAXN];
    for (int x = 0; x < v; x++) {
        int m = INF;
        for (int k = 0; k < ns; k++) {
            int t = dist[x][bestsel_[k]];
            if (t < m) m = t;
        }
        dv[x] = (m + 1 > INF) ? INF : m + 1;
    }
    for (int x = 0; x < v; x++) {
        dist[x][v] = (unsigned char)dv[x];
        dist[v][x] = (unsigned char)dv[x];
    }
    dist[v][v] = 0;
    for (int x = 0; x < v; x++)
        for (int y = 0; y < v; y++) {
            int t = dv[x] + dv[y];
            if (t > INF) t = INF;
            if (t < dist[x][y]) dist[x][y] = (unsigned char)t;
        }
}

/* ------------------------------------------------------------ grow by two + anneal */

static int used_stamp[MAXN];
static int stamp_ = 0;

static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 >= MAXN) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = 0;
    work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    stamp_++;
    used_stamp[x] = stamp_;
    used_stamp[y] = stamp_;
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used_stamp[a] == stamp_ || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (b >= n || used_stamp[b] == stamp_) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used_stamp[a] = stamp_;
        used_stamp[b] = stamp_;
        k++;
    }
    long bad = bad_pairs(work);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (s == v || work->side[s] != work->side[v] || work->deg[s] == 0) continue;
        int t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
        long nb = bad_pairs(work);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(work, v, t);
            del_edge(work, s, u);
            add_edge(work, v, u);
            add_edge(work, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return valid_graph(work);
}

/* ------------------------------------------------------------ IO */

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= d ? 1 : 0;
    }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

static void read_start(Graph *g) {
    static int queue[MAXN];
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) {
        g->deg[v] = 0;
        g->side[v] = 255;
    }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            u == v || g->deg[u] >= d || g->deg[v] >= d || has_edge(g, u, v)) {
            g->n = 0;
            return;
        }
        add_edge(g, u, v);
    }
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) {
                    g->side[u] = (unsigned char)(1 - g->side[v]);
                    queue[tail++] = u;
                } else if (g->side[u] == g->side[v]) {
                    g->n = 0;
                    return;
                }
            }
        }
    }
    if (!valid_graph(g)) g->n = 0;
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    if (d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best, work;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!valid_graph(&best)) complete_bipartite(&best);

    long moore = moore_bound();
    compute_dist(&best);
    while (now() < t_end) {
        int did = 0;
        if (best.n < moore && best.n + 2 < MAXN) {
            build_balls(best.n);
            int first = rndint(2);
            for (int t = 0; t < 2 && !did; t++) {
                int c = (t == 0) ? first : 1 - first;
                int ns = try_insert(&best, c, 6);
                if (ns > 0) {
                    insert_vertex(&best, c, ns);
                    did = 1;
                }
            }
        }
        if (did) continue;
        double left = t_end - now();
        if (left <= 0) break;
        double slice = left < 3.0 ? left : (left / 6.0 > 3.0 ? left / 6.0 : 3.0);
        if (grow_once(&best, &work, now() + slice)) {
            copy_graph(&best, &work);
            compute_dist(&best);
        }
    }
    if (!valid_graph(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Projective-plane arc extensions (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#   A-side: a set SA of points, each joined to a new vertex on the lines through it.
#           Constraint: every line holds <= s points of SA.
#   B-side: a set SB of lines, each joined to a new vertex on the points of it.
#           Constraint: every point lies on <= s lines of SB.
# The sides are independent. Afterwards, spare degree on the new A and B vertices
# is used for extra A-B edges, which can only shorten distances.
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


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by <= s elements of S, where element x hits nbr[x]."""
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
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line.
    A-vertices are 2m..2m+na-1 and B-vertices 2m+na..n-1."""
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
    return n, E, list(range(2 * m, 2 * m + na)), list(range(2 * m + na, n))


def _fill_ab(n, edges, d, A, B):
    """Greedily add A-B edges while both endpoints have spare degree. Keeps diameter and bipartiteness."""
    deg = [0] * n
    have = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        have.add((u, v) if u < v else (v, u))
    E = list(edges)
    for a in A:
        for b in B:
            if deg[a] >= d:
                break
            if deg[b] >= d:
                continue
            key = (a, b) if a < b else (b, a)
            if key in have:
                continue
            have.add(key)
            deg[a] += 1
            deg[b] += 1
            E.append(key)
    return n, E


def _arc_candidates(d, deadline, rng):
    """(n, edges) candidates from arc-extended projective planes, one per prime power q."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, point_lines, line_points, index = _pg_data(q)
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
        n_c, e_c, A, B = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append(_fill_ab(n_c, e_c, d, A, B))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used only for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    """W(q) for the largest prime power q <= min(d - 1, 7), for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def known_start(d, D):
    """Best closed-form graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = (cand[0], cand[1])

    if D >= 3:
        consider(known_start(d, D))
        rng = random.Random(seed * 7919 + d)
        for cand in sorted(_arc_candidates(d, t0 + 0.15 * time_limit, rng), key=lambda t: -t[0]):
            consider(cand)

    if D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # Hand the best construction to C: it inserts vertices, or grows by two with annealing.
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget > 0.5 and best[0] < lib.moore_bound(d, D):
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 5)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except (RuntimeError, ValueError):
            pass   # keep the construction if the search fails

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
