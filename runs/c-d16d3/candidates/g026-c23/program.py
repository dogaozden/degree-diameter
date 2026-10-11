import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S
# such that every line holds at most s points of S and every point lies on at
# most s lines indexed by S. For each P in S add an A-vertex joined to the q+1
# lines through P; for each j in S add a B-vertex joined to the q+1 points on j.
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
# C search engine.
#
# Maintains a valid bipartite graph with max degree d and diameter D.
# Moves:
#  * Insertion: a new vertex on side s joined to <= d spare vertices of the
#    other side whose (D-1)-balls cover all vertices. Randomized greedy set
#    cover with random tie-breaks. Keeps every old distance, so validity holds.
#  * Densify: add a random spare cross edge (always keeps validity).
#  * Remove: delete a random edge, keep it only if the graph is still valid.
#  * Switch: degree-preserving 2-switch, kept only if still valid.
# Vertices are never removed, so the final graph has at least the start order.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4096
#define MAXW 64
#define MAXDEG 64
#define MAXM 200000

static int N = 0, DEG_MAX = 0, DIAM = 0;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int col[MAXN];
static uint64_t bufA[MAXN * MAXW];
static uint64_t bufB[MAXN * MAXW];
static uint64_t covered[MAXW];
static int taken[MAXN];
static int stamp = 0;
static int inU[MAXM], inV[MAXM];
static int inM = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_arc(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][--deg[u]];
            return;
        }
    }
}

static void remove_edge(int u, int v) {
    del_arc(u, v);
    del_arc(v, u);
}

/* Bitset rows: row v (stride W) = all vertices within distance radius of v. */
static uint64_t *reach(int radius) {
    int W = (N + 63) >> 6;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < radius; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int i = 0; i < W; i++) dst[i] = src[i];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *s2 = cur + (size_t)adj[v][k] * W;
                for (int i = 0; i < W; i++) dst[i] |= s2[i];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    return cur;
}

static int full_cover(const uint64_t *c, int W) {
    for (int w = 0; w < W; w++) {
        int rem = N - w * 64;
        uint64_t want = rem >= 64 ? ~0ULL : ((1ULL << rem) - 1);
        if ((c[w] & want) != want) return 0;
    }
    return 1;
}

static int is_valid(void) {
    for (int v = 0; v < N; v++) {
        if (deg[v] > DEG_MAX) return 0;
        for (int k = 0; k < deg[v]; k++)
            if (col[adj[v][k]] == col[v]) return 0;
    }
    int W = (N + 63) >> 6;
    uint64_t *b = reach(DIAM);
    for (int v = 0; v < N; v++)
        if (!full_cover(b + (size_t)v * W, W)) return 0;
    return 1;
}

/* Insert a vertex of colour `side` adjacent to a cover of all vertices by
   (D-1)-balls of spare vertices of the other colour. */
static int try_insert(int side, int trials, const uint64_t *b) {
    int W = (N + 63) >> 6;
    static int cand[MAXN];
    static int chosen[MAXDEG];
    int nc = 0;
    for (int u = 0; u < N; u++)
        if (col[u] == 1 - side && deg[u] < DEG_MAX) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int t = 0; t < trials; t++) {
        stamp++;
        for (int w = 0; w < W; w++) covered[w] = 0;
        int nch = 0;
        while (nch < DEG_MAX && !full_cover(covered, W)) {
            int best = -1, bestg = 0, ties = 0;
            for (int i = 0; i < nc; i++) {
                int u = cand[i];
                if (taken[u] == stamp) continue;
                const uint64_t *bu = b + (size_t)u * W;
                int g = 0;
                for (int w = 0; w < W; w++) g += popc(bu[w] & ~covered[w]);
                if (g > bestg) {
                    bestg = g;
                    best = u;
                    ties = 1;
                } else if (g == bestg && g > 0) {
                    ties++;
                    if (rndint(ties) == 0) best = u;
                }
            }
            if (best < 0) break;
            taken[best] = stamp;
            chosen[nch++] = best;
            const uint64_t *bb = b + (size_t)best * W;
            for (int w = 0; w < W; w++) covered[w] |= bb[w];
        }
        if (nch >= 1 && full_cover(covered, W)) {
            int w = N;
            N++;
            deg[w] = 0;
            col[w] = side;
            for (int i = 0; i < nch; i++) add_edge(w, chosen[i]);
            return 1;
        }
    }
    return 0;
}

static int densify_one(void) {
    static int s0[MAXN], s1[MAXN];
    int n0 = 0, n1 = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < DEG_MAX) {
            if (col[v] == 0) s0[n0++] = v;
            else s1[n1++] = v;
        }
    }
    if (n0 == 0 || n1 == 0) return 0;
    for (int t = 0; t < 100; t++) {
        int u = s0[rndint(n0)], v = s1[rndint(n1)];
        if (!has_edge(u, v)) {
            add_edge(u, v);
            return 1;
        }
    }
    return 0;
}

static int rand_edge(int *a, int *b) {
    if (N <= 0) return 0;
    for (int t = 0; t < 50; t++) {
        int x = rndint(N);
        if (deg[x] == 0) continue;
        int y = adj[x][rndint(deg[x])];
        if (col[x] == 0) {
            *a = x;
            *b = y;
        } else {
            *a = y;
            *b = x;
        }
        return 1;
    }
    return 0;
}

static void remove_move(void) {
    int a, b;
    if (!rand_edge(&a, &b)) return;
    remove_edge(a, b);
    if (!is_valid()) add_edge(a, b);
}

static void switch_move(void) {
    int a, b, c, e;
    if (!rand_edge(&a, &b) || !rand_edge(&c, &e)) return;
    if (a == c || b == e || has_edge(a, e) || has_edge(c, b)) return;
    remove_edge(a, b);
    remove_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    if (!is_valid()) {
        remove_edge(a, e);
        remove_edge(c, b);
        add_edge(a, b);
        add_edge(c, e);
    }
}

static void print_graph(void) {
    int cnt = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) cnt++;
    printf("%d %d\n", N, cnt);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) printf("%d %d\n", v, adj[v][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG_MAX = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    for (int i = 0; i < 10; i++) rnd64();

    if (DEG_MAX < 1 || DEG_MAX > MAXDEG || DIAM < 2 || DIAM > 12) {
        printf("0 0\n");
        return 0;
    }

    int n, m;
    if (scanf("%d %d", &n, &m) != 2) {
        printf("0 0\n");
        return 0;
    }
    if (n <= 0 || n > MAXN / 2 || m < 0 || m > MAXM) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int v = 0; v < N; v++) deg[v] = 0;
    int bad = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            bad = 1;
            break;
        }
        if (u < 0 || u >= N || v < 0 || v >= N || u == v || deg[u] >= DEG_MAX ||
            deg[v] >= DEG_MAX || has_edge(u, v)) {
            bad = 1;
            break;
        }
        add_edge(u, v);
        inU[inM] = u;
        inV[inM] = v;
        inM++;
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    /* 2-colour the start graph; reject if not bipartite. */
    static int q[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int x = q[qh++];
            for (int k = 0; k < deg[x]; k++) {
                int y = adj[x][k];
                if (col[y] == -1) {
                    col[y] = 1 - col[x];
                    q[qt++] = y;
                }
            }
        }
    }
    for (int i = 0; i < inM; i++)
        if (col[inU[i]] == col[inV[i]]) {
            printf("0 0\n");
            return 0;
        }
    if (!is_valid()) {
        printf("0 0\n");
        return 0;
    }

    double t0 = (double)clock() / CLOCKS_PER_SEC;
    while (1) {
        double el = (double)clock() / CLOCKS_PER_SEC - t0;
        if (el > tl) break;
        if (N >= MAXN - 2) break;

        uint64_t *b = reach(DIAM - 1);
        if (try_insert(0, 8, b) || try_insert(1, 8, b)) continue;

        double r = rnd01();
        if (r < 0.35) densify_one();
        else if (r < 0.65) remove_move();
        else switch_move();
    }

    if (!is_valid()) {
        printf("0 0\n");
        return 0;
    }
    print_graph();
    return 0;
}
"""


def _valid_or(best, n, e, d, D):
    """Return (n, e) if it is valid and larger than best, else best."""
    if n > best[0] and lib.is_valid(n, e, d, D):
        return (n, e)
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    # Algebraic starts.
    if D >= 3:
        arcs = _arc_extensions(d, t0 + 0.10 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            best = _valid_or(best, n_c, e_c, d, D)

    if D >= 4 and time.monotonic() < t0 + 0.20 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            best = _valid_or(best, gq[0], gq[1], d, D)

    # C search from the best start: insertion with ball-cover certificates plus
    # validity-checked local moves.
    if D >= 2 and d <= 64:
        remaining = time_limit - (time.monotonic() - t0)
        budget = remaining * 0.80 - 1.5
        if budget > 0.5:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                 stdin_graph=best, timeout=remaining - 1.0)
                n, e = lib.parse_graph_text(text)
                best = _valid_or(best, n, e, d, D)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
