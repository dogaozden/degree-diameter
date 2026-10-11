import itertools
import random
import time

import lib

MAX_C_N = 1000  # the C engine supports up to 1100 vertices; keep a margin

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXDEG 48
#define MAXW ((MAXN + 63) / 64)
#define T0 3.0
#define TFLOOR 0.25
#define TSCALE 4000.0
#define RESET_EVERY 20000

/* Simulated annealing that grows a valid bipartite graph of max degree DEG_MAX
   and diameter DIAM. Cost = number of ordered vertex pairs at distance > DIAM.
   Moves: rewire one endpoint of an edge (keeping degrees <= DEG_MAX), then
   greedily refill the freed slot. When cost reaches 0, a new vertex is inserted. */

static int N = 0;
static int DEG_MAX = 0;
static int DIAM = 0;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static uint64_t bufA[MAXN][MAXW];
static uint64_t bufB[MAXN][MAXW];
static int cand[MAXN];
static int bestN = -1;
static int bestDeg[MAXN];
static int bestAdj[MAXN][MAXDEG];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adj[a][i] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void del_half(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a][i] == b) {
            adj[a][i] = adj[a][--deg[a]];
            return;
        }
    }
}

static void del_edge(int a, int b) {
    del_half(a, b);
    del_half(b, a);
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long cost(void) {
    int words = (N + 63) >> 6;
    uint64_t (*cur)[MAXW] = bufA;
    uint64_t (*nxt)[MAXW] = bufB;
    for (int v = 0; v < N; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * (size_t)words);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * (size_t)words);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = cur[adj[v][i]];
                for (int w = 0; w < words; w++) nxt[v][w] |= src[w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < words; w++) c += popc64(cur[v][w]);
        bad += N - c;
    }
    return bad;
}

static void save_best(void) {
    bestN = N;
    for (int v = 0; v < N; v++) {
        bestDeg[v] = deg[v];
        memcpy(bestAdj[v], adj[v], sizeof(int) * (size_t)deg[v]);
    }
}

/* Add one random edge from b to a spare vertex on the opposite side. */
static int fill_vertex(int b) {
    if (deg[b] >= DEG_MAX) return -1;
    int start = rndint(N);
    for (int k = 0; k < N; k++) {
        int e = start + k;
        if (e >= N) e -= N;
        if (side[e] != side[b] && deg[e] < DEG_MAX && !has_edge(b, e)) {
            add_edge(b, e);
            return e;
        }
    }
    return -1;
}

static void fill_all(void) {
    for (int v = 0; v < N; v++) {
        while (deg[v] < DEG_MAX && fill_vertex(v) >= 0) {
        }
    }
}

static int gather(int s) {
    int nc = 0;
    for (int v = 0; v < N; v++)
        if (side[v] != s && deg[v] < DEG_MAX) cand[nc++] = v;
    return nc;
}

/* Insert a new vertex on a random side, joined to spare vertices of the other side. */
static int insert_vertex(void) {
    if (N >= MAXN - 1) return 0;
    int s = rndint(2);
    int nc = gather(s);
    if (nc == 0) {
        s ^= 1;
        nc = gather(s);
    }
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    int x = N;
    N++;
    deg[x] = 0;
    side[x] = s;
    int k = nc < DEG_MAX ? nc : DEG_MAX;
    for (int i = 0; i < k; i++) add_edge(x, cand[i]);
    return 1;
}

static int read_input(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN || m < 0) return 0;
    N = n;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) return 0;
        if (deg[u] >= DEG_MAX || deg[v] >= DEG_MAX) return 0;
        if (has_edge(u, v)) return 0;
        add_edge(u, v);
    }
    static int col[MAXN];
    static int stk[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        int sp = 0;
        col[s] = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[u][i];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    stk[sp++] = w;
                } else if (col[w] == col[u]) {
                    return 0;
                }
            }
        }
    }
    for (int v = 0; v < N; v++) side[v] = col[v];
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG_MAX = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    if (DEG_MAX < 1 || DEG_MAX > MAXDEG || DIAM < 1 || !read_input()) {
        printf("0 0\n");
        return 0;
    }

    double tend = now_sec() + budget;
    long long C = cost();
    if (C == 0 && N > bestN) save_best();
    fill_all();
    C = cost();
    if (C == 0 && N > bestN) save_best();

    double T = T0;
    long long since = 0;
    while (now_sec() < tend) {
        if (C == 0) {
            if (N > bestN) save_best();
            if (!insert_vertex()) break;
            fill_all();
            C = cost();
            T = T0;
            since = 0;
            continue;
        }
        since++;
        if (since > RESET_EVERY) since = 0;
        T = T0 * exp(-(double)since / TSCALE);
        if (T < TFLOOR) T = TFLOOR;

        int a = rndint(N);
        if (deg[a] == 0) continue;
        int b = adj[a][rndint(deg[a])];
        int c = -1;
        for (int tr = 0; tr < 200 && c < 0; tr++) {
            int x = rndint(N);
            if (side[x] != side[a] && x != b && deg[x] < DEG_MAX && !has_edge(a, x)) c = x;
        }
        if (c < 0) continue;

        del_edge(a, b);
        add_edge(a, c);
        int e = fill_vertex(b);
        long long C2 = cost();
        double dl = (double)(C2 - C);
        if (dl <= 0.0 || rnd01() < exp(-dl / T)) {
            C = C2;
        } else {
            if (e >= 0) del_edge(b, e);
            del_edge(a, c);
            add_edge(a, b);
        }
    }
    if (C == 0 && N > bestN) save_best();

    if (bestN < 0) {
        printf("0 0\n");
        return 0;
    }
    long long m2 = 0;
    for (int v = 0; v < bestN; v++) m2 += bestDeg[v];
    printf("%d %lld\n", bestN, m2 / 2);
    for (int u = 0; u < bestN; u++)
        for (int i = 0; i < bestDeg[u]; i++)
            if (bestAdj[u][i] > u) printf("%d %d\n", u, bestAdj[u][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Incidence data for PG(2, q): point_lines, line_points (both over 0..m-1), edges, index, pts."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _load_ok(S, s, inc, m):
    """True if every partner y is incident with at most s elements of S (inc[x] lists partners of x)."""
    load = [0] * m
    for x in S:
        for y in inc[x]:
            load[y] += 1
            if load[y] > s:
                return False
    return True


def _greedy(s, inc, m, rng, trials, deadline):
    """Randomized greedy: largest set found where every partner is hit at most s times."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            ys = inc[x]
            if all(load[y] < s for y in ys):
                S.append(x)
                for y in ys:
                    load[y] += 1
        if len(S) > len(best):
            best = S
    return best


def _best_arc(inc, m, s, rng, deadline, conic):
    """Best of greedy and the conic (if it is valid for this load) for one side."""
    cands = []
    if s >= 1:
        cands.append(_greedy(s, inc, m, rng, 30, deadline))
    if conic is not None and _load_ok(conic, s, inc, m):
        cands.append(conic)
    return max(cands, key=len, default=[])


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG(2,q) incidence plus new point-class vertices (one per SA point, joined to its lines)
    and new line-class vertices (one per SB line, joined to its points). Diameter 3, degree q+1+load."""
    E = list(edges)
    n = 2 * m
    for P in SA:
        for L in point_lines[P]:
            E.append((n, m + L))
        n += 1
    for j in SB:
        for Q in line_points[j]:
            E.append((Q, n))
        n += 1
    return n, E


def _arc_candidates(d, deadline, rng):
    """For each prime power q with q+1 <= d, build the arc-extended incidence graph with spare s = d-q-1.
    The A-side set (points) and B-side set (lines) are chosen independently."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q) or time.monotonic() > deadline:
            continue
        s = d - q - 1
        if s < 0:
            continue
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        conic = None
        if s >= 2:
            F = lib.GF(q)
            conic = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
            if q % 2 == 0:
                conic.append(index[(0, 1, 0)])
        SA = _best_arc(point_lines, m, s, rng, deadline, conic)
        SB = _best_arc(line_points, m, s, rng, deadline, conic)
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
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
    """W(q) for the largest prime power q with q + 1 <= d (q <= 9 for speed)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.7 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = (1, [])

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Safe fallback: K_{d,d} has diameter 2.
    consider(lib.haar_graph(d, range(d)))
    if best[0] >= lib.moore_bound(d, D):
        return best

    # Diameter 3: arc-extended projective plane incidence graphs.
    if D >= 3:
        for cand in _arc_candidates(d, t0 + 0.15 * time_limit, rng):
            consider(cand)
        if best[0] >= lib.moore_bound(d, D):
            return best

    # Diameter 4: generalized quadrangle incidence graph.
    if D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
        consider(_best_gq(d))
        if best[0] >= lib.moore_bound(d, D):
            return best

    # Bold step: let the C engine grow the best valid start by inserting vertices
    # into spare degree and annealing away diameter violations.
    if 1 < best[0] <= MAX_C_N:
        remaining = deadline - time.monotonic()
        if remaining > 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                                stdin_graph=best, timeout=remaining + 10.0)
                n, e = lib.parse_graph_text(out)
                consider((n, e))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
