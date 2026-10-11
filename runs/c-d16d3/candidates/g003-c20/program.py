"""Diameter-3 bipartite search: arc-extended projective plane starts plus a C engine.

Starts: arc-extended PG(2,q) incidence graphs (q + the arc / conic choice), the generalized
quadrangle for D >= 4, or K_{d,d}. The C engine keeps a valid graph with max degree d and
diameter <= D, and grows it by inserting vertex pairs (x on side 0, y on side 1). Each
insertion reuses spare capacity and/or removes matched edges, so degrees never exceed d.
Simulated annealing over degree-preserving edge swaps then removes the distance violations
(cost = number of pairs at distance > D). A failed insertion is rolled back to the last
valid graph. Python re-checks everything with lib.is_valid and keeps a valid fallback.
"""
import itertools
import random
import time

import lib

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define WORDS (MAXN / 64)
#define MAXDEG 64
#define PLAT 40
#define ITER 2500

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXDEG];
    int side[MAXN];
} Snap;

static int N, W, Dd, Dist;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static uint64_t bufA[MAXN][WORDS];
static uint64_t bufB[MAXN][WORDS];
static Snap base_s, best_s;
static int la, lb, lc, le;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int k = 0; k < deg[u]; k++)
        if (adj[u][k] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_arc(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adj[u][k] == v) {
            adj[u][k] = adj[u][--deg[u]];
            return;
        }
    }
}

static void del_edge(int u, int v) {
    del_arc(u, v);
    del_arc(v, u);
}

static int inlist(const int *L, int n, int x) {
    for (int i = 0; i < n; i++)
        if (L[i] == x) return 1;
    return 0;
}

/* Number of unordered pairs at distance > Dist (unreached pairs included). */
static long cost_of(void) {
    uint64_t (*cur)[WORDS] = bufA;
    uint64_t (*nxt)[WORDS] = bufB;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < W; i++) cur[v][i] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < Dist; r++) {
        for (int v = 0; v < N; v++) {
            for (int i = 0; i < W; i++) nxt[v][i] = cur[v][i];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int i = 0; i < W; i++) nxt[v][i] |= cur[u][i];
            }
        }
        uint64_t (*t)[WORDS] = cur;
        cur = nxt;
        nxt = t;
    }
    long unreached = 0;
    for (int v = 0; v < N; v++) {
        int cnt = 0;
        for (int i = 0; i < W; i++) cnt += popc(cur[v][i]);
        unreached += N - cnt;
    }
    return unreached / 2;
}

static void snap_save(Snap *s) {
    s->n = N;
    for (int v = 0; v < N; v++) {
        s->deg[v] = deg[v];
        s->side[v] = side[v];
        memcpy(s->adj[v], adj[v], sizeof(int) * MAXDEG);
    }
}

static void snap_load(const Snap *s) {
    N = s->n;
    W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        deg[v] = s->deg[v];
        side[v] = s->side[v];
        memcpy(adj[v], s->adj[v], sizeof(int) * MAXDEG);
    }
}

/* Degree-preserving swap: (a,b),(c,e) -> (a,e),(c,b) with a,c on the same side. */
static int swap_move(void) {
    if (N < 4) return 0;
    int a = rndint(N);
    if (deg[a] == 0) return 0;
    int c = -1;
    for (int t = 0; t < 30; t++) {
        int cc = rndint(N);
        if (cc != a && side[cc] == side[a] && deg[cc] > 0) {
            c = cc;
            break;
        }
    }
    if (c < 0) return 0;
    int b = adj[a][rndint(deg[a])];
    int e = adj[c][rndint(deg[c])];
    if (b == e) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    la = a; lb = b; lc = c; le = e;
    return 1;
}

static void undo_swap(void) {
    del_edge(la, le);
    del_edge(lc, lb);
    add_edge(la, lb);
    add_edge(lc, le);
}

/*
 * Insert a new pair x (side 0), y (side 1), each of degree Dd, without changing
 * any old degree. x takes s spare side-1 vertices and y takes the same number of
 * spare side-0 vertices; the remaining slots come from removing edges (a,b) and
 * attaching x to b and y to a. Returns 0 (and changes nothing) on failure.
 */
static int insert_pair(void) {
    if (N + 2 > MAXN - 4) return 0;
    static int spA[MAXN], spB[MAXN];
    int nA = 0, nB = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < Dd) {
            if (side[v] == 0) spA[nA++] = v;
            else spB[nB++] = v;
        }
    }
    for (int i = nA - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = spA[i]; spA[i] = spA[j]; spA[j] = t;
    }
    for (int i = nB - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = spB[i]; spB[i] = spB[j]; spB[j] = t;
    }
    int mx = nA < nB ? nA : nB;
    if (mx > Dd) mx = Dd;
    int s = mx;
    if (rnd01() < 0.5) s = rndint(mx + 1);

    int NX[MAXDEG], NY[MAXDEG], RA[MAXDEG], RB[MAXDEG];
    int nx = 0, ny = 0, nr = 0;
    for (int i = 0; i < s; i++) {
        NX[nx++] = spB[i];
        NY[ny++] = spA[i];
    }
    int tries = 0;
    while (nx < Dd && tries < 5000) {
        tries++;
        int u = rndint(N);
        if (deg[u] == 0) continue;
        int v = adj[u][rndint(deg[u])];
        int a = (side[u] == 0) ? u : v;
        int b = (side[u] == 0) ? v : u;
        if (inlist(NY, ny, a) || inlist(NX, nx, b)) continue;
        NX[nx++] = b;
        NY[ny++] = a;
        RA[nr] = a;
        RB[nr] = b;
        nr++;
    }
    if (nx < Dd) return 0;

    int x = N, y = N + 1;
    for (int i = 0; i < nr; i++) del_edge(RA[i], RB[i]);
    N += 2;
    W = (N + 63) / 64;
    side[x] = 0;
    side[y] = 1;
    deg[x] = 0;
    deg[y] = 0;
    for (int i = 0; i < nx; i++) add_edge(x, NX[i]);
    for (int i = 0; i < ny; i++) add_edge(y, NY[i]);
    return 1;
}

static void plateau(int steps, double t_end) {
    for (int i = 0; i < steps && elapsed() < t_end; i++) {
        if (!swap_move()) continue;
        if (cost_of() != 0) undo_swap();
    }
}

static long anneal(long cur, int iters, double T0, double t_end) {
    for (int it = 0; it < iters && cur > 0 && elapsed() < t_end; it++) {
        double T = T0 * (1.0 - (double)it / iters) + 0.05;
        if (!swap_move()) continue;
        long nc = cost_of();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = nc;
        else undo_swap();
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    if (Dd > MAXDEG) Dd = MAXDEG;
    if (Dd < 1) Dd = 1;
    Dist = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 4 || Dist < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= Dd || deg[v] >= Dd) continue;
        if (has_edge(u, v)) continue;
        add_edge(u, v);
    }

    for (int v = 0; v < N; v++) side[v] = -1;
    static int bq[MAXN];
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, t = 0;
        bq[t++] = s;
        while (head < t) {
            int u = bq[head++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    bq[t++] = v;
                }
            }
        }
    }
    W = (N + 63) / 64;

    double t_end = elapsed() + budget;
    snap_save(&best_s);
    long cur = cost_of();
    if (cur > 0) cur = anneal(cur, 300000, 1.0, t_end);

    if (cur == 0) {
        snap_save(&best_s);
        while (elapsed() < t_end && N < MAXN - 4) {
            plateau(PLAT, t_end);
            snap_save(&base_s);
            if (!insert_pair()) break;
            cur = cost_of();
            cur = anneal(cur, ITER, 1.5, t_end);
            if (cur == 0) {
                snap_save(&best_s);
            } else {
                snap_load(&base_s);
                cur = 0;
            }
        }
    }

    int bn = best_s.n;
    int M = 0;
    for (int v = 0; v < bn; v++)
        for (int k = 0; k < best_s.deg[v]; k++)
            if (best_s.adj[v][k] > v) M++;
    printf("%d %d\n", bn, M);
    for (int v = 0; v < bn; v++)
        for (int k = 0; k < best_s.deg[v]; k++)
            if (best_s.adj[v][k] > v) printf("%d %d\n", v, best_s.adj[v][k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has spare capacity s = d - q - 1. Choose a point set S that is an arc, so each
# line holds at most s points of S. Add an A-vertex per P in S (joined to the
# lines through P) and a B-vertex per j in S (joined to the points on line j).
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
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4), used for D >= 4.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 85% of time_limit."""
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d}: diameter 2 and optimal for D = 2 (bipartite Moore bound 2d).
    fallback = lib.haar_graph(d, range(d))
    if D == 2 or not lib.is_valid(fallback[0], fallback[1], d, D):
        return fallback
    rng = random.Random(seed * 7919 + d)

    starts = []
    if D >= 3:
        starts.extend(_arc_extensions(d, t0 + 0.15 * time_limit, rng))
    if D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)

    best = fallback
    for g in starts:
        if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = g

    # Already at the Moore bound: nothing to search for.
    if best[0] >= lib.moore_bound(d, D):
        return best

    # Search: C engine from the best start, using the remaining time (with margin).
    end_wall = t0 + 0.85 * time_limit
    budget = end_wall - time.monotonic() - 1.5
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                         stdin_graph=best, timeout=budget + 5.0)
        n1, e1 = lib.parse_graph_text(text)
        if n1 > best[0] and lib.is_valid(n1, e1, d, D):
            best = (n1, e1)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
