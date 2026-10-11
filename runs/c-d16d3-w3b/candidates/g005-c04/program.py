import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset-based local search that grows a bipartite graph by one
# vertex at a time. Each step removes or adds cross edges (only between the two
# colour classes, so the graph stays bipartite) and minimises the number of
# vertex pairs at distance greater than D. Degrees never exceed d. A graph is
# output only when its cost is exactly zero, so the output is always valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 2048
#define MAXW 32
#define MAXD 64

typedef uint64_t u64;

static int d, D, N;
static unsigned char A[MAXN][MAXN];
static int deg[MAXN];
static int adjl[MAXN][MAXD];
static int side[MAXN];
static u64 BA[MAXN][MAXW], BB[MAXN][MAXW];
static u64 (*RP)[MAXW], (*RQ)[MAXW];
static uint64_t rng_state = 88172645463325252ULL;

static int bn = 0, bm = 0;
static int bedge[MAXN * MAXD][2];

static double now_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static uint64_t rnd64(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rnd(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int u, int v) {
    A[u][v] = 1;
    A[v][u] = 1;
    adjl[u][deg[u]++] = v;
    adjl[v][deg[v]++] = u;
}

static void del_from(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adjl[u][k] == v) {
            adjl[u][k] = adjl[u][--deg[u]];
            return;
        }
    }
}

static void remove_edge(int u, int v) {
    A[u][v] = 0;
    A[v][u] = 0;
    del_from(u, v);
    del_from(v, u);
}

/* Number of ordered pairs (s, t) with dist(s, t) > D (each unordered pair counted twice). */
static long long cost_eval(void) {
    int W = (N + 63) >> 6;
    RP = BA;
    RQ = BB;
    for (int v = 0; v < N; v++) {
        memset(RP[v], 0, sizeof(u64) * (size_t)W);
        RP[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < D; s++) {
        for (int v = 0; v < N; v++) {
            u64 *out = RQ[v];
            memcpy(out, RP[v], sizeof(u64) * (size_t)W);
            for (int k = 0; k < deg[v]; k++) {
                const u64 *in = RP[adjl[v][k]];
                for (int w = 0; w < W; w++) out[w] |= in[w];
            }
        }
        u64 (*t)[MAXW] = RP;
        RP = RQ;
        RQ = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(RP[v][w]);
        bad += N - c;
    }
    return bad;
}

static void save_best(void) {
    bn = N;
    bm = 0;
    for (int u = 0; u < N; u++) {
        for (int k = 0; k < deg[u]; k++) {
            int v = adjl[u][k];
            if (u < v) {
                bedge[bm][0] = u;
                bedge[bm][1] = v;
                bm++;
            }
        }
    }
}

static void load_best(void) {
    for (int u = 0; u < N; u++) {
        memset(A[u], 0, (size_t)N);
        deg[u] = 0;
    }
    N = bn;
    for (int i = 0; i < bm; i++) add_edge(bedge[i][0], bedge[i][1]);
}

/* Try to reach cost 0 at the current N. Returns 1 on success (graph is valid). */
static int grow_attempt(double secs, double T0, double T1, double global_end) {
    double t0 = now_s();
    long long cur = cost_eval();
    if (cur == 0) return 1;
    static int L0[MAXN], L1[MAXN];
    for (long long it = 0;; it++) {
        double t = now_s();
        if (t - t0 >= secs || t >= global_end) break;
        double frac = (t - t0) / secs;
        if (frac < 0) frac = 0;
        double T = T0 * pow(T1 / T0, frac);

        int use_add = (rnd01() < 0.3);
        int a = -1, b = -1, x = -1, y = -1;
        int removed = 0;
        if (!use_add) {
            int u = -1;
            for (int tries = 0; tries < 20; tries++) {
                int c = rnd(N);
                if (deg[c] > 0) {
                    u = c;
                    break;
                }
            }
            if (u < 0) continue;
            int v = adjl[u][rnd(deg[u])];
            if (side[u] == 0) {
                a = u;
                b = v;
            } else {
                a = v;
                b = u;
            }
            remove_edge(a, b);
            removed = 1;
        }

        int n0c = 0, n1c = 0;
        for (int v = 0; v < N; v++) {
            if (deg[v] < d) {
                if (side[v] == 0) L0[n0c++] = v;
                else L1[n1c++] = v;
            }
        }
        int found = 0;
        if (n0c > 0 && n1c > 0) {
            for (int tries = 0; tries < 30 && !found; tries++) {
                int xx = L0[rnd(n0c)];
                int yy = L1[rnd(n1c)];
                if (A[xx][yy]) continue;
                if (removed && xx == a && yy == b) continue;
                x = xx;
                y = yy;
                found = 1;
            }
        }
        if (!found) {
            if (removed) add_edge(a, b);
            continue;
        }

        add_edge(x, y);
        long long c2 = cost_eval();
        long long delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = c2;
            if (cur == 0) return 1;
        } else {
            remove_edge(x, y);
            if (removed) add_edge(a, b);
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rng_state = 0x9E3779B97F4A7C15ULL ^ ((uint64_t)strtoull(argv[3], NULL, 10) * 0xBF58476D1CE4E5B9ULL);
    if (rng_state == 0) rng_state = 1;
    double tl = atof(argv[4]);
    double end = now_s() + tl;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        printf("0 0\n");
        return 0;
    }
    if (n < 2 || n > MAXN - 64 || d < 1 || d > MAXD || D < 1 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || A[u][v] || deg[u] >= d || deg[v] >= d) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    /* Bipartition by BFS; reject non-bipartite input. */
    for (int i = 0; i < N; i++) side[i] = -1;
    static int queue[MAXN];
    for (int s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int h = 0, t = 0;
        queue[t++] = s;
        while (h < t) {
            int u = queue[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adjl[u][k];
                if (side[v] == -1) {
                    side[v] = 1 - side[u];
                    queue[t++] = v;
                } else if (side[v] == side[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    if (cost_eval() != 0) {
        printf("0 0\n");
        return 0;
    }
    save_best();

    double attempt = tl * 0.05;
    if (attempt < 1.0) attempt = 1.0;
    while (now_s() < end - 0.2 && N < MAXN - 1) {
        int s = rnd(2);
        side[N] = s;
        deg[N] = 0;
        for (int v = 0; v < N; v++) {
            A[v][N] = 0;
            A[N][v] = 0;
        }
        N++;
        if (grow_attempt(attempt, 1.5, 0.05, end - 0.2)) save_best();
        else load_best();
    }

    printf("%d %d\n", bn, bm);
    for (int i = 0; i < bm; i++) printf("%d %d\n", bedge[i][0], bedge[i][1]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. For a point set S with
# every line holding <= s points of S and every point on <= s lines of S, add
# an A-vertex per point of S (joined to its q+1 lines) and a B-vertex per line
# of S (joined to its q+1 points). Diameter stays 3.
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
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, S, line_points)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Spare-capacity fill (diameter 3), checked exactly with lib.is_valid.
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
                g = sum(1 for u in adj[v] if u in uncovered)
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
# Driver: best construction, then C local search that tries to add vertices.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard_end = start + 0.75 * time_limit
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

    # Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        cands = _arc_extensions(d, start + 0.2 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

    # Plain greedy fill of the best graph so far.
    if D >= 3 and best_n > 2:
        n_f, e_f = _fill(best_n, best[1], d, D, start + 0.3 * time_limit,
                         random.Random(seed * 104729 + d))
        consider(n_f, e_f)

    # Generalized quadrangle baseline (diameter 4).
    if D >= 4 and time.monotonic() < start + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # C local search: grow the best valid graph by single vertices.
    remaining = hard_end - time.monotonic()
    if D >= 3 and remaining > 3.0:
        budget = hard_end - time.monotonic()
        timeout = start + 0.9 * time_limit - time.monotonic()
        if timeout > 2.0 and budget > 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=best, timeout=timeout)
                n_c, e_c = lib.parse_graph_text(out)
                consider(n_c, e_c)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
