"""Diameter-3 bipartite search: arc-extended PG(2,q) and difference-cover starts,
then a C engine that grows the graph by ball-cover vertex insertion plus
simulated-annealing repair of bad pairs (degree-preserving edge switches).
"""
import math
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define WMAX 16
#define MAXD 64

typedef uint64_t u64;

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int color[MAXN];
} Graph;

static Graph G, BEST, START;
static int D = 3;
static int DEGMAX = 3;
static u64 rs = 88172645463325252ULL;
static double t_begin = 0.0, t_budget = 0.0;
static u64 RA[MAXN][WMAX], RB[MAXN][WMAX], BALL[MAXN][WMAX];

static u64 rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (u64)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_sec(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static int time_up(void) { return now_sec() - t_begin > t_budget; }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}
static void add_arc(Graph *g, int u, int v) { g->adj[u][g->deg[u]++] = v; }
static void del_arc(Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++) {
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][--g->deg[u]];
            return;
        }
    }
}
static void add_edge(Graph *g, int u, int v) { add_arc(g, u, v); add_arc(g, v, u); }
static void del_edge(Graph *g, int u, int v) { del_arc(g, u, v); del_arc(g, v, u); }

/* out[v] = bitset of vertices within distance R of v. */
static void compute_reach(const Graph *g, int R, u64 out[][WMAX]) {
    int n = g->n, w = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        for (int k = 0; k < w; k++) out[v][k] = 0;
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            for (int k = 0; k < w; k++) RB[v][k] = out[v][k];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                for (int k = 0; k < w; k++) RB[v][k] |= out[u][k];
            }
        }
        for (int v = 0; v < n; v++)
            for (int k = 0; k < w; k++) out[v][k] = RB[v][k];
    }
}

/* Number of unordered pairs at distance > D (unreachable counts). Zero means valid. */
static long bad_pairs(const Graph *g) {
    int n = g->n, w = (n + 63) / 64;
    long tot = 0;
    compute_reach(g, D, RA);
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int k = 0; k < w; k++) c += popc(RA[v][k]);
        tot += n - c;
    }
    return tot / 2;
}

/* Remove K random edges at vertices of colour 1-side, freeing capacity for insertion. */
static void free_slots(Graph *g, int side, int K) {
    int n = g->n, done = 0;
    for (int tries = 0; done < K && tries < 50 * K + 50; tries++) {
        int x = rndint(n);
        if (g->color[x] != 1 - side || g->deg[x] == 0) continue;
        int y = g->adj[x][rndint(g->deg[x])];
        del_edge(g, x, y);
        done++;
    }
}

static int count_cands(const Graph *g, int side) {
    int c = 0;
    for (int v = 0; v < g->n; v++)
        if (g->color[v] == 1 - side && g->deg[v] < DEGMAX) c++;
    return c;
}

/* Insert a vertex on `side`, joined greedily to spare vertices of the other side
   so that its radius-(D-1) balls cover as much as possible. Cover need not be complete:
   annealing repairs the rest. */
static void insert_vertex(Graph *g, int side) {
    if (g->n >= MAXN) return;
    if (count_cands(g, side) < 2 || rnd01() < 0.3)
        free_slots(g, side, 1 + rndint(DEGMAX / 2 + 1));
    int n = g->n;
    int w = (n + 63) / 64;
    compute_reach(g, D - 1, BALL);
    u64 cov[WMAX];
    for (int k = 0; k < w; k++) cov[k] = 0;
    char used[MAXN];
    memset(used, 0, sizeof(used));
    int chosen[MAXD];
    int nc = 0;
    while (nc < DEGMAX) {
        int best = -1;
        double bs = -1.0;
        for (int v = 0; v < n; v++) {
            if (used[v] || g->color[v] != 1 - side || g->deg[v] >= DEGMAX) continue;
            int gain = 0;
            for (int k = 0; k < w; k++) gain += popc(BALL[v][k] & ~cov[k]);
            if (gain == 0) continue;
            double sc = gain + 0.9 * rnd01();
            if (sc > bs) {
                bs = sc;
                best = v;
            }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nc++] = best;
        for (int k = 0; k < w; k++) cov[k] |= BALL[best][k];
    }
    if (nc == 0) return;
    int x = n;
    g->n = n + 1;
    g->deg[x] = 0;
    g->color[x] = side;
    for (int i = 0; i < nc; i++) add_edge(g, x, chosen[i]);
}

/* Degree-preserving switch: (a,b),(c,e) -> (a,e),(c,b), with a,c on one side. */
static int move_switch(Graph *g, int *A) {
    int n = g->n, a = -1;
    for (int t = 0; t < 100; t++) {
        int x = rndint(n);
        if (g->deg[x] > 0) {
            a = x;
            break;
        }
    }
    if (a < 0) return 0;
    int b = g->adj[a][rndint(g->deg[a])];
    int c = -1;
    for (int t = 0; t < 100; t++) {
        int x = rndint(n);
        if (x != a && g->color[x] == g->color[a] && g->deg[x] > 0) {
            c = x;
            break;
        }
    }
    if (c < 0) return 0;
    int e = g->adj[c][rndint(g->deg[c])];
    if (e == b || has_edge(g, a, e) || has_edge(g, c, b)) return 0;
    del_edge(g, a, b);
    del_edge(g, c, e);
    add_edge(g, a, e);
    add_edge(g, c, b);
    A[0] = a; A[1] = b; A[2] = c; A[3] = e;
    return 1;
}
static void undo_switch(Graph *g, int *A) {
    del_edge(g, A[0], A[3]);
    del_edge(g, A[2], A[1]);
    add_edge(g, A[0], A[1]);
    add_edge(g, A[2], A[3]);
}

/* Add an edge between spare vertices of opposite colours (never increases distances). */
static int move_spare(Graph *g, int *A) {
    int n = g->n;
    for (int t = 0; t < 50; t++) {
        int a = rndint(n), b = rndint(n);
        if (a == b || g->color[a] == g->color[b]) continue;
        if (g->deg[a] >= DEGMAX || g->deg[b] >= DEGMAX) continue;
        if (has_edge(g, a, b)) continue;
        add_edge(g, a, b);
        A[0] = a; A[1] = b;
        return 1;
    }
    return 0;
}

/* Delete a random edge (allows the search to leave local minima). */
static int move_remove(Graph *g, int *A) {
    int n = g->n;
    int a = rndint(n);
    if (g->deg[a] == 0) return 0;
    int b = g->adj[a][rndint(g->deg[a])];
    del_edge(g, a, b);
    A[0] = a; A[1] = b;
    return 1;
}

/* Simulated annealing on the bad-pair count. Returns 1 if it reaches a valid graph. */
static int anneal(Graph *g, int iters, double T0, double T1) {
    long cost = bad_pairs(g);
    int A[4];
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 31) == 0 && time_up()) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        double r = rnd01();
        int kind, ok;
        if (r < 0.65) {
            kind = 0;
            ok = move_switch(g, A);
        } else if (r < 0.95) {
            kind = 1;
            ok = move_spare(g, A);
        } else {
            kind = 2;
            ok = move_remove(g, A);
        }
        if (!ok) continue;
        long nc = bad_pairs(g);
        long delta = nc - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cost = nc;
        } else {
            if (kind == 0) undo_switch(g, A);
            else if (kind == 1) del_edge(g, A[0], A[1]);
            else add_edge(g, A[0], A[1]);
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    D = atoi(argv[2]);
    u64 seed = (u64)strtoull(argv[3], NULL, 10);
    t_budget = atof(argv[4]);
    t_begin = now_sec();
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || n0 > MAXN || m0 < 0 ||
        d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    DEGMAX = d;
    memset(&START, 0, sizeof(START));
    START.n = n0;
    int ok = 1;
    for (int i = 0; i < m0 && ok; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { ok = 0; break; }
        if (START.deg[u] >= d || START.deg[v] >= d || has_edge(&START, u, v)) { ok = 0; break; }
        add_edge(&START, u, v);
    }
    if (ok) {
        static int queue[MAXN];
        for (int i = 0; i < n0; i++) START.color[i] = -1;
        for (int s = 0; s < n0; s++) {
            if (START.color[s] >= 0) continue;
            START.color[s] = 0;
            int qh = 0, qt = 0;
            queue[qt++] = s;
            while (qh < qt) {
                int x = queue[qh++];
                for (int i = 0; i < START.deg[x]; i++) {
                    int y = START.adj[x][i];
                    if (START.color[y] < 0) {
                        START.color[y] = 1 - START.color[x];
                        queue[qt++] = y;
                    }
                }
            }
        }
        for (int u = 0; u < n0; u++)
            for (int i = 0; i < START.deg[u]; i++)
                if (START.color[START.adj[u][i]] == START.color[u]) ok = 0;
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    G = START;
    int have = 0;
    if (bad_pairs(&G) == 0) have = 1;
    else if (anneal(&G, 200000, 0.6, 0.03)) have = 1;
    if (have) BEST = G;

    while (have && !time_up()) {
        G = BEST;
        int before = G.n;
        insert_vertex(&G, rndint(2));
        if (G.n == before) continue;
        if (anneal(&G, 6000, 0.8, 0.03)) BEST = G;
    }

    const Graph *out = have ? &BEST : &START;
    int n = out->n;
    long m = 0;
    for (int u = 0; u < n; u++)
        for (int i = 0; i < out->deg[u]; i++)
            if (out->adj[u][i] > u) m++;
    printf("%d %ld\n", n, m);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < out->deg[u]; i++) {
            int v = out->adj[u][i];
            if (v > u) printf("%d %d\n", u, v);
        }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S such
# that every line holds <= s points of S and every point lies on <= s lines
# indexed by S. For each P in S add a new A-vertex on the q+1 lines through P;
# for each j in S add a new B-vertex on the q+1 points of line j.
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
    for t, j in enumerate(S):  # S is also a set of line indices (same vectors)
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
# Cyclic Haar graphs from difference covers (diameter 3).
#
# For a k-subset S of Z_m, H(m, S) joins a_i to b_{i+s} for s in S. If every
# nonzero residue is a difference of two elements of S, all A-A pairs are within
# distance 2, and S-S+S = Z_m gives A-B distance <= 3. Simulated annealing finds
# covers of size k = d with m as large as possible.
# ----------------------------------------------------------------------------

def _diff_counts(S, m):
    """Return (cnt, zeros): cnt[x] = #ordered pairs (s,t), s != t, with s - t = x mod m."""
    cnt = [0] * m
    k = len(S)
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    zeros = sum(1 for x in range(1, m) if cnt[x] == 0)
    return cnt, zeros


def _move(S, cnt, i, y, m, zeros):
    """Replace S[i] by y (y not in S), updating cnt and the zero count. Returns the new zero count."""
    k = len(S)
    old = S[i]
    for j in range(k):
        if j != i:
            t = S[j]
            a = (old - t) % m
            b = (t - old) % m
            cnt[a] -= 1
            if cnt[a] == 0:
                zeros += 1
            cnt[b] -= 1
            if cnt[b] == 0:
                zeros += 1
    S[i] = y
    for j in range(k):
        if j != i:
            t = S[j]
            a = (y - t) % m
            b = (t - y) % m
            if cnt[a] == 0:
                zeros -= 1
            cnt[a] += 1
            if cnt[b] == 0:
                zeros -= 1
            cnt[b] += 1
    return zeros


def _cover_search(k, m, deadline, rng):
    """Find a k-subset S of Z_m whose nonzero differences cover Z_m \\ {0}; return sorted S or None."""
    if k > m or k * (k - 1) + 1 < m:
        return None
    S = rng.sample(range(m), k)
    cnt, zeros = _diff_counts(S, m)
    T = 0.3
    moves = 0
    while zeros > 0:
        moves += 1
        if moves % 512 == 0 and time.monotonic() > deadline:
            return None
        if moves % 200000 == 0:
            S = rng.sample(range(m), k)
            cnt, zeros = _diff_counts(S, m)
            continue
        i = rng.randrange(k)
        y = rng.randrange(m)
        if y in S:
            continue
        old = S[i]
        z = _move(S, cnt, i, y, m, zeros)
        delta = z - zeros
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            zeros = z
        else:
            _move(S, cnt, i, old, m, z)
    return sorted(S)


def _difference_graph(d, deadline, rng):
    """Largest cyclic Haar graph H(m, S) with |S| = d found before the deadline, as (n, edges), or None."""
    k = d
    cap = k * (k - 1) + 1
    if k < 2 or cap < 3:
        return None
    best_m, best_S = 0, None
    cur = max(k + 1, int(0.8 * cap))
    fails = 0
    while time.monotonic() < deadline and cur <= cap:
        now = time.monotonic()
        slice_end = min(deadline, now + max(1.0, 0.35 * (deadline - now)))
        S = _cover_search(k, cur, slice_end, rng)
        if S is not None:
            best_m, best_S = cur, S
            cur += 1
            fails = 0
        else:
            fails += 1
            if best_S is None:
                cur = max(k + 1, cur - 3)
            elif fails >= 3:
                break
    if best_S is None:
        return None
    return lib.haar_graph(best_m, best_S)


# ----------------------------------------------------------------------------
# Driver. Every D >= 3 case: best of the arc-extended and difference-cover starts,
# then the C engine grows it from there. Moore-bound graphs return immediately.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
    arcs.sort(key=lambda t: -t[0])
    for n_c, e_c in arcs[:3]:
        consider(n_c, e_c)

    if D == 3:
        hg = _difference_graph(d, start + 0.30 * time_limit, rng)
        if hg is not None:
            consider(hg[0], hg[1])

    if best[0] >= lib.moore_bound(d, D):
        return best

    stage_end = start + 0.90 * time_limit
    budget = stage_end - time.monotonic() - 2.5  # room for C compilation and I/O
    if budget >= 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 2.0)
            n2, e2 = lib.parse_graph_text(text)
            consider(n2, e2)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
