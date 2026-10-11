"""Diameter-3 bipartite search: arc-extended projective plane starts plus a C annealing engine.

Starts are valid graphs: the arc-extended PG(2,q) incidence graph, the generalized quadrangle
W(q) for D >= 4, or K_{d,d}. The C engine keeps a fixed bipartition and works on a
bad-pair cost (the number of vertex pairs at distance > D). Its moves are:

  * degree-stealing insertion: add a vertex on one side, joined to a greedy cover T of the
    other side. A full vertex in T gives up one random edge, so the insertion is possible
    even without spare capacity. The stolen edge leaves a spare slot behind.
  * spare-spare edge fill: join non-adjacent spare vertices on opposite sides. This never
    raises the cost.
  * double-edge swaps (a,b),(c,d) -> (a,d),(c,b): degrees and bipartiteness are preserved,
    and the swap is accepted by simulated annealing on the cost.

Whenever the cost reaches 0 the graph is a valid snapshot, and the engine grows it by one
vertex. If annealing fails, it restores the last valid snapshot and tries again. Python
re-checks everything with lib.is_valid.
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

#define MAXN 2048
#define WORDS (MAXN / 64)
#define MAXDEG 64
#define LEN 30000
#define TEMP_HI 2.0
#define TEMP_LO 0.2

typedef uint64_t row_t[WORDS];

static int N, W, Dd, Dist;
static int deg[MAXN], side[MAXN], bq[MAXN];
static int adj[MAXN][MAXDEG];
static row_t BUF_A[MAXN], BUF_B[MAXN], RCH[MAXN], BALL[MAXN];
static int snapN = 0, hasSnap = 0;
static int snapDeg[MAXN], snapSide[MAXN], snapAdj[MAXN][MAXDEG];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double uni(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

/* Remove adj[v][idx] and the matching reverse entry. */
static void del_at(int v, int idx) {
    int u = adj[v][idx];
    adj[v][idx] = adj[v][--deg[v]];
    for (int k = 0; k < deg[u]; k++) {
        if (adj[u][k] == v) {
            adj[u][k] = adj[u][--deg[u]];
            break;
        }
    }
}

static void del_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adj[a][k] == b) {
            del_at(a, k);
            return;
        }
    }
}

/* res[v] = bitset of all vertices within distance r of v. */
static void reach(int r, row_t *res) {
    row_t *cur = BUF_A, *nxt = BUF_B;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < W; i++) cur[v][i] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < N; v++) {
            for (int i = 0; i < W; i++) nxt[v][i] = cur[v][i];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = cur[adj[v][k]];
                for (int i = 0; i < W; i++) nxt[v][i] |= src[i];
            }
        }
        row_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    for (int v = 0; v < N; v++)
        for (int i = 0; i < W; i++) res[v][i] = cur[v][i];
}

/* Number of unordered pairs at distance > Dist (unreachable pairs included). */
static int cost_now(void) {
    reach(Dist, RCH);
    long un = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int i = 0; i < W; i++) c += popc(RCH[v][i]);
        un += N - c;
    }
    return (int)(un / 2);
}

static void save_snap(void) {
    snapN = N;
    memcpy(snapDeg, deg, sizeof(deg));
    memcpy(snapSide, side, sizeof(side));
    memcpy(snapAdj, adj, sizeof(adj));
    hasSnap = 1;
}

static void load_snap(void) {
    N = snapN;
    W = (N + 63) / 64;
    memcpy(deg, snapDeg, sizeof(deg));
    memcpy(side, snapSide, sizeof(side));
    memcpy(adj, snapAdj, sizeof(adj));
}

/* Greedy cover T (on side 1-X) for a new vertex on side X. Gain counts vertices within
   distance Dist-1 of a candidate. Full candidates are allowed; they lose an edge later. */
static int choose_T(int X, int *T) {
    row_t U;
    static char used[MAXN];
    reach(Dist - 1, BALL);
    for (int i = 0; i < W; i++) U[i] = ~0ULL;
    if (N & 63) U[W - 1] = (1ULL << (N & 63)) - 1ULL;
    memset(used, 0, sizeof(used));
    int nt = 0;
    while (nt < Dd) {
        int best = -1;
        long bsc = -1;
        for (int v = 0; v < N; v++) {
            if (side[v] == X || used[v]) continue;
            int g = 0;
            for (int i = 0; i < W; i++) g += popc(BALL[v][i] & U[i]);
            if (g <= 0) continue;
            long sc = (long)g * 16 + (deg[v] < Dd ? 8 : 0) + rndint(8);
            if (sc > bsc) {
                bsc = sc;
                best = v;
            }
        }
        if (best < 0) break;
        used[best] = 1;
        T[nt++] = best;
        for (int i = 0; i < W; i++) U[i] &= ~BALL[best][i];
    }
    return nt;
}

/* Add vertex N on side X joined to T. A full t first drops one random edge (degree stealing). */
static void add_vertex(int X, const int *T, int nt) {
    int x = N;
    side[x] = X;
    deg[x] = 0;
    N++;
    W = (N + 63) / 64;
    for (int k = 0; k < nt; k++) {
        int t = T[k];
        if (deg[t] >= Dd) del_at(t, rndint(deg[t]));
        add_edge(x, t);
    }
}

static int grow(void) {
    if (N >= MAXN - 2) return 0;
    int X = rndint(2);
    int T[MAXDEG];
    int nt = choose_T(X, T);
    if (nt == 0) {
        X = 1 - X;
        nt = choose_T(X, T);
    }
    if (nt == 0) return 0;
    add_vertex(X, T, nt);
    return 1;
}

/* Join a spare vertex on side 0 to a non-adjacent spare vertex on side 1. Never raises cost. */
static int spare_fill_once(int exhaustive) {
    static int S0[MAXN], S1[MAXN];
    int n0 = 0, n1 = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] >= Dd) continue;
        if (side[v] == 0) S0[n0++] = v;
        else S1[n1++] = v;
    }
    if (!n0 || !n1) return 0;
    if (exhaustive) {
        for (int i = 0; i < n0; i++)
            for (int j = 0; j < n1; j++)
                if (!has_edge(S0[i], S1[j])) {
                    add_edge(S0[i], S1[j]);
                    return 1;
                }
        return 0;
    }
    for (int t = 0; t < 64; t++) {
        int a = S0[rndint(n0)], b = S1[rndint(n1)];
        if (!has_edge(a, b)) {
            add_edge(a, b);
            return 1;
        }
    }
    return 0;
}

static int pick_nb(int s0, int *a, int *b) {
    for (int t = 0; t < 200; t++) {
        int v = rndint(N);
        if (side[v] != s0 || deg[v] == 0) continue;
        *a = v;
        *b = adj[v][rndint(deg[v])];
        return 1;
    }
    return 0;
}

/* Double-edge swap (a,b),(c,d) -> (a,d),(c,b). a,c on side 0; b,d on side 1. */
static int swap_try(int *q) {
    int a, b, c, d;
    if (!pick_nb(0, &a, &b) || !pick_nb(0, &c, &d)) return 0;
    if (a == c || b == d || has_edge(a, d) || has_edge(c, b)) return 0;
    del_edge(a, b);
    del_edge(c, d);
    add_edge(a, d);
    add_edge(c, b);
    q[0] = a;
    q[1] = b;
    q[2] = c;
    q[3] = d;
    return 1;
}

static void swap_undo(const int *q) {
    int a = q[0], b = q[1], c = q[2], d = q[3];
    del_edge(a, d);
    del_edge(c, b);
    add_edge(a, b);
    add_edge(c, d);
}

/* Simulated annealing on the bad-pair cost. Returns 1 when cost reaches 0. */
static int anneal(int L, int *curp, double t_end) {
    int cur = *curp;
    for (int it = 0; it < L; it++) {
        if ((it & 63) == 0 && now_s() >= t_end) break;
        if (it % 100 == 0) {
            int f = 0;
            while (spare_fill_once(1)) f = 1;
            if (f) {
                cur = cost_now();
                if (cur == 0) {
                    *curp = 0;
                    return 1;
                }
            }
        }
        double temp = TEMP_HI * pow(TEMP_LO / TEMP_HI, (double)it / (double)L);
        int q[4];
        if (!swap_try(q)) continue;
        int nw = cost_now();
        if (nw <= cur || uni() < exp((double)(cur - nw) / temp)) {
            cur = nw;
            if (cur == 0) {
                *curp = 0;
                return 1;
            }
        } else {
            swap_undo(q);
        }
    }
    *curp = cur;
    return cur == 0;
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
    if (n <= 0 || n > MAXN - 2 || Dist < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    W = (N + 63) / 64;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= Dd || deg[v] >= Dd || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    for (int v = 0; v < N; v++) side[v] = -1;
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

    double t_end = now_s() + budget;
    while (now_s() < t_end && N < MAXN - 2) {
        while (spare_fill_once(1)) {
        }
        int cur = cost_now();
        if (cur == 0) {
            if (!hasSnap || N > snapN) save_snap();
            if (!grow()) break;
            cur = cost_now();
        }
        int ok = anneal(LEN, &cur, t_end);
        if (!ok && hasSnap) load_snap();
    }

    int fin = cost_now();
    if (fin == 0 && (!hasSnap || N > snapN)) save_snap();
    if (!hasSnap) {
        printf("0 0\n");
        return 0;
    }
    int M = 0;
    for (int v = 0; v < snapN; v++)
        for (int k = 0; k < snapDeg[v]; k++)
            if (snapAdj[v][k] > v) M++;
    printf("%d %d\n", snapN, M);
    for (int v = 0; v < snapN; v++)
        for (int k = 0; k < snapDeg[v]; k++)
            if (snapAdj[v][k] > v) printf("%d %d\n", v, snapAdj[v][k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has spare capacity s = d - q - 1. Choose a point set S that is an arc, so each
# line holds at most s points of S. Add an A-vertex for each P in S (joined to
# lines through P) and a B-vertex for each j in S (joined to points on line j).
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C driver.
# ----------------------------------------------------------------------------

def _augment(n0, e0, d, D, seed, budget, timeout):
    """Run the C annealing engine from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=timeout)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 85% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.85 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))

    starts = []
    if D >= 3:
        starts.extend(_arc_extensions(d, t0 + 0.2 * time_limit, rng))
    if D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    starts = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    if lib.is_valid(fallback[0], fallback[1], d, D):
        starts.append(fallback)
    if not starts:
        return 1, []
    starts.sort(key=lambda g: -g[0])
    best = starts[0]

    # Already at the Moore bound: nothing to gain from searching.
    if best[0] >= lib.moore_bound(d, D):
        return best

    remaining = hard_end - time.monotonic() - 2.0
    if remaining >= 1.0:
        try:
            n1, e1 = _augment(best[0], best[1], d, D, seed * 31 + 1,
                              remaining, remaining + 4.0)
            if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                best = (n1, e1)
        except Exception:
            pass
    return best
