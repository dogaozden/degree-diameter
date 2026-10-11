"""Diameter-3 bipartite search: arc-extended projective plane start, then a C engine that
grows the graph and repairs it by simulated annealing.

Bold change: the old engine only added vertices greedily and never revisited existing edges.
The new C engine keeps a valid snapshot and alternates two steps:
  1. Cover-based growth (the old rule): add one vertex joined to spare vertices that cover
     every existing vertex within distance D-1. This always keeps the graph valid.
  2. If that fails, a new vertex with spare-capacity neighbours is added and then repaired by
     simulated annealing. The objective is the number of ordered vertex pairs at distance > D.
     Moves keep the bipartition: degree-preserving edge swaps, edge transfers that move spare
     degree, and edge insertions between spare vertices. A snapshot is taken whenever the
     cost reaches zero. Failed attempts restore the last valid snapshot.

Python builds the start (arc-extended PG(2,q) incidence, the generalized quadrangle for D >= 4,
or K_{d,d} as a safe fallback), runs the C engine, and returns only graphs that lib.is_valid accepts.
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
#define MAXDEG 48

static int N, Dd, Dist, W;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static int bq[MAXN];

static uint64_t ballA[MAXN][WORDS];
static uint64_t ballR[MAXN][WORDS];
static uint64_t tmpB[MAXN][WORDS];

static int sN;
static int sdeg[MAXN];
static int sadj[MAXN][MAXDEG];

static double deadline;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double urand(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* out[v] = bitset of vertices within distance r of v. */
static void compute_ball(int r, uint64_t (*out)[WORDS]) {
    uint64_t (*A)[WORDS] = out;
    uint64_t (*B)[WORDS] = tmpB;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < W; i++) A[v][i] = 0;
        A[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < N; v++) {
            for (int i = 0; i < W; i++) B[v][i] = A[v][i];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = A[adj[v][k]];
                for (int i = 0; i < W; i++) B[v][i] |= src[i];
            }
        }
        uint64_t (*T)[WORDS] = A;
        A = B;
        B = T;
    }
    if (A != out) {
        for (int v = 0; v < N; v++)
            for (int i = 0; i < W; i++) out[v][i] = A[v][i];
    }
}

/* Number of ordered pairs at distance > Dist. Zero means valid. */
static long cost(void) {
    compute_ball(Dist, ballA);
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int i = 0; i < W; i++) c += popc(ballA[v][i]);
        bad += N - c;
    }
    return bad;
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

static void del_one(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adj[u][k] == v) {
            adj[u][k] = adj[u][--deg[u]];
            return;
        }
    }
}

static void del_edge(int u, int v) {
    del_one(u, v);
    del_one(v, u);
}

static void snapshot(void) {
    sN = N;
    for (int v = 0; v < N; v++) {
        sdeg[v] = deg[v];
        memcpy(sadj[v], adj[v], sizeof(int) * (size_t)deg[v]);
    }
}

static void restore(void) {
    N = sN;
    W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        deg[v] = sdeg[v];
        memcpy(adj[v], sadj[v], sizeof(int) * (size_t)deg[v]);
    }
}

/* Uniform random vertex on side s; spare=1 needs deg < Dd, spare=0 needs deg > 0. */
static int pick_side(int s, int spare) {
    int cnt = 0, pick = -1;
    for (int v = 0; v < N; v++) {
        if (side[v] != s) continue;
        if (spare ? (deg[v] >= Dd) : (deg[v] == 0)) continue;
        cnt++;
        if (rndint(cnt) == 0) pick = v;
    }
    return pick;
}

/* Cover-based growth: new vertex on side X joined to spare vertices covering all
   existing vertices within distance Dist-1. Always keeps the graph valid. */
static int try_add(int X) {
    if (N + 1 >= MAXN) return 0;
    compute_ball(Dist - 1, ballR);
    uint64_t U[WORDS];
    for (int i = 0; i < W; i++) U[i] = ~0ULL;
    if (N & 63) U[W - 1] = (1ULL << (N & 63)) - 1ULL;
    static int sel[MAXN];
    memset(sel, 0, sizeof(int) * (size_t)N);
    int T[MAXDEG];
    int nt = 0;
    while (nt < Dd) {
        int best = -1;
        long bestsc = -1;
        for (int v = 0; v < N; v++) {
            if (side[v] == X || deg[v] >= Dd || sel[v]) continue;
            long g = 0;
            for (int i = 0; i < W; i++) g += popc(ballR[v][i] & U[i]);
            if (g <= 0) continue;
            long sc = g * 8 + rndint(8);
            if (sc > bestsc) {
                bestsc = sc;
                best = v;
            }
        }
        if (best < 0) break;
        sel[best] = 1;
        T[nt++] = best;
        for (int i = 0; i < W; i++) U[i] &= ~ballR[best][i];
    }
    if (nt == 0) return 0;
    for (int i = 0; i < W; i++)
        if (U[i]) return 0;
    int x = N;
    side[x] = X;
    deg[x] = 0;
    N++;
    W = (N + 63) / 64;
    for (int k = 0; k < nt; k++) add_edge(x, T[k]);
    return 1;
}

/* Simulated annealing on the bad-pair cost. Returns 1 and snapshots when cost reaches 0. */
static int anneal(int iters, double T0, double T1) {
    long cc = cost();
    if (cc == 0) {
        snapshot();
        return 1;
    }
    for (int it = 0; it < iters; it++) {
        if ((it & 31) == 0 && now_s() > deadline) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int r = rndint(100);
        if (r < 15) {
            /* Insert an edge between two spare vertices: never increases the cost. */
            int a = pick_side(0, 1), b = pick_side(1, 1);
            if (a < 0 || b < 0 || has_edge(a, b)) continue;
            add_edge(a, b);
            cc = cost();
            if (cc == 0) {
                snapshot();
                return 1;
            }
        } else if (r < 55) {
            /* Transfer: spare vertex a takes edge (b, c2), so c2 loses one degree. */
            int s = rndint(2);
            int a = pick_side(s, 1);
            int b = pick_side(1 - s, 0);
            if (a < 0 || b < 0 || has_edge(a, b)) continue;
            int c2 = adj[b][rndint(deg[b])];
            del_edge(b, c2);
            add_edge(a, b);
            long nc = cost();
            if (nc <= cc || urand() < exp(-(double)(nc - cc) / T)) {
                cc = nc;
                if (cc == 0) {
                    snapshot();
                    return 1;
                }
            } else {
                del_edge(a, b);
                add_edge(b, c2);
            }
        } else {
            /* Degree-preserving double-edge swap across the bipartition. */
            int a = pick_side(0, 0), a2 = pick_side(0, 0);
            if (a < 0 || a2 < 0 || a == a2) continue;
            int b = adj[a][rndint(deg[a])];
            int b2 = adj[a2][rndint(deg[a2])];
            if (b == b2 || has_edge(a, b2) || has_edge(a2, b)) continue;
            del_edge(a, b);
            del_edge(a2, b2);
            add_edge(a, b2);
            add_edge(a2, b);
            long nc = cost();
            if (nc <= cc || urand() < exp(-(double)(nc - cc) / T)) {
                cc = nc;
                if (cc == 0) {
                    snapshot();
                    return 1;
                }
            } else {
                del_edge(a, b2);
                del_edge(a2, b);
                add_edge(a, b);
                add_edge(a2, b2);
            }
        }
    }
    return 0;
}

/* Add a vertex on a random side joined to up to Dd spare vertices on the other side, then anneal. */
static int grow_anneal(int iters) {
    if (N + 1 >= MAXN - 1) return 0;
    int X = rndint(2), t = 1 - X;
    static int cand[MAXN];
    int nc = 0;
    for (int v = 0; v < N; v++)
        if (side[v] == t && deg[v] < Dd) cand[nc++] = v;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tmp = cand[i];
        cand[i] = cand[j];
        cand[j] = tmp;
    }
    int k = nc < Dd ? nc : Dd;
    int x = N;
    side[x] = X;
    deg[x] = 0;
    N++;
    W = (N + 63) / 64;
    for (int i = 0; i < k; i++) add_edge(x, cand[i]);
    return anneal(iters, 2.0, 0.05);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    if (Dd > MAXDEG) Dd = MAXDEG;
    Dist = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 2 || Dist < 1 || Dd < 1) {
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
    snapshot();
    deadline = now_s() + budget;

    int valid = (cost() == 0);
    if (!valid) {
        /* Start is not valid: anneal until a valid state is found, or time runs out. */
        while (now_s() < deadline) {
            if (anneal(20000, 2.0, 0.05)) break;
        }
    } else {
        int fails = 0;
        while (now_s() < deadline && N < MAXN - 2) {
            if (try_add(rndint(2))) {
                snapshot();
                fails = 0;
                continue;
            }
            if (grow_anneal(6000)) {
                fails = 0;
                continue;
            }
            restore();
            if (++fails > 1000000) break;
        }
    }
    restore();

    int M = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) M++;
    printf("%d %d\n", N, M);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) printf("%d %d\n", v, adj[v][k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# Start from PG(2, q) incidence. Each old vertex has spare capacity s = d - q - 1.
# Choose an arc S so each line holds at most s points of S, then add an A-vertex
# for each P in S and a B-vertex for each j in S.
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
# C engine driver.
# ----------------------------------------------------------------------------

def _grow(n0, e0, d, D, seed, budget):
    """Run the C grow-and-anneal engine from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=budget + 8.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.80 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))

    starts = []
    if D >= 3:
        starts.extend(_arc_extensions(d, t0 + 0.20 * time_limit, rng))
    if D >= 4 and time.monotonic() < t0 + 0.20 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    starts = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    starts.sort(key=lambda g: -g[0])
    if lib.is_valid(fallback[0], fallback[1], d, D):
        starts.append(fallback)
    if not starts:
        return 1, []
    best = starts[0]

    # Grow and repair the best start with the C engine, using the remaining budget.
    remaining = hard_end - time.monotonic()
    if D >= 3 and remaining >= 3.0:
        try:
            n1, e1 = _grow(best[0], best[1], d, D, seed * 31 + 7, remaining - 1.5)
            if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                best = (n1, e1)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
