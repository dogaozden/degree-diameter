"""Diameter-3 bipartite search: arc-extended projective plane starts plus an annealed repair engine.

Starts are valid graphs: the arc-extended PG(2,q) incidence graph (for D = 3), the generalized
quadrangle W(q) (for D >= 4), or K_{d,d}. The C engine grows the graph one vertex at a time.

New idea (repair insertion): a new vertex is attached greedily to spare vertices on the other side
by set cover. If the result still has pairs at distance > D, the engine does not discard it. It runs
a short simulated annealing over graph moves that keep the degree bound and bipartiteness:
degree-preserving 2-switches, rewiring one endpoint onto a spare vertex, and adding free edges
between spare vertices. The objective is the number of bad pairs (distance > D). If annealing
reaches zero bad pairs, the larger graph is committed. Otherwise the snapshot is restored.
The state is always valid at loop boundaries, and Python re-checks the output with lib.is_valid.
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
#define WMAX (MAXN / 64)
#define MAXDEG 64

static int N, W, Dd, Dist;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static uint64_t bufA[MAXN][WMAX], bufB[MAXN][WMAX];
static uint64_t tmpR[MAXN][WMAX];
static uint64_t ballR[MAXN][WMAX];
static int snapN;
static int snapDeg[MAXN];
static int snapAdj[MAXN][MAXDEG];
static int bq[MAXN];
static int sel[MAXN];
static uint64_t rs = 88172645463325252ULL;
static double t_end;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double urand(void) { return (double)(rnd() % 1000000007ULL) / 1000000007.0; }

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

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

/* out[v] = set of vertices within distance R of v. */
static void reach_levels(int R, uint64_t (*out)[WMAX]) {
    uint64_t (*cur)[WMAX] = bufA;
    uint64_t (*nxt)[WMAX] = bufB;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < W; i++) cur[v][i] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < R; s++) {
        for (int v = 0; v < N; v++) {
            for (int i = 0; i < W; i++) nxt[v][i] = cur[v][i];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int i = 0; i < W; i++) nxt[v][i] |= cur[u][i];
            }
        }
        uint64_t (*t)[WMAX] = cur;
        cur = nxt;
        nxt = t;
    }
    for (int v = 0; v < N; v++)
        for (int i = 0; i < W; i++) out[v][i] = cur[v][i];
}

/* Number of unordered pairs at distance > Dist (unreachable pairs included). */
static long evaluate(void) {
    reach_levels(Dist, tmpR);
    long total = 0;
    for (int v = 0; v < N; v++)
        for (int i = 0; i < W; i++) total += popc(tmpR[v][i]);
    long nn = (long)N * (long)N;
    return (nn - total) / 2;
}

/* Greedy set-cover insertion of a new vertex on side X (exact cover at radius Dist-1). */
static int grow(int X) {
    if (N + 2 >= MAXN) return 0;
    reach_levels(Dist - 1, ballR);
    uint64_t U[WMAX];
    for (int i = 0; i < W; i++) U[i] = ~0ULL;
    if (N & 63) U[W - 1] = (1ULL << (N & 63)) - 1ULL;
    memset(sel, 0, sizeof(int) * (size_t)N);
    int T[MAXDEG];
    int nt = 0;
    while (nt < Dd) {
        int best = -1;
        long bestsc = -1;
        for (int v = 0; v < N; v++) {
            if (side[v] == X || deg[v] >= Dd || sel[v]) continue;
            int g = 0;
            for (int i = 0; i < W; i++) g += popc(ballR[v][i] & U[i]);
            if (g <= 0) continue;
            long sc = (long)g * 8 + rndint(8);
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
    int x = N;
    side[x] = X;
    deg[x] = 0;
    for (int k = 0; k < nt; k++) add_edge(x, T[k]);
    N++;
    W = (N + 63) / 64;
    return 1;
}

/* Simulated annealing on bad-pair count. Moves keep degrees <= Dd and bipartiteness. */
static long anneal(long iters, double T0) {
    long cur = evaluate();
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 255) == 0 && now() > t_end) break;
        double T = T0 * (1.0 - (double)it / (double)iters) + 1e-6;
        int r = rndint(10);
        if (r < 2) {
            /* free add between two spare vertices: never increases bad pairs */
            int a = rndint(N), b = rndint(N);
            if (side[a] != 0 || side[b] != 1) continue;
            if (deg[a] >= Dd || deg[b] >= Dd || has_edge(a, b)) continue;
            add_edge(a, b);
            cur = evaluate();
        } else if (r < 5) {
            /* degree-preserving 2-switch of two edges (a,b), (c,e) -> (a,e), (c,b) */
            int a = rndint(N), c = rndint(N);
            if (side[a] != 0 || side[c] != 0 || deg[a] == 0 || deg[c] == 0) continue;
            int b = adj[a][rndint(deg[a])];
            int e = adj[c][rndint(deg[c])];
            if (a == c || b == e || has_edge(a, e) || has_edge(c, b)) continue;
            del_edge(a, b);
            del_edge(c, e);
            add_edge(a, e);
            add_edge(c, b);
            long nw = evaluate();
            if (nw <= cur || urand() < exp(-(double)(nw - cur) / T)) {
                cur = nw;
            } else {
                del_edge(a, e);
                del_edge(c, b);
                add_edge(a, b);
                add_edge(c, e);
            }
        } else {
            /* move one endpoint of edge (a,b) to a spare vertex e on the B side */
            int a = rndint(N);
            if (side[a] != 0 || deg[a] == 0) continue;
            int b = adj[a][rndint(deg[a])];
            int e = rndint(N);
            if (side[e] != 1 || e == b || deg[e] >= Dd || has_edge(a, e)) continue;
            del_edge(a, b);
            add_edge(a, e);
            long nw = evaluate();
            if (nw <= cur || urand() < exp(-(double)(nw - cur) / T)) {
                cur = nw;
            } else {
                del_edge(a, e);
                add_edge(a, b);
            }
        }
    }
    return cur;
}

static void snapshot(void) {
    snapN = N;
    for (int v = 0; v < N; v++) {
        snapDeg[v] = deg[v];
        for (int k = 0; k < deg[v]; k++) snapAdj[v][k] = adj[v][k];
    }
}

static void restore(void) {
    N = snapN;
    W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        deg[v] = snapDeg[v];
        for (int k = 0; k < deg[v]; k++) adj[v][k] = snapAdj[v][k];
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    if (Dd < 1) Dd = 1;
    if (Dd > MAXDEG) Dd = MAXDEG;
    Dist = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    long iters = argc > 5 ? atol(argv[5]) : 1500;
    double T0 = argc > 6 ? atof(argv[6]) : 0.6;
    if (iters < 10) iters = 10;
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
        if (deg[u] >= MAXDEG || deg[v] >= MAXDEG) continue;
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

    t_end = now() + budget;
    if (evaluate() > 0) {
        if (anneal(iters * 20, T0) > 0) {
            printf("0 0\n");
            return 0;
        }
    }

    int fails = 0;
    while (now() < t_end && fails < 400 && N < MAXN - 2) {
        snapshot();
        int X = rndint(2);
        if (!grow(X)) {
            fails++;
            continue;
        }
        long b = evaluate();
        if (b > 0) b = anneal(iters, T0);
        if (b == 0) {
            fails = 0;
        } else {
            restore();
            fails++;
        }
    }

    if (evaluate() > 0) {
        printf("0 0\n");
        return 0;
    }
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
    """Run the C repair-insertion engine from (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", 1500, 0.6],
                     stdin_graph=(n0, e0), timeout=timeout)
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
        starts.extend(_arc_extensions(d, t0 + 0.2 * time_limit, rng))
    if D >= 4 and time.monotonic() < t0 + 0.25 * time_limit:
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

    # The largest start gets most of the search time; the runner-up gets the rest.
    plan = starts[:2]
    for idx, src in enumerate(plan):
        remaining = hard_end - time.monotonic()
        if remaining < 2.0:
            break
        share = remaining * (0.75 if (idx == 0 and len(plan) > 1) else 1.0)
        if idx == len(plan) - 1 and idx > 0:
            share = remaining
        try:
            n1, e1 = _augment(src[0], src[1], d, D, seed * 31 + idx,
                              max(0.3, share - 1.0), share + 3.0)
        except Exception:
            continue
        if n1 > best[0] and lib.is_valid(n1, e1, d, D):
            best = (n1, e1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
