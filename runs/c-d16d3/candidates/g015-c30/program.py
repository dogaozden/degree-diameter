"""Diameter-D bipartite search: arc-extended projective plane starts plus a C grow-and-anneal engine.

Starts are valid graphs: arc-extended PG(2,q) incidence graphs for D >= 3, the generalized
quadrangle W(q) for D >= 4, and K_{d,d} as a safe fallback. The C engine keeps a fixed
bipartition and degree cap d, and minimises the number of vertex pairs at distance > D with
simulated annealing (edge add, spare-slot shift, and degree-preserving 2-switch moves). When the
cost reaches zero it records the graph, adds one vertex on each side, and anneals again. Only
zero-cost states are returned, and Python re-checks every result with lib.is_valid.
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
#define MAXW (MAXN / 64)
#define MAXDEG 64
#define MAXE (MAXN * MAXDEG / 2)

static int N, Dd, Dist;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static unsigned char isadj[MAXN][MAXN];
static int side[MAXN];
static uint64_t bufA[MAXN][MAXW], bufB[MAXN][MAXW];

static int bestN = 0, bestM = 0;
static int bestU[MAXE], bestV[MAXE];
static long curcost = 0;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > Dist (disconnected pairs included). */
static long total_cost(void) {
    int w = (N + 63) / 64;
    uint64_t (*cur)[MAXW] = bufA;
    uint64_t (*nxt)[MAXW] = bufB;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < w; i++) cur[v][i] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < Dist; r++) {
        for (int v = 0; v < N; v++) {
            for (int i = 0; i < w; i++) nxt[v][i] = cur[v][i];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int i = 0; i < w; i++) nxt[v][i] |= cur[u][i];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long miss = 0;
    for (int v = 0; v < N; v++) {
        int p = 0;
        for (int i = 0; i < w; i++) p += popc(cur[v][i]);
        miss += N - p;
    }
    return miss / 2;
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
    isadj[a][b] = 1;
    isadj[b][a] = 1;
}

static void drop_nb(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adj[a][k] == b) {
            adj[a][k] = adj[a][--deg[a]];
            return;
        }
    }
}

static void remove_edge(int a, int b) {
    drop_nb(a, b);
    drop_nb(b, a);
    isadj[a][b] = 0;
    isadj[b][a] = 0;
}

/* Random edge, returned as (a in side 0, b in side 1). */
static int random_edge(int *a, int *b) {
    for (int t = 0; t < 64; t++) {
        int v = rndint(N);
        if (deg[v] == 0) continue;
        int u = adj[v][rndint(deg[v])];
        if (side[v] == 0) {
            *a = v;
            *b = u;
        } else {
            *a = u;
            *b = v;
        }
        return 1;
    }
    return 0;
}

static void save_best(void) {
    int m = 0;
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < deg[v]; k++) {
            if (adj[v][k] > v && m < MAXE) {
                bestU[m] = v;
                bestV[m] = adj[v][k];
                m++;
            }
        }
    }
    bestN = N;
    bestM = m;
}

/* Add one isolated vertex on each side. */
static void grow(void) {
    if (N + 2 > MAXN - 2) return;
    side[N] = 0;
    deg[N] = 0;
    side[N + 1] = 1;
    deg[N + 1] = 0;
    N += 2;
}

static int accept(long delta, double T) {
    if (delta <= 0) return 1;
    return urand() < exp(-(double)delta / T);
}

/* Called whenever the state may have reached zero cost. */
static void after_improve(void) {
    if (curcost == 0) {
        save_best();
        grow();
        curcost = total_cost();
    }
}

static void anneal(double budget) {
    const long PL = 20000;
    const double T0 = 0.9, T1 = 0.08;
    double t_end = elapsed() + budget;
    long pt = 0;
    int spA[MAXN], spB[MAXN];

    curcost = total_cost();
    after_improve();

    while (elapsed() < t_end) {
        if (curcost == 0 && N + 2 > MAXN - 2) break;

        pt++;
        if (pt >= PL) pt = 0;
        double T = T0 * pow(T1 / T0, (double)pt / (double)PL);

        int nA = 0, nB = 0;
        for (int v = 0; v < N; v++) {
            if (deg[v] < Dd) {
                if (side[v] == 0) spA[nA++] = v;
                else spB[nB++] = v;
            }
        }

        int r = rndint(100);
        int a, b;
        if (r < 35) {
            /* Add a missing edge between two spare vertices: never increases cost. */
            if (nA == 0 || nB == 0) continue;
            a = spA[rndint(nA)];
            b = spB[rndint(nB)];
            if (isadj[a][b]) continue;
            add_edge(a, b);
            curcost = total_cost();
            after_improve();
        } else if (r < 55) {
            /* Move one edge end onto a spare vertex (degrees of the other end preserved). */
            if (!random_edge(&a, &b)) continue;
            if (rndint(2) == 1) {
                if (nB == 0) continue;
                int b2 = spB[rndint(nB)];
                if (b2 == b || isadj[a][b2]) continue;
                remove_edge(a, b);
                add_edge(a, b2);
                long nc = total_cost();
                if (accept(nc - curcost, T)) {
                    curcost = nc;
                    after_improve();
                } else {
                    remove_edge(a, b2);
                    add_edge(a, b);
                }
            } else {
                if (nA == 0) continue;
                int a2 = spA[rndint(nA)];
                if (a2 == a || isadj[a2][b]) continue;
                remove_edge(a, b);
                add_edge(a2, b);
                long nc = total_cost();
                if (accept(nc - curcost, T)) {
                    curcost = nc;
                    after_improve();
                } else {
                    remove_edge(a2, b);
                    add_edge(a, b);
                }
            }
        } else {
            /* Degree-preserving 2-switch. */
            int a2, b2;
            if (!random_edge(&a, &b) || !random_edge(&a2, &b2)) continue;
            if (a == a2 || b == b2 || isadj[a][b2] || isadj[a2][b]) continue;
            remove_edge(a, b);
            remove_edge(a2, b2);
            add_edge(a, b2);
            add_edge(a2, b);
            long nc = total_cost();
            if (accept(nc - curcost, T)) {
                curcost = nc;
                after_improve();
            } else {
                remove_edge(a, b2);
                remove_edge(a2, b);
                add_edge(a, b);
                add_edge(a2, b2);
            }
        }
    }
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
    for (int i = 0; i < 10; i++) rnd();

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
        if (isadj[u][v] || deg[u] >= Dd || deg[v] >= Dd) continue;
        add_edge(u, v);
    }

    /* Bipartition by BFS colouring. */
    for (int v = 0; v < N; v++) side[v] = -1;
    int bq[MAXN];
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
    for (int u = 0; u < N; u++)
        for (int k = 0; k < deg[u]; k++)
            if (side[adj[u][k]] == side[u]) {
                printf("0 0\n");
                return 0;
            }

    anneal(budget);

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestU[i], bestV[i]);
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
# C grow-and-anneal driver.
# ----------------------------------------------------------------------------

def _anneal(start, d, D, seed, budget, timeout):
    """Run the C annealer from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=start, timeout=timeout)
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

    # Already at the Moore bound: nothing to search for.
    if best[0] >= lib.moore_bound(d, D):
        return best

    # Grow-and-anneal from the best start, using the remaining time.
    remaining = hard_end - time.monotonic()
    if remaining > 3.0:
        budget = remaining - 2.0
        try:
            n1, e1 = _anneal(best, d, D, seed, budget, budget + 5.0)
            if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                best = (n1, e1)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
