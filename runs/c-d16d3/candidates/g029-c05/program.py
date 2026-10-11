import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: annealed growth of a bipartite graph under max degree d and
# diameter D. Starts from the given graph. Each time the graph is valid, it
# adds one vertex (attached by stealing edge slots) and then repairs diameter
# violations with degree-preserving 2-switches and spare-slot edge additions.
# The best valid snapshot is printed on exit.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 1024
#define WMAX 16
#define DMAX 40
#define SEMAX 24000

static int Dg, Dd, N;
static int side[NMAX];
static int deg[NMAX];
static int adj[NMAX][DMAX];
static unsigned char M[NMAX][NMAX];
static uint64_t RA[NMAX][WMAX];
static uint64_t RB[NMAX][WMAX];

static int snapN = 0, snapE = 0;
static int snapSide[NMAX];
static int SE[SEMAX][2];

static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu_now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int a, int b) {
    M[a][b] = 1;
    M[b][a] = 1;
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void del_entry(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adj[a][k] == b) {
            adj[a][k] = adj[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void remove_edge(int a, int b) {
    M[a][b] = 0;
    M[b][a] = 0;
    del_entry(a, b);
    del_entry(b, a);
}

/* Number of ordered pairs (u,v), u != v, at distance > Dd. Zero iff valid. */
static long long cost_all(void) {
    int W = (N + 63) >> 6;
    uint64_t (*A)[WMAX] = RA;
    uint64_t (*B)[WMAX] = RB;
    uint64_t (*T)[WMAX];
    for (int v = 0; v < N; v++) {
        memset(A[v], 0, sizeof(uint64_t) * WMAX);
        A[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int step = 0; step < Dd; step++) {
        for (int v = 0; v < N; v++) {
            uint64_t *out = B[v];
            memcpy(out, A[v], sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *in = A[adj[v][k]];
                for (int w = 0; w < W; w++) out[w] |= in[w];
            }
        }
        T = A;
        A = B;
        B = T;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(A[v][w]);
        bad += N - c;
    }
    return bad;
}

static void save_best(void) {
    snapN = N;
    snapE = 0;
    memcpy(snapSide, side, sizeof(int) * (size_t)N);
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < deg[v]; k++) {
            int u = adj[v][k];
            if (v < u && snapE < SEMAX) {
                SE[snapE][0] = v;
                SE[snapE][1] = u;
                snapE++;
            }
        }
    }
}

static void clear_graph(void) {
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < deg[v]; k++) M[v][adj[v][k]] = 0;
        deg[v] = 0;
    }
    N = 0;
}

static void load_best(void) {
    clear_graph();
    N = snapN;
    memcpy(side, snapSide, sizeof(int) * (size_t)N);
    for (int e = 0; e < snapE; e++) add_edge(SE[e][0], SE[e][1]);
}

/* Add vertex N on the smaller side, attach it to Dg opposite vertices,
   stealing one edge from a saturated neighbour when needed. */
static void grow(void) {
    int cnt0 = 0, cnt1 = 0;
    for (int v = 0; v < N; v++) {
        if (side[v]) cnt1++;
        else cnt0++;
    }
    int x = N++;
    side[x] = (cnt0 <= cnt1) ? 0 : 1;
    deg[x] = 0;
    int tries = 0;
    while (deg[x] < Dg && tries < 2000) {
        tries++;
        int w = rnd_int(x);
        if (side[w] == side[x] || M[x][w]) continue;
        if (deg[w] >= Dg) {
            if (deg[w] == 0) continue;
            int z = adj[w][rnd_int(deg[w])];
            remove_edge(w, z);
        }
        add_edge(x, w);
    }
}

static int color_graph(void) {
    static int col[NMAX];
    static int q[NMAX];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        int head = 0, tail = 0;
        col[s] = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            for (int k = 0; k < deg[u]; k++) {
                int w = adj[u][k];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    q[tail++] = w;
                } else if (col[w] == col[u]) {
                    return 0;
                }
            }
        }
    }
    for (int v = 0; v < N; v++) side[v] = col[v];
    return 1;
}

/* One annealing move. Spare-slot edge addition or degree-preserving 2-switch. */
static void step(long long *cur, double T) {
    if (rnd_unit() < 0.15) {
        for (int tries = 0; tries < 60; tries++) {
            int a = rnd_int(N), b = rnd_int(N);
            if (a == b || side[a] == side[b] || deg[a] >= Dg || deg[b] >= Dg || M[a][b]) continue;
            add_edge(a, b);
            *cur = cost_all();
            return;
        }
    }
    int a = rnd_int(N);
    if (deg[a] == 0) return;
    int b = adj[a][rnd_int(deg[a])];
    int c = -1;
    for (int tries = 0; tries < 200; tries++) {
        int x = rnd_int(N);
        if (x != a && side[x] == side[a] && deg[x] > 0) {
            c = x;
            break;
        }
    }
    if (c < 0) return;
    int d = adj[c][rnd_int(deg[c])];
    if (d == b || M[a][d] || M[c][b]) return;
    remove_edge(a, b);
    remove_edge(c, d);
    add_edge(a, d);
    add_edge(c, b);
    long long nc = cost_all();
    long long delta = nc - *cur;
    if (delta <= 0 || rnd_unit() < exp(-(double)delta / T)) {
        *cur = nc;
    } else {
        remove_edge(a, d);
        remove_edge(c, b);
        add_edge(a, b);
        add_edge(c, d);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dg = atoi(argv[1]);
    Dd = atoi(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0xD6E8FEB86659FD93ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    double limit = atof(argv[4]);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || n0 >= NMAX - 2 ||
        Dg < 1 || Dg > DMAX || Dd < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n0;
    for (int i = 0; i < m0; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a < 0 || a >= N || b < 0 || b >= N || a == b) continue;
        if (M[a][b] || deg[a] >= Dg || deg[b] >= Dg) continue;
        add_edge(a, b);
    }
    if (!color_graph()) {
        printf("0 0\n");
        return 0;
    }

    double t0 = cpu_now();
    long long cur = cost_all();
    snapN = 0;
    snapE = 0;
    if (cur == 0) save_best();

    double T0 = 2.0, Tmin = 0.25, T = T0;
    long long stall = 0, iters = 0;
    const long long STALL = 40000;

    for (;;) {
        if ((iters & 127) == 0 && cpu_now() - t0 > limit) break;
        iters++;
        if (cur == 0) {
            if (N > snapN) save_best();
            if (N + 2 >= NMAX) break;
            grow();
            cur = cost_all();
            T = T0;
            stall = 0;
            continue;
        }
        if (++stall > STALL) {
            if (snapN > 0) load_best();
            cur = cost_all();
            T = T0;
            stall = 0;
            continue;
        }
        T *= 0.9998;
        if (T < Tmin) T = Tmin;
        step(&cur, T);
    }
    if (cur == 0 && N > snapN) save_best();

    printf("%d %d\n", snapN, snapE);
    for (int e = 0; e < snapE; e++) printf("%d %d\n", SE[e][0], SE[e][1]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions: arc-extended projective plane graphs (diameter 3) and
# the generalized quadrangle W(q) (diameter 4). These supply the C search
# with strong starting graphs.
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


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by at most s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy selection so that every target is hit at most s times."""
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
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
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d; diameter 3."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Build: best Python start graph, then the C annealed-growth search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.2 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best[0]:
                consider(n_c, e_c)

    if D >= 4 and time.monotonic() - t0 < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing to search for.
    if best[0] >= lib.moore_bound(d, D):
        return best

    remaining = time_limit - (time.monotonic() - t0) - 4.0
    if remaining > 3.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(0.9 * remaining, 2)],
                            stdin_graph=best, timeout=remaining)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
