"""Diameter-D bipartite search: arc-extended projective plane starts plus a C annealing engine.

Starts are valid graphs: arc-extended PG(2,q) incidence graphs, the generalized quadrangle
W(q) for D >= 4, or K_{d,d} as a safe fallback. The C engine works differently from the
earlier augmenter. It keeps a valid snapshot, adds one vertex with a greedy set cover, and
then runs simulated annealing on the number of bad pairs (distance > D). Its moves are
degree-preserving bipartite edge switches and edge insertions between spare vertices. When
the bad-pair count reaches zero, the graph is snapshotted and another vertex is added. After
too many failed moves, the engine reloads the last valid snapshot. Python re-checks every
output with lib.is_valid and falls back to the best start.
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
#define MW 16
#define MAXDEG 64
#define MAXE (MAXN * MAXDEG / 2)

typedef uint64_t Row[MW];

static int N, Dd, Dist, WN;
static int deg[MAXN], adj[MAXN][MAXDEG], side[MAXN];
static Row am[MAXN];
static Row BUF[2][MAXN];
static int snapN = 0, snapE = 0;
static int snapU[MAXE], snapV[MAXE];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    return (int)((am[u][v >> 6] >> (v & 63)) & 1ULL);
}

static void link_e(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
    am[u][v >> 6] |= 1ULL << (v & 63);
    am[v][u >> 6] |= 1ULL << (u & 63);
}

static void unlink_half(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adj[u][k] == v) {
            adj[u][k] = adj[u][--deg[u]];
            break;
        }
    }
}

static void unlink_e(int u, int v) {
    unlink_half(u, v);
    unlink_half(v, u);
    am[u][v >> 6] &= ~(1ULL << (v & 63));
    am[v][u >> 6] &= ~(1ULL << (u & 63));
}

/* Bitsets of the radius-r balls; returns a pointer to the buffer holding them. */
static Row *reach(int r) {
    int c = 0;
    for (int v = 0; v < N; v++) {
        memset(BUF[0][v], 0, sizeof(Row));
        BUF[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        int nx = 1 - c;
        for (int v = 0; v < N; v++) {
            uint64_t *dst = BUF[nx][v];
            const uint64_t *src = BUF[c][v];
            for (int i = 0; i < WN; i++) dst[i] = src[i];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *nb = BUF[c][adj[v][k]];
                for (int i = 0; i < WN; i++) dst[i] |= nb[i];
            }
        }
        c = nx;
    }
    return BUF[c];
}

/* Number of unordered pairs at distance > Dist (unreachable pairs included). */
static long full_cost(void) {
    Row *R = reach(Dist);
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int i = 0; i < WN; i++) c += popc(R[v][i]);
        bad += N - c;
    }
    return bad / 2;
}

/* Add one vertex on a random side, joined greedily to spare vertices of the other side. */
static int add_vertex(void) {
    if (N + 2 >= MAXN) return 0;
    int X = rndint(2);
    Row U;
    memset(U, 0, sizeof(Row));
    for (int v = 0; v < N; v++) U[v >> 6] |= 1ULL << (v & 63);
    Row *R = reach(Dist - 1);
    int sel[MAXN];
    memset(sel, 0, sizeof(int) * (size_t)N);
    int T[MAXDEG], nt = 0;
    while (nt < Dd) {
        int best = -1;
        long bsc = -1;
        for (int v = 0; v < N; v++) {
            if (side[v] == X || deg[v] >= Dd || sel[v]) continue;
            long g = 0;
            for (int i = 0; i < WN; i++) g += popc(R[v][i] & U[i]);
            if (g <= 0) continue;
            long sc = g * 8 + rndint(8);
            if (sc > bsc) {
                bsc = sc;
                best = v;
            }
        }
        if (best < 0) break;
        sel[best] = 1;
        T[nt++] = best;
        for (int i = 0; i < WN; i++) U[i] &= ~R[best][i];
    }
    if (nt == 0) return 0;
    int x = N;
    N++;
    WN = (N + 63) / 64;
    side[x] = X;
    deg[x] = 0;
    memset(am[x], 0, sizeof(Row));
    for (int k = 0; k < nt; k++) link_e(x, T[k]);
    return 1;
}

/* Insert an edge between a spare side-0 and spare side-1 vertex. Never increases the cost. */
static int do_add(void) {
    int s0[MAXN], s1[MAXN], n0 = 0, n1 = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] >= Dd) continue;
        if (side[v] == 0) s0[n0++] = v;
        else s1[n1++] = v;
    }
    if (n0 == 0 || n1 == 0) return 0;
    for (int t = 0; t < 40; t++) {
        int a = s0[rndint(n0)], b = s1[rndint(n1)];
        if (!has_edge(a, b)) {
            link_e(a, b);
            return 1;
        }
    }
    return 0;
}

/* Pick edges (a1,b1), (a2,b2) with a's on side 0 whose switch to (a1,b2), (a2,b1) is legal. */
static int pick_switch(int *a1, int *b1, int *a2, int *b2) {
    int x = -1, y = -1;
    for (int t = 0; t < 64 && x < 0; t++) {
        int v = rndint(N);
        if (side[v] == 0 && deg[v] > 0) x = v;
    }
    for (int t = 0; t < 64 && y < 0; t++) {
        int v = rndint(N);
        if (side[v] == 0 && deg[v] > 0 && v != x) y = v;
    }
    if (x < 0 || y < 0) return 0;
    int u = adj[x][rndint(deg[x])];
    int w = adj[y][rndint(deg[y])];
    if (u == w || has_edge(x, w) || has_edge(y, u)) return 0;
    *a1 = x;
    *b1 = u;
    *a2 = y;
    *b2 = w;
    return 1;
}

static void take_snapshot(void) {
    snapN = N;
    snapE = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++) {
            int u = adj[v][k];
            if (u > v && snapE < MAXE) {
                snapU[snapE] = v;
                snapV[snapE] = u;
                snapE++;
            }
        }
}

static void load_snapshot(void) {
    for (int v = 0; v < N; v++) {
        deg[v] = 0;
        memset(am[v], 0, sizeof(Row));
    }
    N = snapN;
    WN = (N + 63) / 64;
    for (int e = 0; e < snapE; e++) link_e(snapU[e], snapV[e]);
}

int main(int argc, char **argv) {
    static int q[MAXN];
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
    if (n <= 0 || n > MAXN - 8 || Dist < 2 || Dd < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= Dd || deg[v] >= Dd || has_edge(u, v)) continue;
        link_e(u, v);
    }

    for (int v = 0; v < N; v++) side[v] = -1;
    int bad = 0;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    q[t++] = v;
                } else if (side[v] == side[u]) {
                    bad = 1;
                }
            }
        }
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    WN = (N + 63) / 64;
    long cur = full_cost();
    if (cur == 0) take_snapshot();

    double t_end = now() + budget;
    const long STUCK = 60000;
    const long EPOCH = 25000;
    const double T0 = 2.0, T1 = 0.08;
    long since = 0;
    int fails_add = 0;

    while (now() < t_end) {
        if (cur == 0) {
            take_snapshot();
            since = 0;
            if (!add_vertex()) {
                if (++fails_add > 20) break;
                continue;
            }
            fails_add = 0;
            cur = full_cost();
            continue;
        }
        since++;
        if (since > STUCK) {
            load_snapshot();
            cur = full_cost();
            since = 0;
            continue;
        }
        if (rndint(12) < 2) {
            if (do_add()) cur = full_cost();
            continue;
        }
        int a1, b1, a2, b2;
        if (!pick_switch(&a1, &b1, &a2, &b2)) continue;
        unlink_e(a1, b1);
        unlink_e(a2, b2);
        link_e(a1, b2);
        link_e(a2, b1);
        long nc = full_cost();
        long delta = nc - cur;
        double frac = (double)(since % EPOCH) / (double)EPOCH;
        double T = T0 * pow(T1 / T0, frac);
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            unlink_e(a1, b2);
            unlink_e(a2, b1);
            link_e(a1, b1);
            link_e(a2, b2);
        }
    }

    printf("%d %d\n", snapN, snapE);
    for (int e = 0; e < snapE; e++) printf("%d %d\n", snapU[e], snapV[e]);
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
# Build: best start, then the annealing engine, with safe fallbacks.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    end = t0 + 0.80 * time_limit
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
    if lib.is_valid(fallback[0], fallback[1], d, D):
        starts.append(fallback)
    if not starts:
        return 1, []
    best = max(starts, key=lambda g: g[0])

    # Already at the Moore bound: nothing to gain, return immediately.
    if best[0] >= lib.moore_bound(d, D):
        return best

    remaining = end - time.monotonic()
    if remaining > 4.0:
        budget = remaining - 2.0
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed * 31 + 7, f"{budget:.2f}"],
                             stdin_graph=best, timeout=budget + 8.0)
            n1, e1 = lib.parse_graph_text(text)
            if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                best = (n1, e1)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
