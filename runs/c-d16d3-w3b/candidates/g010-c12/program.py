import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: degree-preserving bipartite 2-switch annealing with vertex growth.
#
# State: a bipartite graph with max degree d and diameter <= D.
# Cost = number of unordered vertex pairs at distance > D (0 means valid).
# Moves: pick edges (a1,b1), (a2,b2) with a's on side 0 and b's on side 1,
#        replace them by (a1,b2), (a2,b1). Degrees and bipartiteness are kept.
# Growth: when cost is 0, snapshot the graph, add one vertex on a random side,
#        and fill spare degree greedily (any non-adjacent opposite pair with
#        spare degree gets an edge; this never increases cost).
# Stalls: if the cost does not improve for STALL moves, reload the last valid
#        snapshot and grow again with new random fill. Output the last valid
#        snapshot found before the CPU budget ends.
# ----------------------------------------------------------------------------

C_SWITCH = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXD 64
#define MAXW (MAXN / 64)
#define MAXE (MAXN * MAXD)
#define STALL 30000

static int n, d, D, W;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static unsigned char am[MAXN][MAXN];
static int col[MAXN];
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static int bn, bm;
static int bu[MAXE], bv[MAXE];

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static double urand(void) { return (double)rnd() / 4294967296.0; }

static int pc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void list_remove(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void edge_add(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
    am[u][v] = 1;
    am[v][u] = 1;
}

static void edge_remove(int u, int v) {
    list_remove(u, v);
    list_remove(v, u);
    am[u][v] = 0;
    am[v][u] = 0;
}

static void color_all(void) {
    static int q[MAXN];
    for (int s = 0; s < n; s++) col[s] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int u = q[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    q[qt++] = v;
                }
            }
        }
    }
}

static void load_graph(int N, int M, const int *eu, const int *ev) {
    n = N;
    memset(deg, 0, sizeof deg);
    memset(am, 0, sizeof am);
    for (int i = 0; i < M; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (am[u][v] || deg[u] >= d || deg[v] >= d) continue;
        edge_add(u, v);
    }
    color_all();
}

static void take_snapshot(void) {
    bn = n;
    bm = 0;
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u && bm < MAXE) {
                bu[bm] = u;
                bv[bm] = adj[u][i];
                bm++;
            }
}

static void restore(void) { load_graph(bn, bm, bu, bv); }

// Number of unordered pairs at distance > D (unreachable pairs included).
static long bad_count(void) {
    W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) reach[v][w] = 0;
        reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = reach[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= reach[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) reach[v][w] = nxt[v][w];
    }
    long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc(reach[v][w]);
        tot += n - c;
    }
    return tot / 2;
}

// Add an edge between every non-adjacent opposite-side pair with spare degree.
static void fill_deficits(void) {
    static int A[MAXN], B[MAXN];
    int na = 0, nb = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] >= d) continue;
        if (col[v] == 0) A[na++] = v;
        else B[nb++] = v;
    }
    for (int i = na - 1; i > 0; i--) {
        int j = (int)(rnd() % (uint32_t)(i + 1));
        int t = A[i]; A[i] = A[j]; A[j] = t;
    }
    for (int i = nb - 1; i > 0; i--) {
        int j = (int)(rnd() % (uint32_t)(i + 1));
        int t = B[i]; B[i] = B[j]; B[j] = t;
    }
    for (int i = 0; i < na; i++) {
        int a = A[i];
        for (int j = 0; j < nb && deg[a] < d; j++) {
            int b = B[j];
            if (deg[b] < d && !am[a][b]) edge_add(a, b);
        }
    }
}

static void grow(void) {
    if (n >= MAXN - 1) return;
    int w = n;
    n++;
    deg[w] = 0;
    col[w] = (int)(rnd() & 1u);
    fill_deficits();
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2 || N0 < 1 || N0 >= MAXN - 1) {
        printf("0 0\n");
        return 0;
    }
    static int eu[MAXE], ev[MAXE];
    int ne = 0;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (ne < MAXE) { eu[ne] = u; ev[ne] = v; ne++; }
    }

    load_graph(N0, ne, eu, ev);
    long cur = bad_count();
    int have_valid = 0;
    take_snapshot();
    if (cur == 0) {
        have_valid = 1;
        grow();
        cur = bad_count();
    }

    clock_t t0 = clock();
    long it = 0, stall = 0, phase_best = cur;
    while (1) {
        if ((it & 127) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        it++;

        if (cur == 0) {
            take_snapshot();
            have_valid = 1;
            if (n >= MAXN - 1) break;
            grow();
            cur = bad_count();
            stall = 0;
            phase_best = cur;
            continue;
        }
        if (stall > STALL) {
            if (have_valid) {
                restore();
                grow();
            }
            cur = bad_count();
            stall = 0;
            phase_best = cur;
            continue;
        }

        int u = (int)(rnd() % (uint32_t)n);
        int u2 = (int)(rnd() % (uint32_t)n);
        if (deg[u] == 0 || deg[u2] == 0) continue;
        int v = adj[u][rnd() % (uint32_t)deg[u]];
        int v2 = adj[u2][rnd() % (uint32_t)deg[u2]];
        int a1 = (col[u] == 0) ? u : v;
        int b1 = (col[u] == 0) ? v : u;
        int a2 = (col[u2] == 0) ? u2 : v2;
        int b2 = (col[u2] == 0) ? v2 : u2;
        if (a1 == a2 || b1 == b2) continue;
        if (am[a1][b2] || am[a2][b1]) continue;

        edge_remove(a1, b1);
        edge_remove(a2, b2);
        edge_add(a1, b2);
        edge_add(a2, b1);

        long nc = bad_count();
        long delta = nc - cur;
        int acc = (delta <= 0);
        if (!acc) {
            double T = 0.3 + 0.9 * (double)(stall % 5000) / 5000.0;
            acc = urand() < exp(-(double)delta / T);
        }
        if (acc) {
            cur = nc;
        } else {
            edge_remove(a1, b2);
            edge_remove(a2, b1);
            edge_add(a1, b1);
            edge_add(a2, b2);
        }
        if (cur < phase_best) {
            phase_best = cur;
            stall = 0;
        } else {
            stall++;
        }
    }

    printf("%d %d\n", bn, bm);
    for (int i = 0; i < bm; i++) printf("%d %d\n", bu[i], bv[i]);
    return 0;
}
"""


def _c_switch(graph, d, D, seed, budget):
    """Run the switch-annealing engine from graph; return (n, edges) or None on failure."""
    if graph is None or budget < 0.5 or d > 64:
        return None
    try:
        out = lib.run_c(C_SWITCH, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 10.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Every old vertex
# has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# A-side: a set SA of points, each gets a new vertex joined to its q+1 lines.
#         Each line holds <= s points of SA.
# B-side: a set SB of lines, each gets a new vertex joined to its q+1 points.
#         Each point lies on <= s lines of SB.
# Diameter stays 3 for any SA, SB.
# ----------------------------------------------------------------------------

_LS_ITERS = 30000


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
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy for the load-constrained set problem."""
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


def _local_search(m, s, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the load-constrained set problem."""
    if s < 1:
        return list(S)
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= s:
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
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
    """Return (n, edges) arc-extended candidates for each prime power q with q + 1 <= d."""
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for q in qs:
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

        SA = _local_search(m, s, point_lines, SA, rng, deadline, _LS_ITERS)
        SB = _local_search(m, s, line_points, SB, rng, deadline, _LS_ITERS)

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Driver. Time plan (fractions of time_limit):
#   D = 3: 0.00-0.20 arc-extended PG graphs (Python local search)
#          0.20-0.90 switch annealing with growth, 60% on the best arc graph
#          and the rest on the second one.
#   D >= 4: switch annealing with growth from K_{d,d} (valid for D >= 2).
# Every returned graph is checked with lib.is_valid; K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    def el():
        return time.monotonic() - start

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    best = fallback

    starts = []
    if D == 3:
        cands = _arc_extensions(d, start + 0.20 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for g in cands[:2]:
            if lib.is_valid(g[0], g[1], d, D):
                starts.append(g)
    if starts:
        best = max(starts, key=lambda g: g[0])
    else:
        starts = [fallback]

    pool = sorted(starts, key=lambda g: -g[0])[:2]
    for i, g in enumerate(pool):
        remaining = 0.90 * time_limit - el()
        if remaining < 0.5:
            break
        if len(pool) > 1 and i == 0:
            share = 0.6 * remaining
        else:
            share = remaining
        res = _c_switch(g, d, D, seed + 31 * i, share)
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
