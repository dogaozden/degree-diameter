import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing on bipartite graphs with a fixed vertex set.
# Cost = number of unordered pairs at distance > D (unreachable counts as bad).
# Moves keep max degree <= d and bipartiteness (sides are fixed per vertex).
#
# NEW: targeted repair move. Each accepted state remembers one bad pair (u, v).
# The move adds edges that create a short path between u and v:
#   - opposite sides: edge u-v if both have spare degree, else an edge a-b with
#     a in N(u), b in N(v) (path u-a-b-v of length 3);
#   - same side: a new common neighbour w on the other side (path u-w-v).
# Additions never break bipartiteness and only use spare degree, so they are
# a cheap way to convert bad pairs into good ones.
#
# Whenever the cost reaches 0 the engine saves the graph and appends one more
# isolated vertex, so it grows the order while staying valid. It always prints
# a graph; Python re-checks it with lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1600
#define MAXW 25
#define DCAP 64
#define MAXE (MAXN * DCAP)

static int n, d, D;
static int nb[MAXN][DCAP];
static int deg[MAXN];
static int side[MAXN];
static unsigned char adjm[MAXN][MAXN];
static uint64_t RA[MAXN][MAXW];
static uint64_t RB[MAXN][MAXW];
static int bestU[MAXE], bestV[MAXE];
static int best_n = 0, best_m = 0;
static uint64_t rs = 1;
static int vis[MAXN];
static int bu = -1, bv = -1;   /* bad pair of the accepted state */
static int tu = -1, tv = -1;   /* bad pair found by the last bad_pairs call */
static int nadd = 0;           /* edges added by the last targeted move */
static int addU[2], addV[2];

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int popc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static void add_edge(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
    adjm[u][v] = 1; adjm[v][u] = 1;
}
static void rm_one(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nb[u][i] == v) { nb[u][i] = nb[u][deg[u] - 1]; deg[u]--; return; }
    }
}
static void del_edge(int u, int v) {
    rm_one(u, v); rm_one(v, u);
    adjm[u][v] = 0; adjm[v][u] = 0;
}

static int bad_pairs(void) {
    int W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        memset(RA[v], 0, sizeof(uint64_t) * (size_t)W);
        RA[v][v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t (*cur)[MAXW] = RA;
    uint64_t (*nxt)[MAXW] = RB;
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < n; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s = cur[nb[v][i]];
                for (int w = 0; w < W; w++) nxt[v][w] |= s[w];
            }
        }
        uint64_t (*tmp)[MAXW] = cur;
        cur = nxt;
        nxt = tmp;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        bad += n - c;
    }
    /* NEW: record one unreachable pair, scanning from a random vertex. */
    tu = -1; tv = -1;
    if (bad > 0) {
        int start = rint_(n);
        for (int k = 0; k < n && tu < 0; k++) {
            int v = (start + k) % n;
            for (int wd = 0; wd < W && tu < 0; wd++) {
                uint64_t x = ~cur[v][wd];
                if (wd == W - 1 && (n & 63)) x &= (1ULL << (n & 63)) - 1ULL;
                for (int b = 0; b < 64 && x; b++) {
                    if ((x >> b) & 1ULL) { tu = v; tv = wd * 64 + b; break; }
                }
            }
        }
    }
    return (int)(bad / 2);
}

static void save_best(void) {
    int m = 0;
    for (int u = 0; u < n; u++) {
        for (int i = 0; i < deg[u]; i++) {
            if (nb[u][i] > u && m < MAXE) {
                bestU[m] = u; bestV[m] = nb[u][i]; m++;
            }
        }
    }
    best_n = n; best_m = m;
}

static int color_graph(void) {
    static int queue[MAXN];
    int iso = 0;
    for (int v = 0; v < n; v++) vis[v] = 0;
    for (int s = 0; s < n; s++) {
        if (vis[s]) continue;
        if (deg[s] == 0) { vis[s] = 1; side[s] = (iso++) & 1; continue; }
        vis[s] = 1; side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (!vis[v]) { vis[v] = 1; side[v] = 1 - side[u]; queue[qt++] = v; }
                else if (side[v] == side[u]) return 0;
            }
        }
    }
    return 1;
}

/* a -- b  becomes  a -- w, where w is on the same side as b. */
static int move_rewire(int *ua, int *ub, int *uw) {
    int a = -1;
    for (int t = 0; t < 64 && a < 0; t++) {
        int c = rint_(n);
        if (deg[c] > 0) a = c;
    }
    if (a < 0) return 0;
    int b = nb[a][rint_(deg[a])];
    int w = -1;
    for (int t = 0; t < 64; t++) {
        int c = rint_(n);
        if (c != b && side[c] == side[b] && deg[c] < d && !adjm[a][c]) { w = c; break; }
    }
    if (w < 0) return 0;
    del_edge(a, b);
    add_edge(a, w);
    *ua = a; *ub = b; *uw = w;
    return 1;
}

static int move_add(int *ua, int *ub) {
    int x = -1, y = -1;
    for (int t = 0; t < 64; t++) {
        int c = rint_(n);
        if (deg[c] < d) { x = c; break; }
    }
    if (x < 0) return 0;
    for (int t = 0; t < 64; t++) {
        int c = rint_(n);
        if (c != x && side[c] != side[x] && deg[c] < d && !adjm[x][c]) { y = c; break; }
    }
    if (y < 0) return 0;
    add_edge(x, y);
    *ua = x; *ub = y;
    return 1;
}

static int move_remove(int *ua, int *ub) {
    int a = -1;
    for (int t = 0; t < 64 && a < 0; t++) {
        int c = rint_(n);
        if (deg[c] > 0) a = c;
    }
    if (a < 0) return 0;
    int b = nb[a][rint_(deg[a])];
    del_edge(a, b);
    *ua = a; *ub = b;
    return 1;
}

/* NEW: targeted repair move around the remembered bad pair (bu, bv). */
static int move_target(void) {
    int u = bu, v = bv;
    nadd = 0;
    if (u < 0 || v < 0) return 0;
    if (side[u] != side[v]) {
        if (deg[u] < d && deg[v] < d && !adjm[u][v]) {
            add_edge(u, v);
            addU[0] = u; addV[0] = v; nadd = 1;
            return 1;
        }
        if (deg[u] == 0 || deg[v] == 0) return 0;
        for (int t = 0; t < 64; t++) {
            int a = nb[u][rint_(deg[u])];
            int b = nb[v][rint_(deg[v])];
            if (a != b && deg[a] < d && deg[b] < d && !adjm[a][b]) {
                add_edge(a, b);
                addU[0] = a; addV[0] = b; nadd = 1;
                return 1;
            }
        }
        return 0;
    } else {
        if (deg[u] >= d || deg[v] >= d) return 0;
        for (int t = 0; t < 256; t++) {
            int w = rint_(n);
            if (side[w] != side[u] && deg[w] < d && !adjm[u][w] && !adjm[v][w]) {
                add_edge(u, w);
                add_edge(v, w);
                addU[0] = u; addV[0] = w; addU[1] = v; addV[1] = w; nadd = 2;
                return 1;
            }
        }
        return 0;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    clock_t t0 = clock();

    int m0 = 0;
    if (scanf("%d %d", &n, &m0) != 2 || n < 0 || m0 < 0) { printf("0 0\n"); return 0; }
    int *iu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *iv = malloc(sizeof(int) * (size_t)(m0 + 1));
    if (!iu || !iv) return 1;
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &iu[i], &iv[i]) != 2) { m0 = i; break; }
    }

    int ok = (n >= 2 && n <= MAXN - 256 && d >= 1 && d <= DCAP && D >= 1);
    if (ok) {
        for (int i = 0; i < m0 && ok; i++) {
            int u = iu[i], v = iv[i];
            if (u < 0 || v < 0 || u >= n || v >= n || u == v || adjm[u][v] ||
                deg[u] >= d || deg[v] >= d) {
                ok = 0;
            } else {
                add_edge(u, v);
            }
        }
    }
    if (ok) ok = color_graph();
    if (!ok) {
        printf("%d %d\n", n, m0);
        for (int i = 0; i < m0; i++) printf("%d %d\n", iu[i], iv[i]);
        return 0;
    }

    int cur_bad = bad_pairs();
    bu = tu; bv = tv;
    int have_best = 0;
    if (cur_bad == 0) { save_best(); have_best = 1; }

    long it = 0;
    for (;;) {
        if ((it & 127) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > tl) break;
        }
        it++;

        if (cur_bad == 0) {
            save_best();
            have_best = 1;
            if (n >= MAXN - 2) break;
            side[n] = n & 1;
            deg[n] = 0;
            n++;
            cur_bad = bad_pairs();
            bu = tu; bv = tv;
            continue;
        }

        double phase = (double)(it % 60000) / 60000.0;
        double T = 0.15 + 1.2 * (1.0 - phase) * (1.0 - phase);

        int kind = 0, ua = 0, ub = 0, uw = 0, applied = 0;
        int r = rint_(100);
        if (r < 35) { kind = 0; applied = move_rewire(&ua, &ub, &uw); }
        else if (r < 50) { kind = 1; applied = move_add(&ua, &ub); }
        else if (r < 60) { kind = 2; applied = move_remove(&ua, &ub); }
        else { kind = 3; applied = move_target(); }
        if (!applied) continue;

        int nbad = bad_pairs();
        int delta = nbad - cur_bad;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur_bad = nbad;
            bu = tu; bv = tv;
        } else {
            if (kind == 0) { del_edge(ua, uw); add_edge(ua, ub); }
            else if (kind == 1) { del_edge(ua, ub); }
            else if (kind == 2) { add_edge(ua, ub); }
            else {
                for (int i = 0; i < nadd; i++) del_edge(addU[i], addV[i]);
            }
            /* restore the remembered pair of the accepted state */
            bad_pairs();
            bu = tu; bv = tv;
            /* the accepted cost is unchanged, only the pair choice was refreshed */
        }
    }

    if (!have_best) {
        printf("%d %d\n", n, m0);
        for (int i = 0; i < m0; i++) printf("%d %d\n", iu[i], iv[i]);
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). With d >= q+1 each vertex has
# spare capacity s = d - q - 1. Choose S so that every line holds <= s points
# of S and every point lies on <= s lines indexed by S. Add an A-vertex joined
# to the q+1 lines through each P in S, and a B-vertex joined to the q+1 points
# on each line j in S.
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


def _swap_improve(S, s, m, point_lines, line_points, rng, deadline, iters):
    """Local search that grows the arc set S by ejection moves.

    Pick a random outside point P. Collect the members of S that block P (they
    use a saturated line through P or a saturated point of P). If at most two
    members block P, eject them and insert P when the loads stay feasible.
    Equal-size moves are always accepted, and a loss of one is accepted with
    probability 0.1 to escape plateaus. The best set seen is returned.
    """
    cur = list(S)
    inS = set(cur)
    best = list(cur)
    pl_set = [set(point_lines[X]) for X in range(m)]
    lp_set = [set(line_points[X]) for X in range(m)]
    for _ in range(iters):
        if time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if P in inS:
            continue
        cl = [0] * m
        cp = [0] * m
        for X in cur:
            for L in point_lines[X]:
                cl[L] += 1
            for Q in line_points[X]:
                cp[Q] += 1
        Lset = set(point_lines[P])
        Qset = set(line_points[P])
        Lfull = {L for L in Lset if cl[L] >= s}
        Qfull = {Q for Q in Qset if cp[Q] >= s}
        block = [X for X in cur if (pl_set[X] & Lfull) or (lp_set[X] & Qfull)]
        if len(block) > 2:
            continue
        if not block and rng.random() > 0.5:
            continue
        bset = set(block)
        new = [X for X in cur if X not in bset] + [P]
        if not _loads_ok(new, s, m, point_lines, line_points):
            continue
        if len(new) >= len(cur) or rng.random() < 0.1:
            cur = new
            inS = set(cur)
            if len(cur) > len(best):
                best = list(cur)
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
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            g = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
            g = _swap_improve(g, s, m, point_lines, line_points, rng,
                              min(deadline, time.monotonic() + 2.0), iters=6000)
            cands.append(g)
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cs = _swap_improve(cs, s, m, point_lines, line_points, rng,
                                   min(deadline, time.monotonic() + 1.0), iters=3000)
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    end = t_start + 0.8 * time_limit - 1.0

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = (g[0], g[1])

    # Arc-extended projective plane graphs (valid for D >= 3).
    if D >= 3 and time.monotonic() < end:
        cands = _arc_extensions(d, end, random.Random(seed * 7919 + d))
        for g in sorted(cands, key=lambda t: -t[0]):
            consider(g)

    # Targeted-repair annealing for D = 3: add vertices to the best graph.
    if D == 3:
        bound = lib.moore_bound(d, D)
        cbudget = end - time.monotonic()
        if best[0] < bound and cbudget > 3.0:
            try:
                start_graph = (best[0] + 1, list(best[1]))  # one extra isolated vertex
                out = lib.run_c(C_SOURCE, [d, D, seed, round(cbudget - 1.5, 2)],
                                stdin_graph=start_graph, timeout=cbudget + 5)
                consider(lib.parse_graph_text(out))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
