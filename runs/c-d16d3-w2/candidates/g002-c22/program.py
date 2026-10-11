import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing on bipartite graphs with a fixed side per vertex.
# Cost = number of unordered pairs at distance > D (unreachable counts as bad).
# Moves: rewire (keeps degrees, bipartite), add an edge between spare vertices,
# remove an edge. Whenever cost reaches 0 the state is saved and one isolated
# vertex is appended, so the order grows while staying valid. If no cost
# improvement happens for a long stretch, the engine reloads the best saved
# valid graph and grows again. Python re-checks the output with lib.is_valid.
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
static int bestSide[MAXN];
static int best_n = 0, best_m = 0;
static uint64_t rs = 1;
static int vis[MAXN];
static int qbuf[MAXN];

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
    return (int)(bad / 2);
}

static void save_best(void) {
    int m = 0;
    for (int u = 0; u < n; u++) {
        for (int i = 0; i < deg[u]; i++) {
            int v = nb[u][i];
            if (v > u && m < MAXE) { bestU[m] = u; bestV[m] = v; m++; }
        }
    }
    for (int u = 0; u < n; u++) bestSide[u] = side[u];
    best_n = n; best_m = m;
}

static void load_best(void) {
    for (int u = 0; u < n; u++) {
        for (int i = 0; i < deg[u]; i++) adjm[u][nb[u][i]] = 0;
        deg[u] = 0;
    }
    n = best_n;
    for (int u = 0; u < n; u++) side[u] = bestSide[u];
    for (int i = 0; i < best_m; i++) add_edge(bestU[i], bestV[i]);
}

static int color_graph(void) {
    int iso = 0;
    for (int v = 0; v < n; v++) vis[v] = 0;
    for (int s = 0; s < n; s++) {
        if (vis[s]) continue;
        if (deg[s] == 0) { vis[s] = 1; side[s] = (iso++) & 1; continue; }
        vis[s] = 1; side[s] = 0;
        int qh = 0, qt = 0;
        qbuf[qt++] = s;
        while (qh < qt) {
            int u = qbuf[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (!vis[v]) { vis[v] = 1; side[v] = 1 - side[u]; qbuf[qt++] = v; }
                else if (side[v] == side[u]) return 0;
            }
        }
    }
    return 1;
}

/* a--b becomes a--w, with w on the same side as b. */
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

    if (!(n >= 2 && n <= MAXN - 256 && d >= 1 && d <= DCAP && D >= 1)) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m0; i++) {
        int u = iu[i], v = iv[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || adjm[u][v] ||
            deg[u] >= d || deg[v] >= d) continue;
        add_edge(u, v);
    }
    if (!color_graph()) { printf("0 0\n"); return 0; }

    int cur_bad = bad_pairs();
    int have_best = 0;
    if (cur_bad == 0) { save_best(); have_best = 1; }
    int minbad = cur_bad;
    long it = 0, lastimp = 0;
    const long STALL = 120000;

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
            side[n] = (int)(rnd() & 1);
            deg[n] = 0;
            n++;
            cur_bad = bad_pairs();
            minbad = cur_bad;
            lastimp = it;
            continue;
        }

        if (have_best && it - lastimp > STALL) {
            load_best();
            cur_bad = bad_pairs();
            minbad = cur_bad;
            lastimp = it;
            continue;
        }

        double phase = (double)(it % 60000) / 60000.0;
        double T = 0.15 + 1.2 * (1.0 - phase) * (1.0 - phase);

        int kind = 0, ua = 0, ub = 0, uw = 0, applied = 0;
        int r = rint_(100);
        if (r < 55) { kind = 0; applied = move_rewire(&ua, &ub, &uw); }
        else if (r < 90) { kind = 1; applied = move_add(&ua, &ub); }
        else { kind = 2; applied = move_remove(&ua, &ub); }
        if (!applied) continue;

        int nbad = bad_pairs();
        int delta = nbad - cur_bad;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur_bad = nbad;
            if (cur_bad < minbad) { minbad = cur_bad; lastimp = it; }
        } else {
            if (kind == 0) { del_edge(ua, uw); add_edge(ua, ub); }
            else if (kind == 1) { del_edge(ua, ub); }
            else { add_edge(ua, ub); }
        }
    }

    if (!have_best) {
        printf("0 0\n");
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
# Start from the incidence graph of PG(2, q). Points have spare degree s = d-q-1
# on the side of lines, and lines have spare degree s on the side of points.
# Choose SA (points) and SB (lines) so that:
#   every line lies on <= s points of SA,
#   every point lies on <= s lines of SB.
# Add one A-vertex per point of SA (joined to the q+1 lines through it), and one
# B-vertex per line of SB (joined to the q+1 points on it).
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
    """Randomized greedy choice so that every target is hit at most s times."""
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
    """Old PG incidence plus one new A-vertex per point of SA and one new B-vertex per line of SB."""
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
    """Return (n, edges) candidates from PG(2, q) plus arc-extension vertices, q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 0:
            continue
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 200, deadline) if s >= 1 else []
        SB = _greedy_side(m, s, line_points, rng, 200, deadline) if s >= 1 else []
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


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used for D == 4.
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
# C annealing wrapper.
# ----------------------------------------------------------------------------

def _c_grow(graph, d, D, seed, budget):
    """Run the C annealer from a valid graph; return (n, edges) or None on failure."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=graph, timeout=budget + 6.0)
        return lib.parse_graph_text(out)
    except Exception:
        return None


# ----------------------------------------------------------------------------
# Driver.
#   D == 3: best arc-extended projective plane graph as the start.
#   D == 4: generalized quadrangle W(q) as the start.
#   else  : K_{d,d} as the start.
# The C engine then grows the best valid graph for most of the time budget.
# Every result is checked with lib.is_valid; K_{d,d} (diameter 2) is the
# always-valid fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))

    rng = random.Random(seed * 7919 + d)
    try:
        if D == 3:
            for g in _arc_extensions(d, t0 + 0.2 * time_limit, rng):
                consider(g)
        elif D == 4:
            consider(_best_gq(d))
    except Exception:
        pass

    end = t0 + 0.85 * time_limit - 2.0
    budget = end - time.monotonic()
    if budget >= 1.0 and d <= 64:
        consider(_c_grow(best, d, D, seed, budget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
