import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing on bipartite graphs with a fixed side assignment.
#
# Cost = number of unordered vertex pairs at distance > D (unreachable pairs count).
# Moves keep max degree <= d and bipartiteness: rewire, add, remove, and a
# degree-preserving double-edge swap. Whenever the cost reaches 0 the current
# graph is saved and one new vertex is grown: it is joined to up to d spare
# vertices on the opposite side, choosing the wiring (among a few random tries)
# with the fewest bad pairs. Every CYCLE iterations the search restarts from
# the best valid graph, so each restart grows it differently.
# Output is always a valid graph or "0 0"; Python re-checks it with lib.is_valid.
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
#define CYCLE 80000

static int n, d, D;
static int nb[MAXN][DCAP];
static int deg[MAXN];
static int side[MAXN];
static unsigned char adjm[MAXN][MAXN];
static uint64_t RA[MAXN][MAXW];
static uint64_t RB[MAXN][MAXW];
static int bestU[MAXE], bestV[MAXE];
static int best_n = 0, best_m = 0, have_best = 0;
static uint64_t rs = 1;
static int vis[MAXN];
static int queue_[MAXN];
static int cand[MAXN];

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
            if (nb[u][i] > u && m < MAXE) { bestU[m] = u; bestV[m] = nb[u][i]; m++; }
        }
    }
    best_n = n; best_m = m; have_best = 1;
}

static void clear_graph(void) {
    for (int u = 0; u < n; u++) {
        for (int i = 0; i < deg[u]; i++) adjm[u][nb[u][i]] = 0;
        deg[u] = 0;
    }
}

static void load_best(void) {
    clear_graph();
    n = best_n;
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
        queue_[qt++] = s;
        while (qh < qt) {
            int u = queue_[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (!vis[v]) { vis[v] = 1; side[v] = 1 - side[u]; queue_[qt++] = v; }
                else if (side[v] == side[u]) return 0;
            }
        }
    }
    return 1;
}

/* grow one vertex, choosing among a few random wirings the one with fewest bad pairs */
static void grow(void) {
    int x = n;
    n++;
    deg[x] = 0;
    int bestbad = 1 << 30, bestk = 0, bests = -1;
    static int bestset[DCAP];
    for (int tr = 0; tr < 12; tr++) {
        int s = tr & 1;
        int nc = 0;
        for (int v = 0; v < x; v++)
            if (side[v] != s && deg[v] < d) cand[nc++] = v;
        if (nc == 0) continue;
        for (int i = 0; i < nc; i++) {
            int j = i + rint_(nc - i);
            int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
        }
        int k = nc < d ? nc : d;
        side[x] = s;
        for (int i = 0; i < k; i++) add_edge(x, cand[i]);
        int b = bad_pairs();
        if (b < bestbad) {
            bestbad = b; bestk = k; bests = s;
            for (int i = 0; i < k; i++) bestset[i] = cand[i];
        }
        for (int i = 0; i < k; i++) del_edge(x, cand[i]);
    }
    if (bests < 0) { side[x] = rint_(2); return; }
    side[x] = bests;
    for (int i = 0; i < bestk; i++) add_edge(x, bestset[i]);
}

/* a-b becomes a-w, with w on the side of b */
static int move_rewire(int *p) {
    int a = -1;
    for (int t = 0; t < 64 && a < 0; t++) { int c = rint_(n); if (deg[c] > 0) a = c; }
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
    p[0] = a; p[1] = b; p[2] = w;
    return 1;
}

static int move_add(int *p) {
    int x = -1, y = -1;
    for (int t = 0; t < 64; t++) { int c = rint_(n); if (deg[c] < d) { x = c; break; } }
    if (x < 0) return 0;
    for (int t = 0; t < 64; t++) {
        int c = rint_(n);
        if (c != x && side[c] != side[x] && deg[c] < d && !adjm[x][c]) { y = c; break; }
    }
    if (y < 0) return 0;
    add_edge(x, y);
    p[0] = x; p[1] = y;
    return 1;
}

static int move_remove(int *p) {
    int a = -1;
    for (int t = 0; t < 64 && a < 0; t++) { int c = rint_(n); if (deg[c] > 0) a = c; }
    if (a < 0) return 0;
    int b = nb[a][rint_(deg[a])];
    del_edge(a, b);
    p[0] = a; p[1] = b;
    return 1;
}

/* a-b, c-dd become a-dd, c-b (a and c on the same side; degrees preserved) */
static int move_swap(int *p) {
    int a = -1;
    for (int t = 0; t < 64 && a < 0; t++) { int c = rint_(n); if (deg[c] > 0) a = c; }
    if (a < 0) return 0;
    int b = nb[a][rint_(deg[a])];
    int c = -1;
    for (int t = 0; t < 64; t++) {
        int z = rint_(n);
        if (z != a && side[z] == side[a] && deg[z] > 0) { c = z; break; }
    }
    if (c < 0) return 0;
    int dd = nb[c][rint_(deg[c])];
    if (dd == b || adjm[a][dd] || adjm[c][b]) return 0;
    del_edge(a, b);
    del_edge(c, dd);
    add_edge(a, dd);
    add_edge(c, b);
    p[0] = a; p[1] = b; p[2] = c; p[3] = dd;
    return 1;
}

static void undo(int kind, const int *p) {
    if (kind == 0) { del_edge(p[0], p[2]); add_edge(p[0], p[1]); }
    else if (kind == 1) { del_edge(p[0], p[1]); }
    else if (kind == 2) { add_edge(p[0], p[1]); }
    else {
        del_edge(p[0], p[3]);
        del_edge(p[2], p[1]);
        add_edge(p[0], p[1]);
        add_edge(p[2], p[3]);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd();
    clock_t t0 = clock();

    int m0 = 0;
    if (scanf("%d %d", &n, &m0) != 2 || m0 < 0) { printf("0 0\n"); return 0; }
    if (n < 2 || n > MAXN - 256 || d < 1 || d > DCAP || D < 1 || m0 > MAXE) {
        printf("0 0\n");
        return 0;
    }
    int *iu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *iv = malloc(sizeof(int) * (size_t)(m0 + 1));
    if (!iu || !iv) { printf("0 0\n"); return 0; }
    int mm = 0;
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &iu[i], &iv[i]) != 2) break;
        mm++;
    }
    for (int i = 0; i < mm; i++) {
        int u = iu[i], v = iv[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || adjm[u][v] ||
            deg[u] >= d || deg[v] >= d) continue;
        add_edge(u, v);
    }
    free(iu);
    free(iv);
    if (!color_graph()) { printf("0 0\n"); return 0; }

    int cur_bad = bad_pairs();
    if (cur_bad == 0) save_best();

    long it = 0;
    for (;;) {
        if ((it & 127) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > tl) break;
        }
        it++;

        if (cur_bad == 0) {
            save_best();
            if (n >= MAXN - 2) break;
            grow();
            cur_bad = bad_pairs();
            continue;
        }
        if (have_best && it % CYCLE == 0) {
            load_best();
            cur_bad = bad_pairs();
            continue;
        }

        double phase = (double)(it % CYCLE) / (double)CYCLE;
        double T = 0.15 + 1.2 * (1.0 - phase) * (1.0 - phase);

        int p[4] = {0, 0, 0, 0};
        int kind, applied;
        int r = rint_(100);
        if (r < 40) { kind = 0; applied = move_rewire(p); }
        else if (r < 55) { kind = 1; applied = move_add(p); }
        else if (r < 65) { kind = 2; applied = move_remove(p); }
        else { kind = 3; applied = move_swap(p); }
        if (!applied) continue;

        int nbad = bad_pairs();
        int delta = nbad - cur_bad;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur_bad = nbad;
        } else {
            undo(kind, p);
        }
    }

    if (!have_best) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q), which is (q+1)-regular. Spare
# capacity is s = d - q - 1. Choose point sets SA and SB. Each SA point gets a
# new point-side vertex joined to the q+1 lines through it; each SB line gets a
# new line-side vertex joined to the q+1 points on it. Validity needs every line
# to meet SA in <= s points and every point to lie on <= s lines of SB (and the
# symmetric loads). For d = 16, q = 13 this reproduces the record 394 = 2*(183+14).
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
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new point-side vertex per SA point and one new line-side vertex per SB line."""
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


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used for D = 4.
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
# C growth/annealing wrapper.
# ----------------------------------------------------------------------------

def _c_grow(graph, d, D, seed, budget):
    """Run the C annealer from a valid graph; returns (n, edges) as printed by C."""
    out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                    stdin_graph=(graph[0], graph[1]), timeout=budget + 6.0)
    return lib.parse_graph_text(out)


# ----------------------------------------------------------------------------
# Driver.
#   1. Fallback K_{d,d} (diameter 2, always valid for D >= 2).
#   2. D == 3: best arc-extended projective plane graph (reaches 394 for d=16).
#      D == 4: generalized quadrangle W(q).
#   3. If below the Moore bound, the C engine grows the start graph while
#      keeping it valid, using most of the time budget.
#   4. Every candidate is checked with lib.is_valid before it is kept.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + 0.85 * time_limit - 2.0

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    try:
        if D == 3:
            for g in _arc_extensions(d, t0 + 0.15 * time_limit,
                                     random.Random(seed * 7919 + d)):
                consider(g)
        elif D == 4:
            consider(_best_gq(d))
    except Exception:
        pass

    if D >= 3 and best[0] < lib.moore_bound(d, D):
        budget = end - time.monotonic()
        if budget >= 1.0:
            try:
                consider(_c_grow(best, d, D, seed, budget))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
