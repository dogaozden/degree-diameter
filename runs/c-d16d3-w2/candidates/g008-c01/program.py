import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bipartite graphs with a penalty.
#
# State: a bipartite graph with max degree d on alive vertices (indices < cap).
# Energy: E = bad - BETA * nalive, where bad = number of unordered alive pairs
# at distance > D. The best state with bad == 0 is kept and printed.
#
# Moves:
#   add, remove, swap        : as before (random double-edge swap keeps degrees).
#   guided_add (new)         : pick a bad pair (u, w). Join u to a vertex y on the
#                              opposite side with dist(y, w) <= D-1, so u now
#                              reaches w. If u is full, first drop one of its edges.
#   guided_swap (new)        : pick a bad pair (u, w). Double-edge swap
#                              (u,v),(x,y) -> (u,y),(x,v) where y lies within
#                              D-1 of w. Degrees and bipartiteness are preserved.
#
# Distance data (balls of radius D and D-1, and per-vertex bad counts) is cached
# for the accepted state in an Aux record, so guided moves never see stale data.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXD 32
#define MAXW (MAXN / 64)

typedef struct {
    int alive[MAXN];
    int col[MAXN];
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int nalive;
    int cap;
} State;

typedef struct {
    uint64_t reach[MAXN][MAXW];   /* ball of radius D */
    uint64_t ballm1[MAXN][MAXW];  /* ball of radius D-1 */
    int badv[MAXN];               /* alive vertices at distance > D */
} Aux;

static State cur, bak, best;
static Aux AX[2];
static int have_best = 0;
static int d, D;
static uint64_t nxt[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc64(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < cur.deg[u]; i++) if (cur.adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    cur.adj[u][cur.deg[u]++] = v;
    cur.adj[v][cur.deg[v]++] = u;
}

static void del_one(int u, int v) {
    for (int i = 0; i < cur.deg[u]; i++) {
        if (cur.adj[u][i] == v) {
            cur.adj[u][i] = cur.adj[u][cur.deg[u] - 1];
            cur.deg[u]--;
            return;
        }
    }
}

static void del_edge(int u, int v) {
    del_one(u, v);
    del_one(v, u);
}

/* Fills X with distance data for the current state; returns the bad-pair count. */
static long long compute_bad(Aux *X) {
    int cap = cur.cap;
    int W = (cap + 63) >> 6;
    if (W < 1) W = 1;
    for (int v = 0; v < cap; v++) {
        for (int w = 0; w < W; w++) X->reach[v][w] = 0;
        if (cur.alive[v]) X->reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        if (r == D - 1) {
            for (int v = 0; v < cap; v++)
                for (int w = 0; w < W; w++) X->ballm1[v][w] = X->reach[v][w];
        }
        for (int v = 0; v < cap; v++) {
            if (!cur.alive[v]) continue;
            for (int w = 0; w < W; w++) nxt[v][w] = X->reach[v][w];
            for (int i = 0; i < cur.deg[v]; i++) {
                int u = cur.adj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= X->reach[u][w];
            }
        }
        for (int v = 0; v < cap; v++) {
            if (!cur.alive[v]) continue;
            for (int w = 0; w < W; w++) X->reach[v][w] = nxt[v][w];
        }
    }
    long long tot = 0;
    for (int v = 0; v < cap; v++) {
        X->badv[v] = 0;
        if (!cur.alive[v]) continue;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc64(X->reach[v][w]);
        X->badv[v] = cur.nalive - pc;
        tot += X->badv[v];
    }
    return tot / 2;
}

static int move_add(void) {
    int w = -1;
    for (int i = 0; i < MAXN; i++) if (!cur.alive[i]) { w = i; break; }
    if (w < 0) return 0;
    int side = rndi(2);
    static int cand[MAXN];
    int nc = 0;
    for (int v = 0; v < cur.cap; v++)
        if (cur.alive[v] && cur.col[v] == 1 - side) cand[nc++] = v;
    if (nc == 0) return 0;
    int k = nc < d ? nc : d;
    for (int i = 0; i < k; i++) {
        int j = i + rndi(nc - i);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    cur.alive[w] = 1;
    cur.col[w] = side;
    cur.deg[w] = 0;
    cur.nalive++;
    if (w + 1 > cur.cap) cur.cap = w + 1;
    for (int i = 0; i < k; i++) {
        int p = cand[i];
        if (cur.deg[p] >= d) {
            int q = cur.adj[p][rndi(cur.deg[p])];
            del_edge(p, q);
        }
        add_edge(w, p);
    }
    return 1;
}

static int move_remove(void) {
    if (cur.nalive <= 2) return 0;
    int w, tries = 0;
    do {
        w = rndi(cur.cap);
        tries++;
    } while (!cur.alive[w] && tries < 100000);
    if (!cur.alive[w]) return 0;
    while (cur.deg[w] > 0) {
        int u = cur.adj[w][0];
        del_edge(w, u);
    }
    cur.alive[w] = 0;
    cur.nalive--;
    return 1;
}

static int move_swap(void) {
    int u, x, tries = 0;
    do {
        u = rndi(cur.cap);
        tries++;
    } while ((!cur.alive[u] || cur.deg[u] == 0) && tries < 100000);
    if (!cur.alive[u] || cur.deg[u] == 0) return 0;
    int v = cur.adj[u][rndi(cur.deg[u])];
    int s = cur.col[u];
    tries = 0;
    do {
        x = rndi(cur.cap);
        tries++;
    } while ((!cur.alive[x] || cur.deg[x] == 0 || cur.col[x] != s) && tries < 100000);
    if (!cur.alive[x] || cur.deg[x] == 0 || cur.col[x] != s) return 0;
    int y = cur.adj[x][rndi(cur.deg[x])];
    if (x == u || y == v) return 0;
    if (has_edge(u, y) || has_edge(x, v)) return 0;
    del_edge(u, v);
    del_edge(x, y);
    add_edge(u, y);
    add_edge(x, v);
    return 1;
}

/* Uniformly pick a bad pair (u, w): u has some alive vertex at distance > D, w is one such. */
static int pick_bad_pair(const Aux *X, int *ou, int *ow) {
    static int bl[MAXN];
    int cap = cur.cap, nb = 0;
    for (int v = 0; v < cap; v++)
        if (cur.alive[v] && X->badv[v] > 0) bl[nb++] = v;
    if (nb == 0) return 0;
    int u = bl[rndi(nb)];
    int cnt = 0, w = -1;
    for (int v = 0; v < cap; v++) {
        if (!cur.alive[v]) continue;
        if ((X->reach[u][v >> 6] >> (v & 63)) & 1ULL) continue;
        cnt++;
        if (rndi(cnt) == 0) w = v;   /* reservoir sampling */
    }
    if (w < 0) return 0;
    *ou = u;
    *ow = w;
    return 1;
}

/* Guided add: connect the bad-pair endpoint u to a vertex y near w. */
static int move_guided_add(const Aux *X) {
    int u, w;
    if (!pick_bad_pair(X, &u, &w)) return 0;
    int s = cur.col[u];
    int v = -1;
    if (cur.deg[u] >= d) v = cur.adj[u][rndi(cur.deg[u])];
    static int cand[MAXN], freec[MAXN];
    int nc = 0, nf = 0;
    for (int y = 0; y < cur.cap; y++) {
        if (!cur.alive[y] || cur.col[y] == s || y == u || y == v) continue;
        if (!((X->ballm1[w][y >> 6] >> (y & 63)) & 1ULL)) continue;
        if (has_edge(u, y)) continue;
        cand[nc++] = y;
        if (cur.deg[y] < d) freec[nf++] = y;
    }
    if (nc == 0) return 0;
    int y = nf > 0 ? freec[rndi(nf)] : cand[rndi(nc)];
    if (v >= 0) del_edge(u, v);
    if (cur.deg[y] >= d) {
        int z = cur.adj[y][rndi(cur.deg[y])];
        del_edge(y, z);
    }
    add_edge(u, y);
    return 1;
}

/* Guided double-edge swap: (u,v),(x,y) -> (u,y),(x,v) with y within D-1 of w. */
static int move_guided_swap(const Aux *X) {
    int u, w;
    if (!pick_bad_pair(X, &u, &w)) return 0;
    if (cur.deg[u] == 0) return 0;
    int s = cur.col[u];
    static int cand[MAXN];
    int nc = 0;
    for (int y = 0; y < cur.cap; y++) {
        if (!cur.alive[y] || cur.col[y] == s || cur.deg[y] == 0) continue;
        if (!((X->ballm1[w][y >> 6] >> (y & 63)) & 1ULL)) continue;
        cand[nc++] = y;
    }
    if (nc == 0) return 0;
    int y = cand[rndi(nc)];
    int x = cur.adj[y][rndi(cur.deg[y])];
    int v = cur.adj[u][rndi(cur.deg[u])];
    if (x == u || y == v) return 0;
    if (has_edge(u, y) || has_edge(x, v)) return 0;
    del_edge(u, v);
    del_edge(x, y);
    add_edge(u, y);
    add_edge(x, v);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2 || N0 < 1 || N0 > MAXN - 64) { printf("0 0\n"); return 0; }
    memset(&cur, 0, sizeof(cur));
    cur.cap = N0;
    cur.nalive = N0;
    for (int i = 0; i < N0; i++) cur.alive[i] = 1;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N0 || v >= N0 || u == v) continue;
        if (cur.deg[u] >= d || cur.deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    static int queue[MAXN];
    for (int i = 0; i < N0; i++) cur.col[i] = -1;
    for (int s = 0; s < N0; s++) {
        if (cur.col[s] >= 0) continue;
        cur.col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < cur.deg[u]; i++) {
                int v = cur.adj[u][i];
                if (cur.col[v] < 0) {
                    cur.col[v] = 1 - cur.col[u];
                    queue[qt++] = v;
                }
            }
        }
    }
    for (int u = 0; u < N0; u++) {
        for (int i = cur.deg[u] - 1; i >= 0; i--) {
            if (i >= cur.deg[u]) continue;
            int v = cur.adj[u][i];
            if (cur.col[v] == cur.col[u]) del_edge(u, v);
        }
    }

    Aux *acc = &AX[0], *tmp = &AX[1];
    clock_t t0 = clock();
    long long bad = compute_bad(acc);
    const double BETA = 2.0;
    const double T0 = 2.0, T1 = 0.03;
    double E = (double)bad - BETA * cur.nalive;
    if (bad == 0) {
        memcpy(&best, &cur, sizeof(State));
        have_best = 1;
    }

    while (1) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (el > budget) break;
        double frac = budget > 0 ? el / budget : 1.0;
        double T = T0 * pow(T1 / T0, frac);

        memcpy(&bak, &cur, sizeof(State));
        double r = rndu();
        int ok;
        if (bad > 0 && r < 0.25) ok = move_guided_add(acc);
        else if (bad > 0 && r < 0.45) ok = move_guided_swap(acc);
        else if (r < 0.60) ok = move_add();
        else if (r < 0.67) ok = move_remove();
        else ok = move_swap();
        if (!ok) continue;

        long long bad2 = compute_bad(tmp);
        double E2 = (double)bad2 - BETA * cur.nalive;
        if (E2 <= E || rndu() < exp(-(E2 - E) / T)) {
            E = E2;
            bad = bad2;
            Aux *t = acc; acc = tmp; tmp = t;
            if (bad == 0 && (!have_best || cur.nalive > best.nalive)) {
                memcpy(&best, &cur, sizeof(State));
                have_best = 1;
            }
        } else {
            memcpy(&cur, &bak, sizeof(State));
        }
    }

    State *s = have_best ? &best : &cur;
    static int id[MAXN];
    int n = 0;
    for (int i = 0; i < s->cap; i++) id[i] = s->alive[i] ? n++ : -1;
    long m = 0;
    for (int u = 0; u < s->cap; u++) {
        if (!s->alive[u]) continue;
        for (int i = 0; i < s->deg[u]; i++) if (s->adj[u][i] > u) m++;
    }
    printf("%d %ld\n", n, m);
    for (int u = 0; u < s->cap; u++) {
        if (!s->alive[u]) continue;
        for (int i = 0; i < s->deg[u]; i++) {
            int v = s->adj[u][i];
            if (v > u) printf("%d %d\n", id[u], id[v]);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions used as starting graphs.
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

def _c_anneal(graph, d, D, seed, budget):
    """Run the C annealer from graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 0.5 or d > 32:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 8.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Driver.
#   D == 3: arc-extended projective plane graphs as the start (best valid one).
#   D == 4: generalized quadrangle W(q) as the start.
#   else  : K_{d,d} as the start.
# If the start already meets the Moore bound, return it without searching
# (this makes calibration cases instant). Otherwise the C guided annealer
# runs for most of the budget. Every result is checked with lib.is_valid, and
# K_{d,d} (diameter 2) is the always-valid fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    def elapsed():
        return time.monotonic() - start

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
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
            for g in _arc_extensions(d, start + 0.05 * time_limit,
                                     random.Random(seed * 7919 + d)):
                consider(g)
        elif D == 4:
            consider(_best_gq(d))
    except Exception:
        pass

    ceiling = lib.moore_bound(d, D)
    if best[0] >= ceiling:
        return best

    budget = 0.85 * time_limit - elapsed() - 1.5
    if budget >= 0.5:
        consider(_c_anneal(best, d, D, seed, budget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
