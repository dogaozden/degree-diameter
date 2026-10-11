import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Combined C engine. One run does three phases on the same bipartite graph:
#   1. Simulated annealing (penalty E = bad - BETA * nalive). Moves: add a
#      vertex joined to up to d opposite-side vertices (a full partner drops
#      one random edge), remove a vertex, or double-edge swap. The best valid
#      state is kept.
#   2. Greedy ball-cover insertion on the best state (from the parent g000).
#      A new vertex joined to a set N on the opposite side is within distance D
#      of every old vertex when N's (D-1)-balls cover the graph, so insertion
#      keeps validity. Random spare cross edges are added on failure.
#   3. Annealing again, starting from the greedy result at a lower temperature.
# Every stored state is valid (checked by bad-pair count), and the output is the
# largest valid state. Python re-checks with lib.is_valid and keeps a fallback.
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

static State cur, bak, best, gb;
static int have_best = 0;
static int d, D;
static uint64_t reach[MAXN][MAXW];
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

static int has_edge(State *S, int u, int v) {
    for (int i = 0; i < S->deg[u]; i++) if (S->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(State *S, int u, int v) {
    S->adj[u][S->deg[u]++] = v;
    S->adj[v][S->deg[v]++] = u;
}

static void del_one(State *S, int u, int v) {
    for (int i = 0; i < S->deg[u]; i++) {
        if (S->adj[u][i] == v) {
            S->adj[u][i] = S->adj[u][S->deg[u] - 1];
            S->deg[u]--;
            return;
        }
    }
}

static void del_edge(State *S, int u, int v) {
    del_one(S, u, v);
    del_one(S, v, u);
}

/* R-ball bitsets for all alive vertices of S. */
static void compute_reach(State *S, int R) {
    int cap = S->cap;
    int W = (cap + 63) >> 6;
    if (W < 1) W = 1;
    for (int v = 0; v < cap; v++) {
        for (int w = 0; w < W; w++) reach[v][w] = 0;
        if (S->alive[v]) reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < cap; v++) {
            if (!S->alive[v]) continue;
            for (int w = 0; w < W; w++) nxt[v][w] = reach[v][w];
            for (int i = 0; i < S->deg[v]; i++) {
                int u = S->adj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= reach[u][w];
            }
        }
        for (int v = 0; v < cap; v++) {
            if (!S->alive[v]) continue;
            for (int w = 0; w < W; w++) reach[v][w] = nxt[v][w];
        }
    }
}

/* Number of unordered alive pairs at distance > D. Zero means valid. */
static long long compute_bad(State *S) {
    compute_reach(S, D);
    int W = (S->cap + 63) >> 6;
    if (W < 1) W = 1;
    long long tot = 0;
    for (int v = 0; v < S->cap; v++) {
        if (!S->alive[v]) continue;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc64(reach[v][w]);
        tot += S->nalive - pc;
    }
    return tot / 2;
}

static int move_add(void) {
    State *S = &cur;
    int w = -1;
    for (int i = 0; i < MAXN; i++) if (!S->alive[i]) { w = i; break; }
    if (w < 0) return 0;
    int side = rndi(2);
    static int cand[MAXN];
    int nc = 0;
    for (int v = 0; v < S->cap; v++)
        if (S->alive[v] && S->col[v] == 1 - side) cand[nc++] = v;
    if (nc == 0) return 0;
    int k = nc < d ? nc : d;
    for (int i = 0; i < k; i++) {
        int j = i + rndi(nc - i);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    S->alive[w] = 1;
    S->col[w] = side;
    S->deg[w] = 0;
    S->nalive++;
    if (w + 1 > S->cap) S->cap = w + 1;
    for (int i = 0; i < k; i++) {
        int p = cand[i];
        if (S->deg[p] >= d) {
            int q = S->adj[p][rndi(S->deg[p])];
            del_edge(S, p, q);
        }
        add_edge(S, w, p);
    }
    return 1;
}

static int move_remove(void) {
    State *S = &cur;
    if (S->nalive <= 2) return 0;
    int w = -1;
    for (int tries = 0; tries < 100000; tries++) {
        int x = rndi(S->cap);
        if (S->alive[x]) { w = x; break; }
    }
    if (w < 0) return 0;
    while (S->deg[w] > 0) {
        int u = S->adj[w][0];
        del_edge(S, w, u);
    }
    S->alive[w] = 0;
    S->nalive--;
    return 1;
}

static int move_swap(void) {
    State *S = &cur;
    int u = -1;
    for (int tries = 0; tries < 100000; tries++) {
        int x = rndi(S->cap);
        if (S->alive[x] && S->deg[x] > 0) { u = x; break; }
    }
    if (u < 0) return 0;
    int v = S->adj[u][rndi(S->deg[u])];
    int s = S->col[u];
    int x = -1;
    for (int tries = 0; tries < 100000; tries++) {
        int y = rndi(S->cap);
        if (S->alive[y] && S->deg[y] > 0 && S->col[y] == s) { x = y; break; }
    }
    if (x < 0) return 0;
    int y = S->adj[x][rndi(S->deg[x])];
    if (x == u || y == v) return 0;
    if (has_edge(S, u, y) || has_edge(S, x, v)) return 0;
    del_edge(S, u, v);
    del_edge(S, x, y);
    add_edge(S, u, y);
    add_edge(S, x, v);
    return 1;
}

static void anneal(double budget, double T0, double T1) {
    const double BETA = 2.0;
    clock_t t0 = clock();
    long long bad = compute_bad(&cur);
    double E = (double)bad - BETA * cur.nalive;
    if (bad == 0 && (!have_best || cur.nalive > best.nalive)) {
        best = cur;
        have_best = 1;
    }
    while (1) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (el > budget) break;
        double frac = budget > 0 ? el / budget : 1.0;
        double T = T0 * pow(T1 / T0, frac);

        bak = cur;
        double r = rndu();
        int ok;
        if (r < 0.35) ok = move_add();
        else if (r < 0.45) ok = move_remove();
        else ok = move_swap();
        if (!ok) continue;

        bad = compute_bad(&cur);
        double E2 = (double)bad - BETA * cur.nalive;
        if (E2 <= E || rndu() < exp(-(E2 - E) / T)) {
            E = E2;
            if (bad == 0 && (!have_best || cur.nalive > best.nalive)) {
                best = cur;
                have_best = 1;
            }
        } else {
            cur = bak;
        }
    }
}

/* Copy the alive part of S into gb with vertices renumbered 0..n-1. */
static void compact_from(State *S) {
    static int id[MAXN];
    memset(&gb, 0, sizeof(gb));
    int n = 0;
    for (int i = 0; i < S->cap; i++) id[i] = S->alive[i] ? n++ : -1;
    for (int i = 0; i < S->cap; i++) {
        if (!S->alive[i]) continue;
        int a = id[i];
        gb.alive[a] = 1;
        gb.col[a] = S->col[i];
        gb.deg[a] = 0;
        for (int k = 0; k < S->deg[i]; k++) {
            gb.adj[a][gb.deg[a]++] = id[S->adj[i][k]];
        }
    }
    gb.nalive = n;
    gb.cap = n;
}

static int covers_all(const uint64_t *cov, int n) {
    int W = (n + 63) >> 6;
    for (int w = 0; w < W; w++) {
        int r = n - 64 * w;
        uint64_t want = (r >= 64) ? ~0ULL : ((1ULL << r) - 1);
        if ((cov[w] & want) != want) return 0;
    }
    return 1;
}

static int try_insert(State *G, int side) {
    int n = G->cap;
    int W = (n + 63) >> 6;
    static int cand[MAXN];
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (G->col[u] == 1 - side && G->deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    static int used[MAXN];
    for (int i = 0; i < n; i++) used[i] = 0;
    uint64_t cov[MAXW];
    memset(cov, 0, sizeof(cov));
    int chosen[MAXD];
    int nch = 0;
    while (nch < d && !covers_all(cov, n)) {
        int bu = -1, bg = 0;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (used[u]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc64(reach[u][w] & ~cov[w]);
            if (g > bg) { bg = g; bu = u; }
        }
        if (bu < 0) break;
        used[bu] = 1;
        chosen[nch++] = bu;
        for (int w = 0; w < W; w++) cov[w] |= reach[bu][w];
    }
    if (!covers_all(cov, n)) return 0;
    int w = n;
    G->alive[w] = 1;
    G->col[w] = side;
    G->deg[w] = 0;
    G->cap = n + 1;
    G->nalive++;
    for (int i = 0; i < nch; i++) add_edge(G, chosen[i], w);
    return 1;
}

static void grow(double budget) {
    clock_t t0 = clock();
    int fails = 0;
    while (fails < 200 && gb.cap < MAXN - 1) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (el > budget) break;
        compute_reach(&gb, D - 1);
        int sides[2] = {0, 1};
        if (rndi(2)) { sides[0] = 1; sides[1] = 0; }
        int ok = 0;
        for (int k = 0; k < 2 && !ok; k++) ok = try_insert(&gb, sides[k]);
        if (ok) { fails = 0; continue; }
        fails++;
        for (int t = 0; t < 50; t++) {
            int u = rndi(gb.cap), v = rndi(gb.cap);
            if (u == v || gb.col[u] == gb.col[v]) continue;
            if (gb.deg[u] >= d || gb.deg[v] >= d || has_edge(&gb, u, v)) continue;
            add_edge(&gb, u, v);
            break;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double B = atof(argv[4]);
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
        if (cur.deg[u] >= d || cur.deg[v] >= d || has_edge(&cur, u, v)) continue;
        add_edge(&cur, u, v);
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
            if (cur.col[v] == cur.col[u]) del_edge(&cur, u, v);
        }
    }

    if (compute_bad(&cur) == 0) {
        best = cur;
        have_best = 1;
    }

    /* Phase 1: annealing from the input graph. */
    anneal(0.50 * B, 2.0, 0.03);

    /* Phase 2: greedy ball-cover growth from the best valid state. */
    if (have_best) {
        compact_from(&best);
        grow(0.25 * B);
        int okg = (compute_bad(&gb) == 0);
        if (okg && gb.nalive > best.nalive) {
            best = gb;
            have_best = 1;
        }
        /* Phase 3: annealing from the greedy result at lower temperature. */
        cur = okg ? gb : best;
        anneal(0.15 * B, 0.4, 0.03);
    }

    if (!have_best) { printf("0 0\n"); return 0; }

    State *s = &best;
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
    """Return (n, edges) candidates from PG(2, q) plus arc-extension vertices, for prime powers q with q + 1 <= d."""
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
# C engine wrapper.
# ----------------------------------------------------------------------------

def _c_engine(graph, d, D, seed, budget):
    """Run the combined C engine from graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 0.5 or d > 32 or D < 2 or graph[0] > 900:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 10.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Driver.
#   D == 3: best arc-extended projective plane graph as the start.
#   D == 4: generalized quadrangle W(q) as the start.
#   else  : K_{d,d} as the start.
# The C engine then anneals, grows greedily, and anneals again. Every result
# is checked with lib.is_valid, and K_{d,d} (diameter 2) is the always-valid
# fallback.
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
            for g in _arc_extensions(d, start + 0.08 * time_limit,
                                     random.Random(seed * 7919 + d)):
                consider(g)
        elif D == 4:
            consider(_best_gq(d))
    except Exception:
        pass

    budget = 0.80 * time_limit - elapsed() - 1.5
    if budget >= 0.5:
        consider(_c_engine(best, d, D, seed, budget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
