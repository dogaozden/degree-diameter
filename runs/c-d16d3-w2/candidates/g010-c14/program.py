import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing with a penalty on a graph with alive/dead slots.
#
# State: bipartite graph with max degree d on alive vertices (indices < cap).
# Energy: E = bad - BETA * nalive, where bad = number of unordered alive pairs
# at distance > D. The best state with bad == 0 (largest nalive) is kept.
# Moves (all keep max degree <= d and bipartiteness):
#   add     : activate a dead slot on one side, join it to up to d opposite-side
#             vertices (spare-capacity partners first, full ones lose a random edge),
#   remove  : deactivate an alive vertex,
#   swap    : double-edge swap (u,v),(x,y) -> (u,y),(x,v),
#   rewire  : a-b -> a-w with w on b's side and spare capacity,
#   edge    : add an edge between opposite-side vertices with spare capacity.
# Stalls restart from the best valid state. The output is the best valid graph
# (or the input if none was found); Python re-checks everything.
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
#define STALL 15000LL

typedef struct {
    int alive[MAXN];
    int col[MAXN];
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int nalive;
    int cap;
} State;

static State cur, bak, best, init_state;
static int have_best = 0;
static int d, D;
static uint64_t reach_a[MAXN][MAXW];
static uint64_t reach_b[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double wall(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void copy_state(State *dst, const State *src) {
    int hi = dst->cap > src->cap ? dst->cap : src->cap;
    if (hi > MAXN) hi = MAXN;
    memcpy(dst->alive, src->alive, sizeof(int) * (size_t)hi);
    memcpy(dst->col, src->col, sizeof(int) * (size_t)hi);
    memcpy(dst->deg, src->deg, sizeof(int) * (size_t)hi);
    memcpy(dst->adj, src->adj, sizeof(int) * MAXD * (size_t)hi);
    dst->nalive = src->nalive;
    dst->cap = src->cap;
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

static long long compute_bad(void) {
    int cap = cur.cap;
    int W = (cap + 63) >> 6;
    if (W < 1) W = 1;
    uint64_t (*cu)[MAXW] = reach_a;
    uint64_t (*nx)[MAXW] = reach_b;
    for (int v = 0; v < cap; v++) {
        for (int w = 0; w < W; w++) cu[v][w] = 0;
        if (cur.alive[v]) cu[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < cap; v++) {
            if (!cur.alive[v]) continue;
            for (int w = 0; w < W; w++) nx[v][w] = cu[v][w];
            for (int i = 0; i < cur.deg[v]; i++) {
                const uint64_t *s = cu[cur.adj[v][i]];
                for (int w = 0; w < W; w++) nx[v][w] |= s[w];
            }
        }
        uint64_t (*t)[MAXW] = cu;
        cu = nx;
        nx = t;
    }
    long long tot = 0;
    for (int v = 0; v < cap; v++) {
        if (!cur.alive[v]) continue;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc64(cu[v][w]);
        tot += cur.nalive - pc;
    }
    return tot / 2;
}

static int move_add(void) {
    int w = -1;
    for (int i = 0; i < MAXN - 1; i++) if (!cur.alive[i]) { w = i; break; }
    if (w < 0) return 0;
    int side = rndi(2);
    static int spare[MAXN], full[MAXN], chosen[MAXD];
    int ns = 0, nf = 0;
    for (int v = 0; v < cur.cap; v++) {
        if (!cur.alive[v] || cur.col[v] == side) continue;
        if (cur.deg[v] < d) spare[ns++] = v;
        else full[nf++] = v;
    }
    for (int i = 0; i < ns; i++) {
        int j = i + rndi(ns - i);
        int t = spare[i]; spare[i] = spare[j]; spare[j] = t;
    }
    for (int i = 0; i < nf; i++) {
        int j = i + rndi(nf - i);
        int t = full[i]; full[i] = full[j]; full[j] = t;
    }
    int k = 0;
    for (int i = 0; i < ns && k < d; i++) chosen[k++] = spare[i];
    for (int i = 0; i < nf && k < d; i++) chosen[k++] = full[i];
    if (k == 0) return 0;
    cur.alive[w] = 1;
    cur.col[w] = side;
    cur.deg[w] = 0;
    cur.nalive++;
    if (w + 1 > cur.cap) cur.cap = w + 1;
    for (int i = 0; i < k; i++) {
        int p = chosen[i];
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
    int w = -1;
    for (int t = 0; t < 1000; t++) {
        int c = rndi(cur.cap);
        if (cur.alive[c]) { w = c; break; }
    }
    if (w < 0) return 0;
    while (cur.deg[w] > 0) {
        int u = cur.adj[w][0];
        del_edge(w, u);
    }
    cur.alive[w] = 0;
    cur.nalive--;
    return 1;
}

static int move_swap(void) {
    int u = -1;
    for (int t = 0; t < 200; t++) {
        int c = rndi(cur.cap);
        if (cur.alive[c] && cur.deg[c] > 0) { u = c; break; }
    }
    if (u < 0) return 0;
    int v = cur.adj[u][rndi(cur.deg[u])];
    int s = cur.col[u];
    int x = -1;
    for (int t = 0; t < 200; t++) {
        int c = rndi(cur.cap);
        if (cur.alive[c] && cur.deg[c] > 0 && cur.col[c] == s) { x = c; break; }
    }
    if (x < 0) return 0;
    int y = cur.adj[x][rndi(cur.deg[x])];
    if (x == u || y == v) return 0;
    if (has_edge(u, y) || has_edge(x, v)) return 0;
    del_edge(u, v);
    del_edge(x, y);
    add_edge(u, y);
    add_edge(x, v);
    return 1;
}

static int move_rewire(void) {
    int a = -1;
    for (int t = 0; t < 200; t++) {
        int c = rndi(cur.cap);
        if (cur.alive[c] && cur.deg[c] > 0) { a = c; break; }
    }
    if (a < 0) return 0;
    int b = cur.adj[a][rndi(cur.deg[a])];
    int w = -1;
    for (int t = 0; t < 200; t++) {
        int c = rndi(cur.cap);
        if (c != b && cur.alive[c] && cur.col[c] == cur.col[b] &&
            cur.deg[c] < d && !has_edge(a, c)) {
            w = c;
            break;
        }
    }
    if (w < 0) return 0;
    del_edge(a, b);
    add_edge(a, w);
    return 1;
}

static int move_edge(void) {
    int x = -1;
    for (int t = 0; t < 200; t++) {
        int c = rndi(cur.cap);
        if (cur.alive[c] && cur.deg[c] < d) { x = c; break; }
    }
    if (x < 0) return 0;
    int y = -1;
    for (int t = 0; t < 200; t++) {
        int c = rndi(cur.cap);
        if (cur.alive[c] && cur.deg[c] < d && cur.col[c] != cur.col[x] && !has_edge(x, c)) {
            y = c;
            break;
        }
    }
    if (y < 0) return 0;
    add_edge(x, y);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0 = 0, M0 = 0;
    if (scanf("%d %d", &N0, &M0) != 2 || N0 < 1 || N0 > MAXN - 64 || M0 < 0) {
        printf("0 0\n");
        return 0;
    }
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

    copy_state(&init_state, &cur);
    long long bad = compute_bad();
    if (bad == 0) {
        copy_state(&best, &cur);
        have_best = 1;
    }
    const double BETA = 2.0, T0 = 1.5, T1 = 0.05;
    double E = (double)bad - BETA * (double)cur.nalive;
    double t0 = wall();
    long long it = 0, last_imp = 0;

    for (;;) {
        double el = wall() - t0;
        if (el >= budget) break;
        double frac = budget > 0.0 ? el / budget : 1.0;
        double T = T0 * pow(T1 / T0, frac);
        it++;

        copy_state(&bak, &cur);
        double r = rndu();
        int ok;
        if (r < 0.30) ok = move_add();
        else if (r < 0.38) ok = move_remove();
        else if (r < 0.60) ok = move_swap();
        else if (r < 0.92) ok = move_rewire();
        else ok = move_edge();
        if (!ok) continue;

        long long nb = compute_bad();
        double E2 = (double)nb - BETA * (double)cur.nalive;
        if (E2 <= E || rndu() < exp(-(E2 - E) / T)) {
            E = E2;
            if (nb == 0 && (!have_best || cur.nalive > best.nalive)) {
                copy_state(&best, &cur);
                have_best = 1;
                last_imp = it;
            }
        } else {
            copy_state(&cur, &bak);
        }

        if (have_best && it - last_imp > STALL) {
            copy_state(&cur, &best);
            E = (double)compute_bad() - BETA * (double)cur.nalive;
            last_imp = it;
        }
    }

    State *s = have_best ? &best : &init_state;
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
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence. With spare s = d - q - 1, choose point sets
# SA and SB so that every line holds <= s points of SA and every point lies on
# <= s lines of SB. Add an A-vertex per SA point (joined to its q+1 lines) and a
# B-vertex per SB line (joined to its q+1 points). For d = 16 and q = 13 the
# conic gives 394 vertices, which is the record. The C annealer tries to add more.
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
    """PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
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
    """W(q) for the largest prime power q with q + 1 <= d, q <= 7 for speed (diameter 4)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C annealer wrapper.
# ----------------------------------------------------------------------------

def _c_anneal(graph, d, D, seed, budget):
    """Run the C annealer from graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 0.5 or d > 32:
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
#   D == 1 : single edge. D == 2 : K_{d,d} is optimal and returned directly.
#   D >= 3 : arc-extended projective plane graphs (best valid one), plus W(q)
#            for D >= 4. Then the C annealer runs on the best start for most of
#            the time budget. Every result is checked with lib.is_valid, and
#            K_{d,d} is the always-valid fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or best[0] >= lib.moore_bound(d, D):
        return best[0], list(best[1])

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))

    try:
        if D >= 3:
            for g in _arc_extensions(d, start + 0.10 * time_limit,
                                     random.Random(seed * 7919 + d)):
                consider(g)
        if D >= 4:
            consider(_best_gq(d))
    except Exception:
        pass

    end = start + 0.85 * time_limit - 1.5
    budget = end - time.monotonic()
    if best[0] < lib.moore_bound(d, D) and budget >= 1.0:
        consider(_c_anneal(best, d, D, seed, budget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
