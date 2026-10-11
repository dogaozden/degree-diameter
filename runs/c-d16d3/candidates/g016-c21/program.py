"""Arc-extension search for the d=16, D=3 target, with a new C search core.

Construction: take the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1, degree r = q+1).
Choose two independent sets:
  S_A, a set of points such that every line holds at most s = d - r of them. Add one new
       point-side vertex per element, joined to the r lines through that point.
  S_B, a set of lines such that every point lies on at most s of them. Add one new
       line-side vertex per element, joined to the r points on that line.
Every original vertex stays within degree d. Every pair of vertices is within distance 3,
because any two points share a line, any two lines meet, and every new vertex reaches
everything within 3 steps. So any pair of sets with these load bounds gives a valid graph.
The C engine finds large sets by annealed add-with-eviction moves. It does not search the
whole graph.

Expectation: for d=16 the best family member uses q=13, s=2, and the largest 2-arcs in PG(2,13)
have 14 points. That gives 2*(183+14) = 394, which matches the record, so this path reproduces the
record but does not beat it. The Python arc candidates and known constructions are kept as fallbacks.
Every output is checked with lib.is_valid, and the Haar graph K_{d,d} is the last resort.
"""
import random
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 32
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

/* Number of unordered vertex pairs at distance > D (bitset BFS). */
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        total += n - c;
    }
    return total / 2;
}

static int is_valid(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) { g->side[u] = 1 - g->side[v]; queue[tail++] = u; }
                else if (g->side[u] == g->side[v]) { g->n = 0; return; }
            }
        }
    }
    if (!is_valid(g)) g->n = 0;
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

/* ------------------------------------------------------------ cap-set search
 * Elements: vertices on side sd. Blocks: their neighbours (other side).
 * Constraint: every block has at most CAP chosen neighbouring elements.
 * Moves: pick an unchosen element, evict chosen neighbours of its full blocks,
 * insert it. Accept by a Metropolis rule on the change in size.
 */
static int CAP;
static unsigned char chosen[MAXN];
static int cnt[MAXN];
static int elems[MAXN];
static int remv[MAXN];

static void setc(const Graph *g, int x, int on) {
    chosen[x] = (unsigned char)on;
    int dl = on ? 1 : -1;
    for (int i = 0; i < g->deg[x]; i++) cnt[g->adj[x][i]] += dl;
}

static void arc_search(const Graph *g, int sd, int cap, double until, unsigned char *bestc) {
    CAP = cap;
    int n = g->n, ne = 0;
    for (int v = 0; v < n; v++) {
        chosen[v] = 0;
        cnt[v] = 0;
        bestc[v] = 0;
        if (g->side[v] == sd) elems[ne++] = v;
    }
    if (ne == 0) return;
    int cur = 0, best = 0;
    long it = 0;
    const double T = 0.35;
    while (1) {
        if ((++it & 31) == 0 && now() > until) break;
        int x = elems[rndint(ne)];
        if (chosen[x]) continue;
        int nr = 0;
        for (int i = 0; i < g->deg[x]; i++) {
            int y = g->adj[x][i];
            while (cnt[y] >= CAP) {
                int k = g->deg[y], s0 = rndint(k), z = -1;
                for (int j = 0; j < k; j++) {
                    int w = g->adj[y][(s0 + j) % k];
                    if (chosen[w]) { z = w; break; }
                }
                if (z < 0) break;
                setc(g, z, 0);
                remv[nr++] = z;
            }
        }
        int ok = 1;
        for (int i = 0; i < g->deg[x]; i++)
            if (cnt[g->adj[x][i]] >= CAP) { ok = 0; break; }
        if (ok) {
            int delta = 1 - nr;
            if (delta >= 0 || rnd01() < exp(delta / T)) {
                setc(g, x, 1);
                cur += delta;
                if (cur > best) {
                    best = cur;
                    for (int j = 0; j < ne; j++) bestc[elems[j]] = chosen[elems[j]];
                }
                continue;
            }
        }
        for (int j = nr - 1; j >= 0; j--) setc(g, remv[j], 1);
    }
}

/* Add one new vertex per chosen element: point-side for cA, line-side for cB. */
static void build_arc(const Graph *base, const unsigned char *cA, const unsigned char *cB, Graph *out) {
    copy_graph(out, base);
    int n0 = base->n;
    for (int pass = 0; pass < 2; pass++) {
        const unsigned char *c = pass == 0 ? cA : cB;
        for (int v = 0; v < n0; v++) {
            if (!c[v] || out->n >= MAXN) continue;
            int w = out->n++;
            out->deg[w] = 0;
            out->side[w] = base->side[v];
            for (int i = 0; i < base->deg[v]; i++) add_edge(out, w, base->adj[v][i]);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [arc] < base_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int arc = argc >= 6 && strcmp(argv[5], "arc") == 0;
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph base, best, out;
    static unsigned char cA[MAXN], cB[MAXN];
    if (d < 1 || d > MAXD || D < 1) { printf("0 0\n"); return 0; }
    read_start(&base);
    if (base.n == 0) { printf("0 0\n"); return 0; }
    copy_graph(&best, &base);

    if (arc) {
        int r = 0;
        for (int v = 0; v < base.n; v++)
            if (base.deg[v] > r) r = base.deg[v];
        int cap = d - r;
        if (cap >= 1) {
            double mid = t0 + (t_end - t0) * 0.5;
            arc_search(&base, 0, cap, mid, cA);
            arc_search(&base, 1, cap, t_end, cB);
            build_arc(&base, cA, cB, &out);
            if (out.n > best.n && is_valid(&out)) copy_graph(&best, &out);
        }
    }
    if (!is_valid(&best)) { printf("0 0\n"); return 0; }
    print_graph(&best);
    return 0;
}
'''


def _pg_data(q):
    """Points/lines of PG(2, q): point i and line i share the vector pts[i]."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, m, point_lines, line_points):
    """Every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy set S with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG(2,q) incidence plus, per element P of S, a new A-vertex on the lines through P
    and a new B-vertex on the points of line P. Diameter 3, max degree q+1+s."""
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


def _arc_candidates(d, deadline, rng):
    """(n, edges) candidates from arc-extended projective planes, for each prime power q."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, point_lines, line_points, index = _pg_data(q)
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 30, deadline)]
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


def _arc_c_choice(d):
    """Prime power q (with slack s = d - q - 1 >= 1) whose arc family has the largest estimated order."""
    best = None
    for q in range(2, d - 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 1:
            continue
        m = q * q + q + 1
        est = 2 * m + 2 * min((q + 1) * (s - 1) + 1, m)
        if best is None or est > best[0]:
            best = (est, q)
    return best[1] if best else None


def known_start(d, D):
    """Best closed-form graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = (cand[0], cand[1])

    if D >= 3:
        consider(known_start(d, D))
        rng = random.Random(seed * 7919 + d)
        for cand in sorted(_arc_candidates(d, t0 + 0.10 * time_limit, rng), key=lambda t: -t[0]):
            consider(cand)

    # New search: independent cap-sets on both sides of PG(2, q), run in C.
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if D >= 3 and budget > 0.5 and best[0] < lib.moore_bound(d, D):
        q = _arc_c_choice(d)
        if q is not None:
            try:
                base = lib.projective_plane_incidence(q)
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), "arc"],
                                 stdin_graph=base, timeout=budget + 5)
                n, e = lib.parse_graph_text(text)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
            except (RuntimeError, ValueError):
                pass   # keep the construction if the search fails

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
