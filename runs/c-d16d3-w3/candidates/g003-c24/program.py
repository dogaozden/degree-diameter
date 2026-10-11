"""Combined diameter-3 search: structured starts, then a ruin-and-recreate engine in C.

Starts (each checked with lib.is_valid):
  - projective plane incidence graphs and Araujo-Pardo/Lopez graphs when they apply,
  - conic blow-up of PG(2,q) (q = d-3 odd) and arc-extended PG(2,q) incidence graphs,
    with the arc refined by a plateau local search,
  - W(q) for D >= 4 with small q, and K_{d,d} as the always-valid fallback.

Engine (new in this version): ruin and recreate.
  1. RUIN: delete 1-3 random vertices. Their neighbours lose degree and some pairs break.
  2. RECREATE: insert k (or k+1) new vertices. Each new vertex on side X takes a greedy
     partial cover of the other side by radius-(D-1) balls, with random tie-breaking.
  3. REPAIR: degree-preserving edge swaps (annealed, small uphill acceptance) try to
     remove the remaining bad pairs.
  4. ACCEPT: only exactly valid graphs (checked by bitset ball counting) are kept.
     The current state can move along plateaus of equal size, and the best size is kept.

If the engine cannot improve a start, the start itself is returned, so the score never drops.
"""
import itertools
import random
import time

import lib

C_RR = r"""
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1024
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

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
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

static void del_half(Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][--g->deg[u]];
            return;
        }
}

static void del_edge(Graph *g, int u, int v) {
    del_half(g, u, v);
    del_half(g, v, u);
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

static uint64_t MA[MAXN * MAXW], MB[MAXN * MAXW];
static int badv[MAXN];

/* Bitset of all vertices within distance r of each vertex; returns the buffer holding it. */
static uint64_t *ball_matrix(const Graph *g, int r) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = MA, *nxt = MB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int k = 0; k < r; k++) {
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
    return cur;
}

static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *B = ball_matrix(g, D);
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = B + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        badv[v] = n - c;
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
            int found = 0;
            for (int j = 0; j < g->deg[u]; j++)
                if (g->adj[u][j] == v) { found = 1; break; }
            if (!found) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN - 2) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) {
            g->n = 0;
            return;
        }
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
                if (g->side[u] == 255) {
                    g->side[u] = 1 - g->side[v];
                    queue[tail++] = u;
                } else if (g->side[u] == g->side[v]) {
                    g->n = 0;
                    return;
                }
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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* Delete vertex v and its edges; the last vertex is moved into slot v. */
static void remove_vertex(Graph *g, int v) {
    for (int i = 0; i < g->deg[v]; i++) del_half(g, g->adj[v][i], v);
    g->deg[v] = 0;
    int L = g->n - 1;
    if (v != L) {
        g->deg[v] = g->deg[L];
        g->side[v] = g->side[L];
        memcpy(g->adj[v], g->adj[L], sizeof(int) * g->deg[L]);
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            for (int j = 0; j < g->deg[u]; j++)
                if (g->adj[u][j] == L) { g->adj[u][j] = v; break; }
        }
    }
    g->deg[L] = 0;
    g->n = L;
}

/* Add one vertex on side X joined to a greedy partial cover of the other side by
   radius-(D-1) balls. Leftover bad pairs are handled later by repair(). */
static int recreate_one(Graph *g, int X) {
    int n = g->n;
    if (n + 1 >= MAXN) return 0;
    int W = (n + 63) / 64;
    uint64_t *B = ball_matrix(g, D - 1);
    uint64_t U[MAXW];
    for (int w = 0; w < W; w++) U[w] = ~0ULL;
    if (n & 63) U[W - 1] = (1ULL << (n & 63)) - 1ULL;
    static int inT[MAXN];
    memset(inT, 0, sizeof(int) * (size_t)n);
    int T[MAXD], nt = 0;
    while (nt < d) {
        int best = -1;
        double bestsc = -1.0;
        for (int v = 0; v < n; v++) {
            if (g->side[v] == X || g->deg[v] >= d || inT[v]) continue;
            const uint64_t *bv = B + (size_t)v * W;
            int gain = 0;
            for (int w = 0; w < W; w++) gain += __builtin_popcountll(bv[w] & U[w]);
            if (gain == 0) continue;
            double sc = gain + 2.5 * rnd01();
            if (sc > bestsc) { bestsc = sc; best = v; }
        }
        if (best < 0) break;
        inT[best] = 1;
        T[nt++] = best;
        const uint64_t *bb = B + (size_t)best * W;
        for (int w = 0; w < W; w++) U[w] &= ~bb[w];
    }
    if (nt == 0) return 0;
    int x = n;
    g->n = n + 1;
    g->deg[x] = 0;
    g->side[x] = (unsigned char)X;
    for (int k = 0; k < nt; k++) add_edge(g, x, T[k]);
    return 1;
}

/* Degree-preserving edge swaps that try to drive the number of bad pairs to zero. */
static long repair(Graph *g, int steps) {
    long bad = bad_pairs(g);
    for (int s = 0; s < steps && bad > 0; s++) {
        int v = rndint(g->n);
        for (int tries = 0; tries < 20 && badv[v] == 0; tries++) v = rndint(g->n);
        if (g->deg[v] == 0) continue;
        int u = g->adj[v][rndint(g->deg[v])];
        int a = rndint(g->n);
        if (a == v || g->side[a] != g->side[v] || g->deg[a] == 0) continue;
        int t = g->adj[a][rndint(g->deg[a])];
        if (t == u || has_edge(g, v, t) || has_edge(g, a, u)) continue;
        del_edge(g, v, u);
        del_edge(g, a, t);
        add_edge(g, v, t);
        add_edge(g, a, u);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < 0.02) {
            bad = nb;
        } else {
            del_edge(g, v, t);
            del_edge(g, a, u);
            add_edge(g, v, u);
            add_edge(g, a, t);
        }
    }
    return bad;
}

static void rr_search(Graph *best, double until) {
    static Graph cur, work;
    copy_graph(&cur, best);
    while (now() < until) {
        int k = 1 + rndint(3);
        int grow = rnd01() < 0.5 ? 1 : 0;
        if (cur.n <= k + 4) break;
        copy_graph(&work, &cur);
        for (int r = 0; r < k; r++) remove_vertex(&work, rndint(work.n));
        int adds = k + grow, ok = 1;
        for (int a = 0; a < adds && ok; a++) {
            int X = rndint(2);
            if (!recreate_one(&work, X) && !recreate_one(&work, 1 - X)) ok = 0;
        }
        if (!ok) continue;
        long bad = repair(&work, 400);
        if (bad != 0) continue;
        if (!is_valid(&work)) continue;
        copy_graph(&cur, &work);
        if (cur.n > best->n) copy_graph(best, &cur);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    if (d < 1 || d > MAXD - 2 || D < 1) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    if (D >= 2) rr_search(&best, t_end);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured starts.
# ----------------------------------------------------------------------------

def known_start(d, D):
    """Best directly constructible graph for D = 3: Moore graph or Araujo-Pardo/Lopez."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def conic_blowup(d, D):
    """Twin blow-up of PG(2,q), q = d-3 odd, duplicating conic points and dual-conic lines."""
    q = d - 3
    if D != 3 or q < 3 or q % 2 == 0 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {v: i for i, v in enumerate(pts)}
    m = len(pts)
    conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if any(v not in index for v in conic):
        return None
    arc = [index[v] for v in conic]
    n0, base = lib.projective_plane_incidence(q)
    pcopy = {i: [i] for i in range(m)}
    lcopy = {j: [m + j] for j in range(m)}
    n = n0
    for i in arc:
        pcopy[i].append(n)
        n += 1
    for j in arc:
        lcopy[j].append(n)
        n += 1
    edges = set()
    for u, v in base:
        i, j = u, v - m
        for a in pcopy[i]:
            for b in lcopy[j]:
                edges.add((a, b) if a < b else (b, a))
    return n, sorted(edges)


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
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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


def _local_arc(m, s, point_lines, line_points, rng, init, deadline, iters):
    """Plateau local search for a large set S where every line and every point carries at most s members of S."""
    inS = [False] * m
    cl = [0] * m
    cp = [0] * m
    S = []

    def fits(P):
        return all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P])

    def put(P):
        inS[P] = True
        S.append(P)
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def take(P):
        inS[P] = False
        S.remove(P)
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    for P in init:
        if not inS[P] and fits(P):
            put(P)
    best = list(S)
    for it in range(iters):
        if it % 256 == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        if fits(P):
            put(P)
        else:
            fullL = {L for L in point_lines[P] if cl[L] >= s}
            fullQ = {Q for Q in line_points[P] if cp[Q] >= s}
            blockers = [Q for Q in S
                        if any(L in fullL for L in point_lines[Q])
                        or any(R in fullQ for R in line_points[Q])]
            if len(blockers) != 1:
                continue
            b = blockers[0]
            take(b)
            if fits(P):
                put(P)
            else:
                put(b)
                continue
        if len(S) > len(best):
            best = list(S)
    return best


def _conic_set(q, index, F):
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
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[], _greedy_arc(m, s, pl, lp, rng, 40, deadline)]
        if s >= 2 and q >= 3:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        init = max(cands, key=len)
        loc = _local_arc(m, s, pl, lp, rng, init,
                         min(deadline, time.monotonic() + 0.5), 4000)
        cands.append(loc)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


def _gq_w(q):
    """Incidence graph of W(q), the generalized quadrangle (diameter 4)."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def starts(d, D, deadline, rng):
    out = []
    ks = known_start(d, D)
    if ks is not None:
        out.append(ks)
    cb = conic_blowup(d, D)
    if cb is not None:
        out.append(cb)
    if D >= 3:
        out.extend(_arc_extensions(d, deadline, rng))
    if D >= 4 and d - 1 <= 6:
        for q in range(min(d - 1, 5), 1, -1):
            if lib.is_prime_power(q):
                out.append(_gq_w(q))
                break
    return out


# ----------------------------------------------------------------------------
# C engine driver.
# ----------------------------------------------------------------------------

def _run_rr(n0, e0, d, D, seed, budget):
    text = lib.run_c(C_RR, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=budget + 5.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.80 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    cands = []
    for g in starts(d, D, t0 + 0.15 * time_limit, rng):
        try:
            if lib.is_valid(g[0], g[1], d, D):
                cands.append(g)
        except Exception:
            pass
    if lib.is_valid(fallback[0], fallback[1], d, D):
        cands.append(fallback)
    if not cands:
        return 1, []
    best = max(cands, key=lambda g: g[0])

    # Already at the Moore bound: nothing to search for.
    if best[0] >= lib.moore_bound(d, D):
        return best

    remaining = hard_end - time.monotonic()
    if remaining > 3.0:
        try:
            n1, e1 = _run_rr(best[0], best[1], d, D, seed * 31 + 1,
                             max(0.5, remaining - 1.5))
            if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                best = (n1, e1)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
