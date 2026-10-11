"""Diameter-3 search: structured starts, then a remove-and-reinsert plateau search in C.

Starts (each validated with lib.is_valid):
  - conic blow-up of PG(2,q) (q = d-3 odd), and arc-extended PG(2,q) incidence graphs,
    where the arc set is refined by a plateau local search,
  - Araujo-Pardo/Lopez graphs and projective planes when they apply,
  - W(q) for D >= 4 with small q, and K_{d,d} as the always-valid fallback.

Engine (new in this version): SWAP. From a valid graph it deletes 1-3 random vertices, then
greedily re-inserts vertices. A new vertex on side X joins a greedy cover of the opposite side
whose radius-(D-1) balls cover every vertex, which is exactly the condition for its own
eccentricity to stay within D. The freed degree from deleted vertices lets the cover grow
beyond the old size. A candidate is accepted only if the full bipartite diameter check passes.
Equal-size moves form a plateau walk, and a rare one-vertex drop is allowed to escape it.
The best valid graph is kept throughout, so a failed run only wastes time.
"""
import itertools
import random
import time

import lib

C_SWAP = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 1024
#define MAXW (MAXN / 64)
#define MAXD 40

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int side[MAXN];
} Graph;

static int d, D;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int popc(uint64_t x) { return __builtin_popcountll(x); }

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Bitset of vertices within distance r of each vertex. Returns a pointer into RA or RB. */
static const uint64_t *balls(const Graph *g, int r) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
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

/* Number of unordered vertex pairs at distance > D (unreachable pairs included). */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    const uint64_t *b = balls(g, D);
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(b[(size_t)v * W + w]);
        total += n - c;
    }
    return total / 2;
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

/* Delete vertex x; the last vertex is moved into slot x so labels stay 0..n-1. */
static void remove_vertex(Graph *g, int x) {
    for (int i = 0; i < g->deg[x]; i++) del_half(g, g->adj[x][i], x);
    g->deg[x] = 0;
    int last = g->n - 1;
    if (x != last) {
        for (int i = 0; i < g->deg[last]; i++) {
            int u = g->adj[last][i];
            for (int j = 0; j < g->deg[u]; j++)
                if (g->adj[u][j] == last) {
                    g->adj[u][j] = x;
                    break;
                }
        }
        g->deg[x] = g->deg[last];
        memcpy(g->adj[x], g->adj[last], sizeof(int) * g->deg[last]);
        g->side[x] = g->side[last];
    }
    g->deg[last] = 0;
    g->n--;
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

/* Add one vertex on side X, joined to a greedy cover of the other side.
   The cover must reach every vertex within distance D-1. Returns 1 on success. */
static int try_add(Graph *g, int X) {
    int n = g->n, W = (n + 63) / 64;
    if (n + 1 >= MAXN) return 0;
    const uint64_t *b = balls(g, D - 1);
    uint64_t U[MAXW];
    for (int w = 0; w < W; w++) U[w] = ~0ULL;
    if (n & 63) U[W - 1] = (1ULL << (n & 63)) - 1ULL;
    char sel[MAXN];
    memset(sel, 0, (size_t)n);
    int T[MAXD], nt = 0;
    while (nt < d) {
        int best = -1;
        long bs = -1;
        for (int v = 0; v < n; v++) {
            if (g->side[v] == X || g->deg[v] >= d || sel[v]) continue;
            long gain = 0;
            for (int w = 0; w < W; w++) gain += popc(b[(size_t)v * W + w] & U[w]);
            if (gain <= 0) continue;
            long sc = gain * 8 + rndint(8);
            if (sc > bs) {
                bs = sc;
                best = v;
            }
        }
        if (best < 0) break;
        sel[best] = 1;
        T[nt++] = best;
        for (int w = 0; w < W; w++) U[w] &= ~b[(size_t)best * W + w];
        int left = 0;
        for (int w = 0; w < W; w++) left |= (U[w] != 0);
        if (!left) break;
    }
    for (int w = 0; w < W; w++)
        if (U[w]) return 0;
    if (nt == 0) return 0;
    int x = n;
    g->side[x] = X;
    g->deg[x] = 0;
    for (int k = 0; k < nt; k++) add_edge(g, x, T[k]);
    g->n = n + 1;
    return 1;
}

static int read_graph(Graph *g) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN - 2 || m < 0) return 0;
    g->n = n;
    for (int v = 0; v < n; v++) {
        g->deg[v] = 0;
        g->side[v] = -1;
    }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (g->deg[u] >= MAXD || g->deg[v] >= MAXD) return 0;
        for (int i = 0; i < g->deg[u]; i++)
            if (g->adj[u][i] == v) return 0;
        add_edge(g, u, v);
    }
    for (int v = 0; v < n; v++)
        if (g->deg[v] > d) return 0;
    static int q[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->side[s] >= 0) continue;
        int h = 0, t = 0;
        g->side[s] = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int i = 0; i < g->deg[u]; i++) {
                int v = g->adj[u][i];
                if (g->side[v] < 0) {
                    g->side[v] = 1 - g->side[u];
                    q[t++] = v;
                } else if (g->side[v] == g->side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
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

static Graph cur, best, work;

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 8; i++) rnd();

    if (!read_graph(&cur) || bad_pairs(&cur) != 0) {
        printf("0 0\n");
        return 0;
    }
    copy_graph(&best, &cur);
    double t_end = now() + budget * 0.92;

    while (now() < t_end) {
        copy_graph(&work, &cur);
        int k = 1 + rndint(3);
        if (work.n - k < 2) break;
        int pick[3];
        for (int i = 0; i < k; i++) {
            int v, ok;
            do {
                v = rndint(work.n);
                ok = 1;
                for (int j = 0; j < i; j++)
                    if (pick[j] == v) ok = 0;
            } while (!ok);
            pick[i] = v;
        }
        /* Remove in descending label order so later labels stay valid. */
        for (int i = 0; i < k; i++)
            for (int j = i + 1; j < k; j++)
                if (pick[j] > pick[i]) {
                    int t = pick[i];
                    pick[i] = pick[j];
                    pick[j] = t;
                }
        for (int i = 0; i < k; i++) remove_vertex(&work, pick[i]);

        for (int att = 0; att < k + 3; att++) {
            int X = rndint(2);
            if (!try_add(&work, X) && !try_add(&work, 1 - X)) break;
        }

        if (work.n < cur.n - 1) continue;
        if (work.n == cur.n - 1 && rnd01() >= 0.02) continue;
        if (bad_pairs(&work) != 0) continue;
        copy_graph(&cur, &work);
        if (cur.n > best.n) copy_graph(&best, &cur);
    }

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

def _run_swap(n0, e0, d, D, seed, budget):
    text = lib.run_c(C_SWAP, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=budget + 10.0)
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

    # Already at the Moore bound: nothing can beat it, so return at once.
    if best[0] >= lib.moore_bound(d, D):
        return best

    # SWAP engine: remove-and-reinsert plateau search with the rest of the budget.
    remaining = hard_end - time.monotonic()
    if remaining > 3.0:
        try:
            n1, e1 = _run_swap(best[0], best[1], d, D, seed * 31 + 1,
                               max(0.5, remaining - 2.0))
            if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                best = (n1, e1)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
