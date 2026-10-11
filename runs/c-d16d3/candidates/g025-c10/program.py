"""Diameter-3 bipartite search: arc-extended projective plane starts plus a C local search.

Starts are valid graphs: the arc-extended PG(2,q) incidence graph (diameter 3), the generalized
quadrangle W(q) for D >= 4, or K_{d,d}. The C engine first grows the graph with strict additions:
a new vertex joins a set T of spare vertices chosen by greedy set cover, and is kept only if the
whole graph is still within distance D.

Then it runs an iterated local search, which is the new idea here. It deletes 1-3 random vertices,
greedily refills with 1-3 new vertices (non-strict cover), and keeps the result only if the graph is
still valid and not smaller. Balls are bitsets, so each validity check is cheap. After a long stall
it restarts from the best graph found. Python re-checks everything with lib.is_valid.
"""
import itertools
import random
import time

import lib

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXS 1024
#define WORDS (MAXS / 64)
#define MAXDEG 64
#define STALL_LIMIT 1500

typedef struct {
    int S_total, nalive;
    int alive[MAXS], deg[MAXS], side[MAXS];
    int adj[MAXS][MAXDEG];
} State;

static State G, SAVE, BEST;
static int Dd, Dist;
static uint64_t ball[MAXS][WORDS];
static uint64_t tmpb[MAXS][WORDS];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int count_bits(const uint64_t *w) {
    int c = 0;
    for (int i = 0; i < WORDS; i++) c += popc(w[i]);
    return c;
}

/* ball[v] = set of alive vertices within distance r of v (bitset over slots). */
static void compute_balls(int r) {
    for (int v = 0; v < G.S_total; v++) {
        for (int i = 0; i < WORDS; i++) ball[v][i] = 0;
        if (G.alive[v]) ball[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < G.S_total; v++) {
            if (!G.alive[v]) continue;
            for (int i = 0; i < WORDS; i++) tmpb[v][i] = ball[v][i];
            for (int k = 0; k < G.deg[v]; k++) {
                int u = G.adj[v][k];
                for (int i = 0; i < WORDS; i++) tmpb[v][i] |= ball[u][i];
            }
        }
        for (int v = 0; v < G.S_total; v++) {
            if (!G.alive[v]) continue;
            for (int i = 0; i < WORDS; i++) ball[v][i] = tmpb[v][i];
        }
    }
}

/* Full check: every pair within Dist, edges bichromatic, degrees within Dd. */
static int full_valid(void) {
    compute_balls(Dist);
    for (int v = 0; v < G.S_total; v++) {
        if (!G.alive[v]) continue;
        if (count_bits(ball[v]) != G.nalive) return 0;
        if (G.deg[v] > Dd) return 0;
        for (int k = 0; k < G.deg[v]; k++)
            if (G.side[G.adj[v][k]] == G.side[v]) return 0;
    }
    return 1;
}

static int free_slot(void) {
    for (int i = 0; i < G.S_total; i++)
        if (!G.alive[i]) return i;
    if (G.S_total >= MAXS) return -1;
    return G.S_total++;
}

static void add_edge(int u, int v) {
    G.adj[u][G.deg[u]++] = v;
    G.adj[v][G.deg[v]++] = u;
}

static void remove_vertex(int v) {
    for (int k = 0; k < G.deg[v]; k++) {
        int u = G.adj[v][k];
        for (int j = 0; j < G.deg[u]; j++) {
            if (G.adj[u][j] == v) {
                G.adj[u][j] = G.adj[u][G.deg[u] - 1];
                G.deg[u]--;
                break;
            }
        }
    }
    G.deg[v] = 0;
    G.alive[v] = 0;
    G.nalive--;
}

/* Add one vertex on side X joined to a greedy cover T of the alive vertices by
   radius Dist-1 balls. If strict, fail unless the cover is complete. */
static int add_vertex(int X, int strict) {
    uint64_t U[WORDS];
    int T[MAXDEG], nt = 0;
    static char sel[MAXS];
    if (G.nalive + 2 >= MAXS) return 0;
    compute_balls(Dist - 1);
    for (int i = 0; i < WORDS; i++) U[i] = 0;
    for (int v = 0; v < G.S_total; v++)
        if (G.alive[v]) U[v >> 6] |= 1ULL << (v & 63);
    memset(sel, 0, sizeof(sel));
    while (nt < Dd) {
        int best = -1;
        long bsc = -1;
        for (int v = 0; v < G.S_total; v++) {
            if (!G.alive[v] || G.side[v] == X || G.deg[v] >= Dd || sel[v]) continue;
            int g = 0;
            for (int i = 0; i < WORDS; i++) g += popc(ball[v][i] & U[i]);
            if (g <= 0) continue;
            long sc = (long)g * 16 + rndint(16);
            if (sc > bsc) {
                bsc = sc;
                best = v;
            }
        }
        if (best < 0) break;
        sel[best] = 1;
        T[nt++] = best;
        for (int i = 0; i < WORDS; i++) U[i] &= ~ball[best][i];
    }
    if (nt == 0) return 0;
    if (strict) {
        for (int i = 0; i < WORDS; i++)
            if (U[i]) return 0;
    }
    int x = free_slot();
    if (x < 0) return 0;
    G.alive[x] = 1;
    G.side[x] = X;
    G.deg[x] = 0;
    G.nalive++;
    for (int k = 0; k < nt; k++) add_edge(x, T[k]);
    return 1;
}

/* Iterated local search move: remove 1-3 vertices, refill, keep if valid and not smaller.
   Returns 1 if the graph strictly grew. */
static int perturb(void) {
    int old = G.nalive;
    SAVE = G;
    int r = 1 + rndint(3);
    for (int i = 0; i < r; i++) {
        int v = -1, tries = 0;
        do {
            v = rndint(G.S_total);
            tries++;
        } while (!G.alive[v] && tries < 100000);
        if (!G.alive[v]) break;
        remove_vertex(v);
    }
    int adds = r + rndint(2);
    int ok = 1;
    for (int i = 0; i < adds; i++) {
        int X = rndint(2);
        if (!add_vertex(X, 0)) {
            if (!add_vertex(1 - X, 0)) {
                ok = 0;
                break;
            }
        }
    }
    if (!ok || G.nalive < old || !full_valid()) {
        G = SAVE;
        return 0;
    }
    if (G.nalive > BEST.nalive) BEST = G;
    return G.nalive > old;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    if (Dd > MAXDEG) Dd = MAXDEG;
    Dist = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXS - 64 || Dist < 2 || Dd < 1) {
        printf("0 0\n");
        return 0;
    }
    memset(&G, 0, sizeof(G));
    G.S_total = n;
    G.nalive = n;
    for (int i = 0; i < n; i++) G.alive[i] = 1;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= n || v < 0 || v >= n || u == v) continue;
        if (G.deg[u] >= Dd || G.deg[v] >= Dd) continue;
        int dup = 0;
        for (int k = 0; k < G.deg[u]; k++)
            if (G.adj[u][k] == v) dup = 1;
        if (dup) continue;
        add_edge(u, v);
    }

    /* 2-colour the start graph (components coloured independently). */
    for (int v = 0; v < n; v++) G.side[v] = -1;
    {
        static int qu[MAXS];
        for (int s = 0; s < n; s++) {
            if (G.side[s] >= 0) continue;
            G.side[s] = 0;
            int head = 0, t = 0;
            qu[t++] = s;
            while (head < t) {
                int u = qu[head++];
                for (int k = 0; k < G.deg[u]; k++) {
                    int v = G.adj[u][k];
                    if (G.side[v] < 0) {
                        G.side[v] = 1 - G.side[u];
                        qu[t++] = v;
                    }
                }
            }
        }
    }

    BEST = G;
    double t_end = elapsed() + budget;
    int phase = 0, fails = 0, stall = 0;
    while (elapsed() < t_end) {
        if (phase == 0) {
            SAVE = G;
            int X = rndint(2);
            int ok = add_vertex(X, 1);
            if (!ok) ok = add_vertex(1 - X, 1);
            if (ok && full_valid()) {
                fails = 0;
            } else {
                G = SAVE;
                if (++fails > 200) phase = 1;
            }
            if (G.nalive > BEST.nalive) BEST = G;
        } else {
            if (perturb()) stall = 0;
            else if (++stall > STALL_LIMIT) {
                G = BEST;
                stall = 0;
            }
        }
    }

    static int id[MAXS];
    int c = 0;
    for (int v = 0; v < BEST.S_total; v++) id[v] = BEST.alive[v] ? c++ : -1;
    int M = 0;
    for (int v = 0; v < BEST.S_total; v++) {
        if (!BEST.alive[v]) continue;
        for (int k = 0; k < BEST.deg[v]; k++)
            if (BEST.adj[v][k] > v) M++;
    }
    printf("%d %d\n", c, M);
    for (int v = 0; v < BEST.S_total; v++) {
        if (!BEST.alive[v]) continue;
        for (int k = 0; k < BEST.deg[v]; k++) {
            int u = BEST.adj[v][k];
            if (u > v) printf("%d %d\n", id[v], id[u]);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has spare capacity s = d - q - 1. Choose a point set S that is an arc, so each
# line holds at most s points of S. Add an A-vertex for each P in S (joined to
# lines through P) and a B-vertex for each j in S (joined to points on line j).
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
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4), used for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
# C search driver.
# ----------------------------------------------------------------------------

def _augment(n0, e0, d, D, seed, budget):
    """Run the C engine from the start graph (n0, e0) for `budget` seconds and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=budget + 5.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 85% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.85 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))

    starts = []
    if D >= 3:
        starts.extend(_arc_extensions(d, t0 + 0.2 * time_limit, rng))
    if D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    starts = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    starts.sort(key=lambda g: -g[0])
    if lib.is_valid(fallback[0], fallback[1], d, D):
        starts.append(fallback)
    if not starts:
        return 1, []
    best = starts[0]

    # Already at the Moore bound: nothing can be gained, return instantly.
    if best[0] >= lib.moore_bound(d, D):
        return best

    for idx, src in enumerate(starts[:2]):
        remaining = hard_end - time.monotonic()
        if remaining < 3.0:
            break
        budget = remaining - 4.0
        try:
            n1, e1 = _augment(src[0], src[1], d, D, seed * 31 + idx, budget)
        except Exception:
            continue
        if n1 > best[0] and lib.is_valid(n1, e1, d, D):
            best = (n1, e1)
        break

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
