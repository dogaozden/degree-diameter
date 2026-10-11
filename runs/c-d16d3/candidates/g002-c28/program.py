"""Diameter-3 bipartite search: projective-plane starts plus a C iterated local search.

Starts: for each prime power q with q + 1 <= d, the plain incidence graph of PG(2, q), and an
arc-extended version that uses the spare degree s = d - q - 1 with extra A and B vertices.
The C engine has two phases:
  1. Greedy augmentation. A new vertex on side X joins a set T of spare vertices on the other
     side (greedy set cover). It is accepted only if every existing vertex lies within
     distance D-1 of T, which keeps the whole graph valid.
  2. Iterated local search (new in this version). It removes one or two random vertices,
     checks full validity by BFS, and, if the graph is still valid, regrows it greedily.
     The move is kept if the order does not drop, and otherwise the snapshot is restored.
     The best valid graph seen is returned.
Python re-checks every result with lib.is_valid.
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

#define MAXN 1024
#define WORDS (MAXN / 64)
#define MAXDEG 64

typedef struct {
    int N;
    int deg[MAXN];
    int adj[MAXN][MAXDEG];
    int side[MAXN];
} State;

static State G, SAVE, BEST;
static int Dd, Dist, W;
static uint64_t ball[MAXN][WORDS];
static int mark[MAXN], lev[MAXN], bq[MAXN];
static int stamp = 0;
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

static void set_W(void) { W = (G.N + 63) / 64; }

/* Bitset of all vertices within distance r of src in the current G. */
static void ball_of(int src, int r, uint64_t *bits) {
    int head = 0, t = 0;
    stamp++;
    for (int i = 0; i < W; i++) bits[i] = 0;
    bq[t++] = src;
    mark[src] = stamp;
    lev[src] = 0;
    while (head < t) {
        int u = bq[head++];
        bits[u >> 6] |= 1ULL << (u & 63);
        if (lev[u] >= r) continue;
        for (int k = 0; k < G.deg[u]; k++) {
            int v = G.adj[u][k];
            if (mark[v] != stamp) {
                mark[v] = stamp;
                lev[v] = lev[u] + 1;
                bq[t++] = v;
            }
        }
    }
}

static void recompute_balls(void) {
    for (int v = 0; v < G.N; v++) ball_of(v, Dist - 1, ball[v]);
}

/* True iff every pair of vertices of G is within distance Dist. */
static int full_valid(void) {
    uint64_t b[WORDS];
    int N = G.N;
    set_W();
    for (int v = 0; v < N; v++) {
        ball_of(v, Dist, b);
        for (int i = 0; i < W; i++) {
            uint64_t want = ~0ULL;
            if (i == W - 1 && (N & 63)) want = (1ULL << (N & 63)) - 1ULL;
            if ((b[i] & want) != want) return 0;
        }
    }
    return 1;
}

/* Try to add one new vertex on side X. Returns 1 if the graph grew. */
static int try_add(int X) {
    uint64_t U[WORDS];
    int sel[MAXN];
    int T[MAXDEG];
    int nt = 0;
    if (G.N + 1 >= MAXN) return 0;
    for (int i = 0; i < W; i++) U[i] = ~0ULL;
    if (G.N & 63) U[W - 1] = (1ULL << (G.N & 63)) - 1ULL;
    memset(sel, 0, sizeof(sel));
    while (nt < Dd) {
        int best = -1;
        long bestsc = -1;
        for (int v = 0; v < G.N; v++) {
            if (G.side[v] == X || G.deg[v] >= Dd || sel[v]) continue;
            int g = 0;
            for (int i = 0; i < W; i++) g += popc(ball[v][i] & U[i]);
            if (g <= 0) continue;
            long sc = (long)g * 8 + rndint(8);
            if (sc > bestsc) {
                bestsc = sc;
                best = v;
            }
        }
        if (best < 0) break;
        sel[best] = 1;
        T[nt++] = best;
        for (int i = 0; i < W; i++) U[i] &= ~ball[best][i];
    }
    for (int i = 0; i < W; i++)
        if (U[i]) return 0;
    if (nt == 0) return 0;
    int x = G.N;
    G.side[x] = X;
    G.deg[x] = nt;
    for (int k = 0; k < nt; k++) {
        int t = T[k];
        G.adj[x][k] = t;
        G.adj[t][G.deg[t]++] = x;
    }
    G.N++;
    set_W();
    recompute_balls();
    return 1;
}

/* Delete vertex v and move the last vertex into its slot, so ids stay 0..N-1. */
static void remove_vertex(int v) {
    int last = G.N - 1;
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
    if (v != last) {
        for (int k = 0; k < G.deg[last]; k++) {
            int u = G.adj[last][k];
            for (int j = 0; j < G.deg[u]; j++) {
                if (G.adj[u][j] == last) {
                    G.adj[u][j] = v;
                    break;
                }
            }
        }
        G.deg[v] = G.deg[last];
        memcpy(G.adj[v], G.adj[last], sizeof(G.adj[v]));
        G.side[v] = G.side[last];
    }
    G.deg[last] = 0;
    G.N--;
    set_W();
}

/* Greedy growth: stop after maxfails consecutive failures or at the time limit. */
static int grow(int maxfails, double t_end) {
    int fails = 0, added = 0;
    while (fails < maxfails && G.N < MAXN - 2 && elapsed() < t_end) {
        if (try_add(rndint(2))) {
            fails = 0;
            added++;
        } else {
            fails++;
        }
    }
    return added;
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
    if (n <= 0 || n > MAXN - 2 || Dist < 1) {
        printf("0 0\n");
        return 0;
    }
    memset(&G, 0, sizeof(G));
    G.N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= n || v < 0 || v >= n || u == v) continue;
        if (G.deg[u] >= Dd || G.deg[v] >= Dd) continue;
        G.adj[u][G.deg[u]++] = v;
        G.adj[v][G.deg[v]++] = u;
    }

    for (int v = 0; v < G.N; v++) G.side[v] = -1;
    for (int s = 0; s < G.N; s++) {
        if (G.side[s] >= 0) continue;
        G.side[s] = 0;
        int head = 0, t = 0;
        bq[t++] = s;
        while (head < t) {
            int u = bq[head++];
            for (int k = 0; k < G.deg[u]; k++) {
                int v = G.adj[u][k];
                if (G.side[v] < 0) {
                    G.side[v] = 1 - G.side[u];
                    bq[t++] = v;
                }
            }
        }
    }

    double t_end = elapsed() + budget;
    set_W();
    recompute_balls();
    grow(300, t_end);
    BEST = G;

    long stall = 0;
    while (elapsed() < t_end && G.N > 2) {
        stall++;
        SAVE = G;
        int nrem = 1 + rndint(2);
        for (int r = 0; r < nrem && G.N > 2; r++) remove_vertex(rndint(G.N));
        if (!full_valid()) {
            G = SAVE;
            set_W();
            recompute_balls();
        } else {
            recompute_balls();
            grow(40, t_end);
            if (G.N > BEST.N) {
                BEST = G;
                stall = 0;
            }
            if (G.N < SAVE.N) {
                G = SAVE;
                set_W();
                recompute_balls();
            }
        }
        if (BEST.N <= 64 && stall > 3000) break;
    }

    int M = 0;
    for (int v = 0; v < BEST.N; v++)
        for (int k = 0; k < BEST.deg[v]; k++)
            if (BEST.adj[v][k] > v) M++;
    printf("%d %d\n", BEST.N, M);
    for (int v = 0; v < BEST.N; v++)
        for (int k = 0; k < BEST.deg[v]; k++)
            if (BEST.adj[v][k] > v) printf("%d %d\n", v, BEST.adj[v][k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Projective plane starts (diameter 3).
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


def _pg_starts(d, deadline, rng):
    """Plain PG(2,q) incidence graphs and arc-extended versions, for each prime power q with q+1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q) or time.monotonic() > deadline:
            continue
        out.append(lib.projective_plane_incidence(q))
        s = d - q - 1
        if s < 1:
            continue
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[]]
        cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if S and _loads_ok(S, s, m, pl, lp):
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
# C driver.
# ----------------------------------------------------------------------------

def _augment(n0, e0, d, D, seed, budget, timeout):
    """Run the C engine from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=timeout)
    return lib.parse_graph_text(text)


def _improve(src, best, d, D, seed, share):
    """Run the engine from src for about `share` seconds; return the better valid graph."""
    try:
        n1, e1 = _augment(src[0], src[1], d, D, seed,
                          max(0.3, share - 1.0), share + 3.0)
    except Exception:
        return best
    if n1 > best[0] and lib.is_valid(n1, e1, d, D):
        return (n1, e1)
    return best


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 82% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.82 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))

    starts = []
    if D >= 3:
        starts.extend(_pg_starts(d, t0 + 0.2 * time_limit, rng))
    if D >= 4 and time.monotonic() < t0 + 0.25 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    starts = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    starts.sort(key=lambda g: -g[0])

    best = fallback if lib.is_valid(fallback[0], fallback[1], d, D) else (1, [])
    if starts and starts[0][0] > best[0]:
        best = starts[0]

    # Run the engine on the top starts, then continue on the best result.
    cands = starts[:3]
    fracs = [0.4, 0.25, 0.2]
    for idx, src in enumerate(cands):
        left = hard_end - time.monotonic()
        if left < 2.0:
            break
        share = min(left, (hard_end - t0) * fracs[idx])
        best = _improve(src, best, d, D, seed * 31 + idx, share)
    left = hard_end - time.monotonic()
    if left >= 2.0:
        best = _improve(best, best, d, D, seed * 31 + 9, left)

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
