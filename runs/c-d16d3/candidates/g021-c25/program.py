"""Diameter-3 bipartite search: arc-extended projective plane starts plus a C engine.

Each start is a valid graph (arc-extended PG(2,q) incidence, the generalized quadrangle
for D >= 4, or K_{d,d}). The C engine grows the graph by adding vertices. A new vertex on
side X is joined to a set T of spare vertices on the other side, found by randomized greedy
set cover with several noise levels. A vertex is accepted only if every existing vertex lies
within distance D-1 of T, so the new vertex is within distance D of everything. Adding
vertices never increases existing distances, so the graph stays valid.

New in this version: an iterated-local-search plateau walk. When growth stalls, the engine
removes a random vertex (swap-with-last compaction), keeps the result only if it is still
valid, regrows, and restores the snapshot if the vertex count dropped. The best valid graph
seen is always kept. Python re-checks everything with lib.is_valid.
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

#define MAXN 2048
#define WORDS (MAXN / 64)
#define MAXDEG 64
#define ATT 6

typedef struct {
    int N;
    int deg[MAXN];
    int adj[MAXN][MAXDEG];
    int side[MAXN];
} State;

static int N, Dd, Dist, W;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static uint64_t ball[MAXN][WORDS];
static int mark[MAXN], lev[MAXN], bq[MAXN];
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;
static State snap, bestS;

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

/* Bitset of all vertices within distance r of src. */
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
        for (int k = 0; k < deg[u]; k++) {
            int v = adj[u][k];
            if (mark[v] != stamp) {
                mark[v] = stamp;
                lev[v] = lev[u] + 1;
                bq[t++] = v;
            }
        }
    }
}

static void recompute_balls(void) {
    for (int v = 0; v < N; v++) ball_of(v, Dist - 1, ball[v]);
}

/* True if every pair of vertices is within distance Dist. */
static int full_ok(void) {
    uint64_t tmp[WORDS];
    for (int v = 0; v < N; v++) {
        ball_of(v, Dist, tmp);
        int c = 0;
        for (int i = 0; i < W; i++) c += popc(tmp[i]);
        if (c != N) return 0;
    }
    return 1;
}

static void save_state(State *s) {
    s->N = N;
    memcpy(s->deg, deg, sizeof deg);
    memcpy(s->adj, adj, sizeof adj);
    memcpy(s->side, side, sizeof side);
}

static void load_state(const State *s) {
    N = s->N;
    memcpy(deg, s->deg, sizeof deg);
    memcpy(adj, s->adj, sizeof adj);
    memcpy(side, s->side, sizeof side);
    W = (N + 63) / 64;
    recompute_balls();
}

/* Remove vertex x by moving the last vertex into its slot. Caller re-computes balls. */
static void remove_vertex(int x) {
    for (int k = 0; k < deg[x]; k++) {
        int t = adj[x][k];
        for (int j = 0; j < deg[t]; j++) {
            if (adj[t][j] == x) {
                adj[t][j] = adj[t][deg[t] - 1];
                deg[t]--;
                break;
            }
        }
    }
    int y = N - 1;
    if (x != y) {
        for (int k = 0; k < deg[y]; k++) {
            int t = adj[y][k];
            for (int j = 0; j < deg[t]; j++) {
                if (adj[t][j] == y) {
                    adj[t][j] = x;
                    break;
                }
            }
        }
        deg[x] = deg[y];
        side[x] = side[y];
        memcpy(adj[x], adj[y], sizeof(int) * MAXDEG);
    }
    deg[y] = 0;
    N--;
}

/* Randomized greedy set cover of all vertices by balls (radius Dist-1) of spare vertices on
   the side opposite to X. noise = 0 gives plain greedy; larger noise lets it deviate. */
static int cover_try(int X, int noise, int *T, int *ntOut) {
    uint64_t U[WORDS];
    static int sel[MAXN];
    int nt = 0;
    for (int i = 0; i < W; i++) U[i] = ~0ULL;
    if (N & 63) U[W - 1] = (1ULL << (N & 63)) - 1ULL;
    memset(sel, 0, sizeof(int) * (size_t)N);
    while (nt < Dd) {
        int best = -1;
        long bestsc = -1;
        for (int v = 0; v < N; v++) {
            if (side[v] == X || deg[v] >= Dd || sel[v]) continue;
            int g = 0;
            for (int i = 0; i < W; i++) g += popc(ball[v][i] & U[i]);
            if (g <= 0) continue;
            long sc = (long)g * 65536L + (noise > 0 ? (long)rndint(noise) : 0L);
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
    *ntOut = nt;
    return 1;
}

/* Try to add one new vertex. Returns 1 if the graph grew. */
static int try_add(void) {
    static const int levels[4] = {0, 32768, 98304, 196608};
    int T[MAXDEG];
    if (N + 2 >= MAXN) return 0;
    int X = rndint(2);
    for (int a = 0; a < ATT; a++) {
        int nt = 0;
        if (cover_try(X, levels[a & 3], T, &nt)) {
            int x = N;
            side[x] = X;
            deg[x] = nt;
            for (int k = 0; k < nt; k++) {
                int t = T[k];
                adj[x][k] = t;
                adj[t][deg[t]++] = x;
            }
            N++;
            W = (N + 63) / 64;
            recompute_balls();
            return 1;
        }
    }
    return 0;
}

static int grow(int maxfails, double t_end) {
    int fails = 0, added = 0;
    while (fails < maxfails && N < MAXN - 2 && elapsed() < t_end) {
        if (try_add()) {
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
    if (n <= 0 || n > MAXN - 2 || Dist < 1 || Dd < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= Dd || deg[v] >= Dd) continue;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }

    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, t = 0;
        bq[t++] = s;
        while (head < t) {
            int u = bq[head++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    bq[t++] = v;
                }
            }
        }
    }

    W = (N + 63) / 64;
    recompute_balls();

    double t_end = elapsed() + budget;
    save_state(&bestS);
    grow(200, t_end);
    if (N > bestS.N) save_state(&bestS);

    /* Iterated local search: remove a random vertex, keep only if still valid, regrow,
       and restore the snapshot if the vertex count dropped. */
    while (elapsed() < t_end) {
        grow(60, t_end);
        if (N > bestS.N) save_state(&bestS);
        if (N < 3 || N >= MAXN - 2) break;
        save_state(&snap);
        int Nprev = N;
        remove_vertex(rndint(N));
        W = (N + 63) / 64;
        recompute_balls();
        if (!full_ok()) {
            load_state(&snap);
            continue;
        }
        grow(20, t_end);
        if (N > bestS.N) save_state(&bestS);
        if (N < Nprev) load_state(&snap);
    }

    load_state(&bestS);
    int M = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) M++;
    printf("%d %d\n", N, M);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) printf("%d %d\n", v, adj[v][k]);
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
# C driver.
# ----------------------------------------------------------------------------

def _augment(n0, e0, d, D, seed, budget, timeout):
    """Run the C engine from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=timeout)
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

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))

    starts = []
    if D >= 3:
        starts.extend(_arc_extensions(d, t0 + 0.25 * time_limit, rng))
    if D >= 4 and time.monotonic() < t0 + 0.25 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    starts = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    starts.sort(key=lambda g: -g[0])
    if lib.is_valid(fallback[0], fallback[1], d, D):
        starts.append(fallback)
    if not starts:
        return 1, []
    best = max(starts, key=lambda g: g[0])

    # Augment the top starts with the C engine, then keep augmenting the best result.
    plan = starts[:3]
    for idx in range(len(plan) + 1):
        remaining = hard_end - time.monotonic()
        if remaining < 2.0:
            break
        if idx < len(plan):
            src = plan[idx]
            share = remaining / (len(plan) + 1 - idx)
        else:
            src = best
            share = remaining
        try:
            n1, e1 = _augment(src[0], src[1], d, D, seed * 31 + idx,
                              max(0.3, share - 1.0), share + 3.0)
        except Exception:
            continue
        if n1 > best[0] and lib.is_valid(n1, e1, d, D):
            best = (n1, e1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
