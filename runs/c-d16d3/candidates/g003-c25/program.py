"""Diameter-3 bipartite search: arc-extended projective plane starts plus a C augmentation engine.

Starts are valid graphs: arc-extended PG(2,q) incidence, the generalized quadrangle W(q)
for D >= 4, or K_{d,d}. The C engine adds one vertex at a time on a random side, joined to
a set T of spare vertices on the other side. A vertex is accepted only if every vertex of the
graph lies within distance D-1 of T, so the new vertex is within distance D of everything.
Adding vertices never increases existing distances, so the graph stays valid.

New in this version: when the greedy set cover for T fails, the C engine runs a
WalkSAT-style cover repair. It picks a random uncovered vertex, adds a spare vertex that covers
it (or swaps out the T member that uniquely covers the fewest vertices), and retries. When
insertions stall, it adds random spare-to-spare edges. Those only shrink distances, so validity
is kept and the spare capacity used by covers grows. Python re-checks everything with lib.is_valid.
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
#define RESTARTS 6
#define REPAIR_ITERS 100

static int N, Dd, Dist, W;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static uint64_t ball[MAXN][WORDS];
static int mark[MAXN], lev[MAXN], bq[MAXN];
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;
static int cnt[MAXN];
static uint64_t Ub[WORDS], Ob[WORDS];

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

static int getbit(const uint64_t *b, int i) { return (int)((b[i >> 6] >> (i & 63)) & 1ULL); }
static void setbit(uint64_t *b, int i) { b[i >> 6] |= 1ULL << (i & 63); }

static int isadj(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) return 1;
    return 0;
}

static int in_set(const int *T, int nt, int v) {
    for (int k = 0; k < nt; k++)
        if (T[k] == v) return 1;
    return 0;
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

/* Cover state of the vertex set T: cnt[v] = number of T members within reach of v.
   Ub = uncovered vertices, Ob = vertices covered exactly once. Returns #uncovered. */
static int build_state(const int *T, int nt) {
    int unc = 0;
    for (int w = 0; w < WORDS; w++) {
        Ub[w] = 0;
        Ob[w] = 0;
    }
    for (int v = 0; v < N; v++) cnt[v] = 0;
    for (int k = 0; k < nt; k++)
        for (int v = 0; v < N; v++)
            if (getbit(ball[T[k]], v)) cnt[v]++;
    for (int v = 0; v < N; v++) {
        if (cnt[v] == 0) {
            setbit(Ub, v);
            unc++;
        } else if (cnt[v] == 1) {
            setbit(Ob, v);
        }
    }
    return unc;
}

/* Randomized greedy set cover of all vertices by spare vertices on the side opposite X. */
static void greedy_build(int X, int *T, int *nt) {
    uint64_t G[WORDS];
    for (int w = 0; w < W; w++) G[w] = ~0ULL;
    if (N & 63) G[W - 1] = (1ULL << (N & 63)) - 1ULL;
    *nt = 0;
    while (*nt < Dd) {
        int best = -1;
        long bestsc = -1;
        for (int v = 0; v < N; v++) {
            if (side[v] == X || deg[v] >= Dd) continue;
            if (in_set(T, *nt, v)) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(ball[v][w] & G[w]);
            if (g <= 0) continue;
            long sc = (long)g * 16 + rndint(16);
            if (sc > bestsc) {
                bestsc = sc;
                best = v;
            }
        }
        if (best < 0) break;
        T[(*nt)++] = best;
        int left = 0;
        for (int w = 0; w < W; w++) {
            G[w] &= ~ball[best][w];
            left |= (G[w] != 0);
        }
        if (!left) break;
    }
}

/* WalkSAT-style cover repair: fix a random uncovered vertex by adding a covering spare vertex,
   replacing the T member that uniquely covers the fewest vertices when T is full. */
static int repair(int X, int *T, int *nt, int iters) {
    for (int it = 0; it < iters; it++) {
        int unc = build_state(T, *nt);
        if (unc == 0) return 1;
        int r = rndint(unc), e = -1;
        for (int v = 0; v < N && e < 0; v++) {
            if (getbit(Ub, v)) {
                if (r == 0) e = v;
                else r--;
            }
        }
        int best = -1;
        long bestsc = -1;
        for (int c = 0; c < N; c++) {
            if (side[c] == X || deg[c] >= Dd) continue;
            if (!getbit(ball[c], e)) continue;
            if (in_set(T, *nt, c)) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(ball[c][w] & Ub[w]);
            long sc = (long)g * 16 + rndint(16);
            if (sc > bestsc) {
                bestsc = sc;
                best = c;
            }
        }
        if (best < 0) return 0;
        if (*nt < Dd) {
            T[(*nt)++] = best;
            continue;
        }
        int ridx = 0;
        if (rndint(100) < 10) {
            ridx = rndint(*nt);
        } else {
            long bl = -1;
            for (int k = 0; k < *nt; k++) {
                int loss = 0;
                for (int w = 0; w < W; w++) loss += popc(ball[T[k]][w] & Ob[w]);
                long sc = (long)loss * 8 + rndint(8);
                if (bl < 0 || sc < bl) {
                    bl = sc;
                    ridx = k;
                }
            }
        }
        T[ridx] = best;
    }
    return build_state(T, *nt) == 0;
}

/* Try to add one new vertex on side X. Returns 1 if the graph grew. */
static int try_add(int X) {
    int T[MAXDEG];
    int nt = 0;
    int ok = 0;
    if (N + 1 >= MAXN) return 0;
    for (int rep = 0; rep < RESTARTS && !ok; rep++) {
        greedy_build(X, T, &nt);
        if (build_state(T, nt) == 0) ok = 1;
        else ok = repair(X, T, &nt, REPAIR_ITERS);
    }
    if (!ok || nt == 0) return 0;
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

/* Add one edge between spare vertices on opposite sides. Distances only shrink. */
static int add_random_edge(void) {
    for (int tries = 0; tries < 200; tries++) {
        int u = rndint(N), v = rndint(N);
        if (side[u] < 0 || side[v] < 0 || side[u] == side[v]) continue;
        if (deg[u] >= Dd || deg[v] >= Dd) continue;
        if (isadj(u, v)) continue;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
        return 1;
    }
    return 0;
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
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= Dd || deg[v] >= Dd || isadj(u, v)) continue;
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
    int fails = 0;
    while (elapsed() < t_end && N < MAXN - 2 && fails < 6000) {
        int X = rndint(2);
        if (try_add(X)) {
            fails = 0;
        } else {
            fails++;
            if (fails % 40 == 0) {
                int added = 0;
                for (int k = 0; k < 3; k++) added += add_random_edge();
                if (added) recompute_balls();
            }
        }
    }

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
# C augmentation driver.
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
    best = max(starts, key=lambda g: g[0])

    # Stage 1: the largest start gets most of the remaining time.
    # Stage 2: keep augmenting the best result with the rest.
    cur = best
    for idx in range(2):
        remaining = hard_end - time.monotonic()
        if remaining < 3.0:
            break
        share = remaining * (0.7 if idx == 0 else 1.0)
        try:
            n1, e1 = _augment(cur[0], cur[1], d, D, seed * 31 + idx,
                              max(0.5, share - 1.0), share + 3.0)
        except Exception:
            break
        if n1 > best[0] and lib.is_valid(n1, e1, d, D):
            best = (n1, e1)
            cur = best

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
