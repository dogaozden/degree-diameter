"""Diameter-3 bipartite search: arc-extended projective plane starts plus a C engine.

The C engine has two phases:
1. Greedy augmentation: add a vertex on a random side, joined to a set T of spare
   vertices on the other side (greedy set cover), accepted only if every existing
   vertex lies within distance D-1 of T.
2. Remove-and-repair local search (new in this version): delete one or two random
   vertices, repair the broken distances by adding edges between opposite-side pairs
   that are too far apart and still have spare degree (adding edges never breaks
   validity), regrow with greedy augmentation, and keep the result if it is valid and
   not smaller (occasionally accepting a small loss). The best valid graph is printed.

Distance balls are computed with bitset propagation, which is much faster than BFS.
Python re-checks everything with lib.is_valid and falls back to K_{d,d}.
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

typedef struct {
    int N;
    int deg[MAXN];
    int adj[MAXN][MAXDEG];
    int side[MAXN];
} Snap;

static int N, Dd, Dist, W;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static uint64_t ball[MAXN][WORDS];   /* radius Dist-1 */
static uint64_t bfull[MAXN][WORDS];  /* radius Dist */
static uint64_t cur_r[MAXN][WORDS], nxt_r[MAXN][WORDS];
static int bq[MAXN];
static uint64_t rs = 88172645463325252ULL;
static Snap prevS, bestS;

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

static int bit(const uint64_t *b, int v) {
    return (int)((b[v >> 6] >> (v & 63)) & 1ULL);
}

/* out[v] = set of vertices within distance r of v, computed by bitset propagation. */
static void balls_radius(int r, uint64_t (*out)[WORDS]) {
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < W; i++) cur_r[v][i] = 0;
        cur_r[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < N; v++) {
            for (int i = 0; i < W; i++) nxt_r[v][i] = cur_r[v][i];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = cur_r[adj[v][k]];
                for (int i = 0; i < W; i++) nxt_r[v][i] |= src[i];
            }
        }
        for (int v = 0; v < N; v++)
            for (int i = 0; i < W; i++) cur_r[v][i] = nxt_r[v][i];
    }
    for (int v = 0; v < N; v++)
        for (int i = 0; i < W; i++) out[v][i] = cur_r[v][i];
}

static void recompute_balls(void) { balls_radius(Dist - 1, ball); }

static void compute_full(void) { balls_radius(Dist, bfull); }

/* Try to add one new vertex on side X. Returns 1 if the graph grew. */
static int try_add(int X) {
    uint64_t U[WORDS];
    int sel[MAXN];
    int T[MAXDEG];
    int nt = 0;
    if (N + 1 >= MAXN) return 0;
    for (int i = 0; i < W; i++) U[i] = ~0ULL;
    if (N & 63) U[W - 1] = (1ULL << (N & 63)) - 1ULL;
    memset(sel, 0, sizeof(sel));
    while (nt < Dd) {
        int best = -1;
        long bestsc = -1;
        for (int v = 0; v < N; v++) {
            if (side[v] == X || deg[v] >= Dd || sel[v]) continue;
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

static void grow(int maxfail) {
    int fails = 0;
    while (fails < maxfail && N < MAXN - 2) {
        if (try_add(rndint(2))) fails = 0;
        else fails++;
    }
}

static void save_snap(Snap *s) {
    s->N = N;
    memcpy(s->deg, deg, sizeof(deg));
    memcpy(s->adj, adj, sizeof(adj));
    memcpy(s->side, side, sizeof(side));
}

static void load_snap(const Snap *s) {
    N = s->N;
    W = (N + 63) / 64;
    memcpy(deg, s->deg, sizeof(deg));
    memcpy(adj, s->adj, sizeof(adj));
    memcpy(side, s->side, sizeof(side));
}

/* Delete vertex x; the last vertex is moved into slot x so labels stay 0..N-1. */
static void remove_vertex(int x) {
    int last = N - 1;
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
    deg[x] = 0;
    if (x != last) {
        for (int k = 0; k < deg[last]; k++) {
            int t = adj[last][k];
            for (int j = 0; j < deg[t]; j++) {
                if (adj[t][j] == last) {
                    adj[t][j] = x;
                    break;
                }
            }
        }
        memcpy(adj[x], adj[last], sizeof(int) * MAXDEG);
        deg[x] = deg[last];
        side[x] = side[last];
    }
    deg[last] = 0;
    N = last;
    W = (N + 63) / 64;
}

/* Add edges between opposite-side pairs that are too far apart and have spare degree.
   Adding an edge never increases a distance, so this cannot break existing paths. */
static void repair(void) {
    int limit = 4 * Dd + 16;
    for (int it = 0; it < limit; it++) {
        compute_full();
        int cnt = 0, pu = -1, pv = -1;
        for (int u = 0; u < N; u++) {
            if (deg[u] >= Dd) continue;
            for (int v = u + 1; v < N; v++) {
                if (side[v] == side[u] || deg[v] >= Dd) continue;
                if (bit(bfull[u], v)) continue;
                cnt++;
                if (rndint(cnt) == 0) {
                    pu = u;
                    pv = v;
                }
            }
        }
        if (cnt == 0) break;
        adj[pu][deg[pu]++] = pv;
        adj[pv][deg[pv]++] = pu;
    }
}

static int full_valid(void) {
    for (int v = 0; v < N; v++) {
        if (deg[v] > Dd) return 0;
        for (int k = 0; k < deg[v]; k++)
            if (side[adj[v][k]] == side[v]) return 0;
    }
    compute_full();
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int i = 0; i < W; i++) c += popc(bfull[v][i]);
        if (c != N) return 0;
    }
    return 1;
}

static void print_graph(void) {
    int M = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) M++;
    printf("%d %d\n", N, M);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) printf("%d %d\n", v, adj[v][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    if (Dd > MAXDEG) Dd = MAXDEG;
    if (Dd < 1) Dd = 1;
    Dist = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 2 || Dist < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    W = (N + 63) / 64;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= Dd || deg[v] >= Dd) continue;
        int dup = 0;
        for (int k = 0; k < deg[u]; k++)
            if (adj[u][k] == v) {
                dup = 1;
                break;
            }
        if (dup) continue;
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

    recompute_balls();
    double t_end = elapsed() + budget;

    if (!full_valid()) {
        print_graph();
        return 0;
    }
    save_snap(&bestS);
    grow(60);
    if (full_valid() && N > bestS.N) save_snap(&bestS);
    else load_snap(&bestS);
    recompute_balls();

    while (elapsed() < t_end) {
        int n0 = N;
        save_snap(&prevS);
        int k = (rndint(100) < 75) ? 1 : 2;
        for (int r = 0; r < k && N > 2; r++) remove_vertex(rndint(N));
        repair();
        recompute_balls();
        grow(40);
        int ok = full_valid();
        if (ok && (N >= n0 || rndint(100) < 3)) {
            if (N > bestS.N) save_snap(&bestS);
        } else {
            load_snap(&prevS);
        }
        if (N < bestS.N - 4 && rndint(20) == 0) load_snap(&bestS);
        recompute_balls();
    }

    load_snap(&bestS);
    print_graph();
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
    best = max(starts, key=lambda g: g[0])

    # Already at the Moore bound: nothing to improve.
    if best[0] >= lib.moore_bound(d, D):
        return best

    # Local search from the two largest distinct starts, then from the best result.
    plan = starts[:2]
    for idx in range(len(plan) + 1):
        remaining = hard_end - time.monotonic()
        if remaining < 2.0:
            break
        if idx < len(plan):
            src = plan[idx]
            share = min(remaining, 0.2 * time_limit)
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
