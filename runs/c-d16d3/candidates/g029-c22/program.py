"""Diameter-3 bipartite search: arc-extended projective plane starts plus a C repair-annealing engine.

New in this version: the C engine is a repair search at fixed order. Each round it adds one vertex
(greedy set cover over spare vertices of the other side), then anneals on the number of bad pairs
(vertex pairs at distance > D). Moves are degree-preserving 2-switches, endpoint rewires onto spare
vertices, and edge insertions between spare vertices. Bipartiteness and the degree cap are kept by
construction. Bad vertices are targeted with extra probability. A round that reaches zero bad pairs
becomes the new snapshot. A failed round restores the snapshot and tries again with fresh randomness.
Every snapshot is valid, and Python re-checks the output with lib.is_valid.
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
#include <math.h>
#include <time.h>

#define MAXN 2048
#define WORDS (MAXN / 64)
#define MAXDEG 48
#define MAXSNAP (MAXN * MAXDEG / 2)

typedef uint64_t row_t[WORDS];

static int N, Dd, Dist, W;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static unsigned char mat[MAXN][MAXN];
static int side[MAXN];
static row_t RA[MAXN], RB[MAXN];
static int badv[MAXN], badt[MAXN];
static int bq[MAXN];

static int snapN, snapM;
static int snapSide[MAXN];
static int snapE[MAXSNAP][2];

static int mv_nr, mv_na;
static int mv_r[2][2], mv_a[2][2];

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* reach[v] = bitset of vertices within distance `rounds` of v. Returns the buffer holding it. */
static row_t *reach_into(int rounds) {
    row_t *cur = RA, *nx = RB;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < W; i++) cur[v][i] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < rounds; r++) {
        for (int v = 0; v < N; v++) {
            for (int i = 0; i < W; i++) nx[v][i] = cur[v][i];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = cur[adj[v][k]];
                for (int i = 0; i < W; i++) nx[v][i] |= src[i];
            }
        }
        row_t *t = cur;
        cur = nx;
        nx = t;
    }
    return cur;
}

/* Number of unordered pairs at distance > Dist. Per-vertex counts go to badt. */
static int compute_bad(void) {
    row_t *R = reach_into(Dist);
    long tot = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int i = 0; i < W; i++) c += popc(R[v][i]);
        badt[v] = N - c;
        tot += N - c;
    }
    return (int)(tot / 2);
}

static int add_edge(int u, int v) {
    if (u == v || u < 0 || v < 0 || u >= N || v >= N) return 0;
    if (side[u] == side[v]) return 0;
    if (deg[u] >= Dd || deg[v] >= Dd || mat[u][v]) return 0;
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
    mat[u][v] = mat[v][u] = 1;
    return 1;
}

static void rm_from(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adj[u][k] == v) {
            adj[u][k] = adj[u][--deg[u]];
            return;
        }
    }
}

static void del_edge(int u, int v) {
    if (!mat[u][v]) return;
    rm_from(u, v);
    rm_from(v, u);
    mat[u][v] = mat[v][u] = 0;
}

static void clear_graph(void) {
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < deg[v]; k++) mat[v][adj[v][k]] = 0;
        deg[v] = 0;
    }
}

static void take_snapshot(void) {
    snapN = N;
    snapM = 0;
    for (int v = 0; v < N; v++) {
        snapSide[v] = side[v];
        for (int k = 0; k < deg[v]; k++) {
            int u = adj[v][k];
            if (u > v) {
                snapE[snapM][0] = v;
                snapE[snapM][1] = u;
                snapM++;
            }
        }
    }
}

static void restore_snapshot(void) {
    clear_graph();
    N = snapN;
    W = (N + 63) / 64;
    for (int v = 0; v < N; v++) side[v] = snapSide[v];
    for (int i = 0; i < snapM; i++) add_edge(snapE[i][0], snapE[i][1]);
}

/* Add one vertex on a random side, joined greedily to spare vertices that cover the most
   vertices within distance Dist-1. Exact validity is decided later by compute_bad. */
static void grow(void) {
    int X = rndint(2);
    int x = N;
    N++;
    W = (N + 63) / 64;
    side[x] = X;
    deg[x] = 0;
    row_t *R = reach_into(Dist - 1);
    row_t U;
    for (int i = 0; i < W; i++) U[i] = 0;
    for (int v = 0; v < x; v++) U[v >> 6] |= 1ULL << (v & 63);
    for (int k = 0; k < Dd; k++) {
        int best = -1;
        long bs = -1;
        for (int t = 0; t < x; t++) {
            if (side[t] == X || deg[t] >= Dd) continue;
            int g = 0;
            for (int i = 0; i < W; i++) g += popc(R[t][i] & U[i]);
            if (g <= 0) continue;
            long sc = (long)g * 16 + rndint(16);
            if (sc > bs) {
                bs = sc;
                best = t;
            }
        }
        if (best < 0) break;
        add_edge(x, best);
        for (int i = 0; i < W; i++) U[i] &= ~R[best][i];
    }
    if (deg[x] == 0) {
        for (int t = 0; t < x; t++) {
            if (side[t] != X && deg[t] < Dd && add_edge(x, t)) break;
        }
    }
}

static int pickv(void) {
    if (urand() < 0.5) {
        for (int t = 0; t < 8; t++) {
            int v = rndint(N);
            if (badv[v] > 0) return v;
        }
    }
    return rndint(N);
}

static int random_edge(int *p, int *q) {
    for (int t = 0; t < 50; t++) {
        int v = pickv();
        if (deg[v] == 0) continue;
        int u = adj[v][rndint(deg[v])];
        if (side[v] == 0) {
            *p = v;
            *q = u;
        } else {
            *p = u;
            *q = v;
        }
        return 1;
    }
    return 0;
}

/* A vertex on side s with spare degree, not equal to old, not adjacent to fixed. */
static int pick_spare(int s, int fixed, int old) {
    for (int t = 0; t < 40; t++) {
        int v = rndint(N);
        if (side[v] != s || deg[v] >= Dd || v == old || mat[v][fixed]) continue;
        return v;
    }
    return -1;
}

/* Propose a move and fill mv_*. Returns 0 if no valid move was found. */
static int propose(void) {
    mv_nr = mv_na = 0;
    double r = urand();
    if (r < 0.45) {
        /* degree-preserving 2-switch: (a,b),(c,d) -> (a,d),(c,b) */
        int a, b, c, d;
        if (!random_edge(&a, &b) || !random_edge(&c, &d)) return 0;
        if (a == c || b == d || mat[a][d] || mat[c][b]) return 0;
        mv_nr = 2;
        mv_r[0][0] = a; mv_r[0][1] = b;
        mv_r[1][0] = c; mv_r[1][1] = d;
        mv_na = 2;
        mv_a[0][0] = a; mv_a[0][1] = d;
        mv_a[1][0] = c; mv_a[1][1] = b;
        return 1;
    }
    if (r < 0.85) {
        /* endpoint rewire onto a spare vertex */
        int a, b;
        if (!random_edge(&a, &b)) return 0;
        mv_nr = 1;
        mv_r[0][0] = a; mv_r[0][1] = b;
        mv_na = 1;
        if (urand() < 0.5) {
            int ap = pick_spare(side[a], b, a);
            if (ap < 0) { mv_nr = mv_na = 0; return 0; }
            mv_a[0][0] = ap; mv_a[0][1] = b;
        } else {
            int bp = pick_spare(side[b], a, b);
            if (bp < 0) { mv_nr = mv_na = 0; return 0; }
            mv_a[0][0] = a; mv_a[0][1] = bp;
        }
        return 1;
    }
    /* edge insertion between two spare vertices */
    int u = -1;
    for (int t = 0; t < 40; t++) {
        int v = pickv();
        if (deg[v] < Dd) {
            u = v;
            break;
        }
    }
    if (u < 0) return 0;
    int v = pick_spare(1 - side[u], u, -1);
    if (v < 0) return 0;
    mv_nr = 0;
    mv_na = 1;
    mv_a[0][0] = u;
    mv_a[0][1] = v;
    return 1;
}

static void apply_move(void) {
    for (int i = 0; i < mv_nr; i++) del_edge(mv_r[i][0], mv_r[i][1]);
    for (int i = 0; i < mv_na; i++) add_edge(mv_a[i][0], mv_a[i][1]);
}

static void revert_move(void) {
    for (int i = 0; i < mv_na; i++) del_edge(mv_a[i][0], mv_a[i][1]);
    for (int i = 0; i < mv_nr; i++) add_edge(mv_r[i][0], mv_r[i][1]);
}

/* Simulated annealing on the bad-pair count at fixed order. Returns the final count. */
static int anneal(int B, double t_end, int maxIter) {
    const double T0 = 2.0, T1 = 0.1;
    for (int it = 0; it < maxIter && B > 0; it++) {
        if ((it & 31) == 0 && elapsed() >= t_end) break;
        if (!propose()) continue;
        apply_move();
        int nb = compute_bad();
        int delta = nb - B;
        double frac = (double)it / (double)maxIter;
        double temp = T0 * pow(T1 / T0, frac);
        if (delta <= 0 || urand() < exp(-(double)delta / temp)) {
            B = nb;
            memcpy(badv, badt, sizeof(int) * (size_t)N);
        } else {
            revert_move();
        }
    }
    return B;
}

static void print_snapshot(void) {
    printf("%d %d\n", snapN, snapM);
    for (int i = 0; i < snapM; i++) printf("%d %d\n", snapE[i][0], snapE[i][1]);
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
    if (n <= 0 || n > MAXN - 8 || Dist < 1 || Dd < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        deg[v] = 0;
        side[v] = -1;
    }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v || mat[u][v]) continue;
        if (deg[u] >= Dd || deg[v] >= Dd) continue;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
        mat[u][v] = mat[v][u] = 1;
    }
    /* 2-colour the graph; reject if it is not bipartite */
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
    for (int u = 0; u < N; u++)
        for (int k = 0; k < deg[u]; k++)
            if (side[adj[u][k]] == side[u]) {
                printf("0 0\n");
                return 0;
            }

    double t_end = elapsed() + budget;
    int have_best = 0;
    int B = compute_bad();
    memcpy(badv, badt, sizeof(int) * (size_t)N);
    if (B == 0) {
        take_snapshot();
        have_best = 1;
    }
    int streak = 0;
    const int maxIter = 5000;
    while (elapsed() < t_end && N < MAXN - 4) {
        if (have_best) {
            restore_snapshot();
            if (streak >= 400) break;
            grow();
        }
        B = compute_bad();
        memcpy(badv, badt, sizeof(int) * (size_t)N);
        B = anneal(B, t_end, maxIter);
        if (B == 0) {
            take_snapshot();
            have_best = 1;
            streak = 0;
        } else if (have_best) {
            restore_snapshot();
            streak++;
        }
    }
    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    print_snapshot();
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
    """Run the C repair-annealing engine from the start graph (n0, e0) and parse its output."""
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
        starts.extend(_arc_extensions(d, t0 + 0.20 * time_limit, rng))
    if D >= 4 and time.monotonic() < t0 + 0.20 * time_limit:
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

    # Repair-anneal the two largest starts; most of the time goes to the largest.
    plan = starts[:2]
    for idx, src in enumerate(plan):
        remaining = hard_end - time.monotonic()
        if remaining < 2.0:
            break
        share = remaining * 0.7 if (idx == 0 and len(plan) > 1) else remaining
        try:
            n1, e1 = _augment(src[0], src[1], d, D, seed * 31 + idx,
                              max(0.5, share - 1.0), share + 2.0)
        except Exception:
            continue
        if n1 > best[0] and lib.is_valid(n1, e1, d, D):
            best = (n1, e1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
