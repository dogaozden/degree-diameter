"""Diameter-D bipartite search: arc-extended projective plane starts, then a C annealer.

Stage 1 builds valid starts: arc-extended PG(2,q) incidence graphs for D >= 3, the
generalized quadrangle W(q) for D >= 4, and K_{d,d} as a universal fallback.

Stage 2 is a different search from the earlier ball-based augmentation. The C engine
keeps the graph bipartite and degree-bounded, and grows it by two vertices at a time.
A new A-vertex x and B-vertex y take a matching (b_i, c_i) of size d: remove each edge
(c_i, b_i), add (x, b_i) and (y, c_i). Degrees are preserved and the order rises by 2.
Simulated annealing then repairs the diameter using degree-preserving 2-switches, with
the number of vertex pairs at distance > D as the cost. Every accepted state with cost 0
is a valid snapshot. If repair fails, the engine restores the last valid snapshot and
tries a different insertion. Python re-checks everything with lib.is_valid and keeps the
best valid graph, falling back to the start.
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

#define MAXN 1024
#define WMAX (MAXN / 64)
#define MAXDEG 64
#define MAXIT 30000
#define MAXFAIL 6

static int N, Dd, Dist;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static unsigned char am[MAXN][MAXN];
static int side[MAXN];
static uint64_t BA[MAXN][WMAX], BB[MAXN][WMAX];

static int sN;
static int sdeg[MAXN], sside[MAXN];
static int sadj[MAXN][MAXDEG];
static int have_valid = 0;

static int insA[MAXN], insB[MAXN];
static int ins_epoch = 0;

static int sw_a, sw_b, sw_c, sw_e;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
    am[a][b] = 1;
    am[b][a] = 1;
}

static void rem_from(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adj[a][k] == b) {
            adj[a][k] = adj[a][--deg[a]];
            return;
        }
    }
}

static void del_edge(int a, int b) {
    rem_from(a, b);
    rem_from(b, a);
    am[a][b] = 0;
    am[b][a] = 0;
}

/* Number of unordered pairs at distance > Dist (unreachable pairs included). */
static long cost(void) {
    int w = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < w; i++) BA[v][i] = 0;
        BA[v][v >> 6] |= 1ULL << (v & 63);
        for (int k = 0; k < deg[v]; k++) {
            int u = adj[v][k];
            BA[v][u >> 6] |= 1ULL << (u & 63);
        }
    }
    for (int r = 2; r <= Dist; r++) {
        for (int v = 0; v < N; v++) {
            for (int i = 0; i < w; i++) BB[v][i] = BA[v][i];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int i = 0; i < w; i++) BB[v][i] |= BA[u][i];
            }
        }
        for (int v = 0; v < N; v++)
            for (int i = 0; i < w; i++) BA[v][i] = BB[v][i];
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int i = 0; i < w; i++) c += popc(BA[v][i]);
        bad += N - c;
    }
    return bad / 2;
}

/* Add edges between spare A and B vertices. Adding edges never increases distances. */
static void fill_spare(void) {
    for (int a = 0; a < N; a++) {
        if (side[a] != 0) continue;
        for (int b = 0; b < N && deg[a] < Dd; b++) {
            if (side[b] != 1 || deg[b] >= Dd || am[a][b]) continue;
            add_edge(a, b);
        }
    }
}

static int pick_side(int s) {
    for (int t = 0; t < 4000; t++) {
        int v = rndint(N);
        if (side[v] == s && deg[v] > 0) return v;
    }
    return -1;
}

/* Degree-preserving 2-switch: (a,b),(c,e) -> (a,e),(c,b). */
static int do_switch(void) {
    int a = pick_side(0), c = pick_side(0);
    if (a < 0 || c < 0 || a == c) return 0;
    int b = adj[a][rndint(deg[a])];
    int e = adj[c][rndint(deg[c])];
    if (b == e || am[a][e] || am[c][b]) return 0;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    sw_a = a; sw_b = b; sw_c = c; sw_e = e;
    return 1;
}

static void undo_switch(void) {
    del_edge(sw_a, sw_e);
    del_edge(sw_c, sw_b);
    add_edge(sw_a, sw_b);
    add_edge(sw_c, sw_e);
}

/* Insert two vertices x (side 0) and y (side 1) using a matching of current edges. */
static int insert_pair(void) {
    if (N + 2 > MAXN) return 0;
    int cs[MAXDEG], bs[MAXDEG], m = 0;
    ins_epoch++;
    for (int t = 0; t < 40000 && m < Dd; t++) {
        int c = rndint(N);
        if (side[c] != 0 || deg[c] == 0) continue;
        int b = adj[c][rndint(deg[c])];
        if (insA[c] == ins_epoch || insB[b] == ins_epoch) continue;
        insA[c] = ins_epoch;
        insB[b] = ins_epoch;
        cs[m] = c;
        bs[m] = b;
        m++;
    }
    if (m == 0) return 0;
    int x = N, y = N + 1;
    N += 2;
    deg[x] = 0;
    deg[y] = 0;
    side[x] = 0;
    side[y] = 1;
    for (int i = 0; i < m; i++) {
        del_edge(cs[i], bs[i]);
        add_edge(x, bs[i]);
        add_edge(y, cs[i]);
    }
    return 1;
}

static void save_snapshot(void) {
    sN = N;
    for (int v = 0; v < N; v++) {
        sdeg[v] = deg[v];
        sside[v] = side[v];
        for (int k = 0; k < deg[v]; k++) sadj[v][k] = adj[v][k];
    }
}

static void restore_snapshot(void) {
    memset(am, 0, sizeof(am));
    N = sN;
    for (int v = 0; v < N; v++) {
        deg[v] = sdeg[v];
        side[v] = sside[v];
        for (int k = 0; k < deg[v]; k++) {
            adj[v][k] = sadj[v][k];
            am[v][adj[v][k]] = 1;
        }
    }
}

/* Anneal until cost 0 or the budget runs out. Returns 1 iff the current state is valid. */
static int anneal(double t_end, long maxit) {
    long cur = cost();
    if (cur == 0) return 1;
    const double T0 = 1.5, T1 = 0.05;
    for (long it = 0; it < maxit; it++) {
        if ((it & 63) == 0 && now() > t_end) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)maxit);
        if (!do_switch()) continue;
        long nc = cost();
        long dl = nc - cur;
        if (dl <= 0 || rnd01() < exp(-(double)dl / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            undo_switch();
        }
    }
    return cost() == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    if (Dd < 1) Dd = 1;
    if (Dd > MAXDEG) Dd = MAXDEG;
    Dist = atoi(argv[2]);
    if (Dist < 1) Dist = 1;
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 4242ULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 2) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (am[u][v] || deg[u] >= Dd || deg[v] >= Dd) continue;
        add_edge(u, v);
    }

    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        static int q[MAXN];
        int head = 0, t = 0;
        q[t++] = s;
        while (head < t) {
            int u = q[head++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    q[t++] = v;
                }
            }
        }
    }

    fill_spare();
    save_snapshot();
    have_valid = (cost() == 0);

    double t_end = now() + budget;
    int fails = 0;
    int level_ok = have_valid;

    while (now() < t_end) {
        if (!level_ok) {
            if (anneal(t_end, MAXIT)) {
                level_ok = 1;
            } else {
                if (!have_valid) continue;  /* keep repairing the current state */
                if (++fails > MAXFAIL) break;
                restore_snapshot();
                if (!insert_pair()) break;
                fill_spare();
                level_ok = (cost() == 0);
                continue;
            }
        }
        /* Current state is valid at this order. */
        save_snapshot();
        have_valid = 1;
        fails = 0;
        if (!insert_pair()) break;
        fill_spare();
        level_ok = (cost() == 0);
    }

    int M = 0;
    for (int v = 0; v < sN; v++)
        for (int k = 0; k < sdeg[v]; k++)
            if (sadj[v][k] > v) M++;
    printf("%d %d\n", sN, M);
    for (int v = 0; v < sN; v++)
        for (int k = 0; k < sdeg[v]; k++)
            if (sadj[v][k] > v) printf("%d %d\n", v, sadj[v][k]);
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

def _grow(n0, e0, d, D, seed, budget, timeout):
    """Run the C annealing grower from the start graph (n0, e0) and parse its output."""
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
    best = max(starts, key=lambda g: g[0])

    # Already at the Moore bound: nothing more to gain.
    if best[0] >= lib.moore_bound(d, D):
        return best

    # Grow the top starts with the annealing engine, splitting the remaining time.
    plan = starts[:2]
    for idx, src in enumerate(plan):
        remaining = hard_end - time.monotonic()
        if remaining < 3.0:
            break
        share = remaining / (len(plan) - idx)
        budget = max(0.3, share - 2.0)
        timeout = budget + 2.0 + 0.02 * time_limit
        try:
            n1, e1 = _grow(src[0], src[1], d, D, seed * 31 + idx, budget, timeout)
        except Exception:
            continue
        if n1 > best[0] and lib.is_valid(n1, e1, d, D):
            best = (n1, e1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
