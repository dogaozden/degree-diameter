import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: annealed vertex insertion with a bad-pair cost.
#
# The graph is kept bipartite (every edge joins side 0 to side 1) and degree
# <= d. The cost is the number of unordered vertex pairs at distance > D,
# computed exactly with bitset balls. The search grows the graph one vertex at
# a time: add an isolated vertex on a random side, then anneal with three
# degree-respecting moves (add a spare cross edge, switch two edges, move one
# endpoint to a spare vertex) until the cost is 0. A success becomes the new
# snapshot. A failure restores the snapshot, shakes it with random moves and
# tries again.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define CAP 2048
#define WMAX (CAP / 64)
#define EMAX (CAP * 64)
#define MV_NONE 0
#define MV_ADD 1
#define MV_SWAP 2
#define MV_SHIFT 3
#define ITERS 15000
#define T_HI 1.0
#define T_LO 0.08
#define SHAKE_MIN 40

typedef struct { int type, i, j, a, b, c, dd, x; } Move;

static unsigned char adjm[CAP][CAP];
static int side_[CAP];
static int deg_[CAP];
static int n, m, D, dmax;
static int eu[EMAX], ev[EMAX];
static uint64_t RA[CAP][WMAX], RB[CAP][WMAX];
static int bn, bm, bside[CAP], bu[EMAX], bv[EMAX];
static int best_valid = 0;
static uint64_t rs = 88172645463325252ULL;
static double t_budget = 10.0;
static double t_zero = 0.0;

static double wall(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static double elapsed(void) { return wall() - t_zero; }

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > D. Zero means valid. */
static long long cost_eval(void) {
    int W = (n + 63) >> 6;
    uint64_t (*cur)[WMAX] = RA;
    uint64_t (*nxt)[WMAX] = RB;
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * W);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < n; v++) memcpy(nxt[v], cur[v], sizeof(uint64_t) * W);
        for (int e = 0; e < m; e++) {
            int a = eu[e], b = ev[e];
            uint64_t *na = nxt[a], *nb = nxt[b];
            const uint64_t *ca = cur[a], *cb = cur[b];
            for (int w = 0; w < W; w++) {
                na[w] |= cb[w];
                nb[w] |= ca[w];
            }
        }
        uint64_t (*tmp)[WMAX] = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long s = 0;
    for (int v = 0; v < n; v++)
        for (int w = 0; w < W; w++) s += pc64(cur[v][w]);
    return ((long long)n * n - s) / 2;
}

static void add_edge_raw(int a, int b) {
    eu[m] = a;
    ev[m] = b;
    m++;
    adjm[a][b] = adjm[b][a] = 1;
    deg_[a]++;
    deg_[b]++;
}

static void add_vertex(int s) {
    side_[n] = s;
    deg_[n] = 0;
    n++;
}

static void clear_state(void) {
    for (int e = 0; e < m; e++) adjm[eu[e]][ev[e]] = adjm[ev[e]][eu[e]] = 0;
    for (int v = 0; v < n; v++) deg_[v] = 0;
    n = 0;
    m = 0;
}

static int load_input(void) {
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) return 0;
    if (n0 < 2 || n0 > CAP - 2 || m0 < 0 || m0 > EMAX - 1) return 0;
    n = n0;
    for (int i = 0; i < m0; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) return 0;
        if (a < 0 || b < 0 || a >= n || b >= n || a == b || adjm[a][b]) return 0;
        add_edge_raw(a, b);
    }
    return 1;
}

static int color_graph(void) {
    static int stk[CAP];
    for (int v = 0; v < n; v++) side_[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side_[s] != -1) continue;
        side_[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int v = 0; v < n; v++) {
                if (!adjm[u][v]) continue;
                if (side_[v] == -1) {
                    side_[v] = 1 - side_[u];
                    stk[sp++] = v;
                } else if (side_[v] == side_[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void orient_edges(void) {
    for (int e = 0; e < m; e++) {
        if (side_[eu[e]] == 1) {
            int t = eu[e];
            eu[e] = ev[e];
            ev[e] = t;
        }
    }
}

static void save_best(void) {
    bn = n;
    bm = m;
    for (int v = 0; v < n; v++) bside[v] = side_[v];
    for (int e = 0; e < m; e++) {
        bu[e] = eu[e];
        bv[e] = ev[e];
    }
}

static void restore_best(void) {
    for (int e = 0; e < m; e++) adjm[eu[e]][ev[e]] = adjm[ev[e]][eu[e]] = 0;
    for (int v = 0; v < n; v++) deg_[v] = 0;
    n = bn;
    m = bm;
    for (int v = 0; v < n; v++) side_[v] = bside[v];
    for (int e = 0; e < m; e++) {
        eu[e] = bu[e];
        ev[e] = bv[e];
        adjm[eu[e]][ev[e]] = adjm[ev[e]][eu[e]] = 1;
        deg_[eu[e]]++;
        deg_[ev[e]]++;
    }
}

/* Random vertex on side s; if need_spare, its degree must be below dmax. */
static int pick_side(int s, int need_spare) {
    for (int t = 0; t < 80; t++) {
        int v = rndint(n);
        if (side_[v] != s) continue;
        if (need_spare && deg_[v] >= dmax) continue;
        return v;
    }
    return -1;
}

static int mv_add(Move *mv) {
    if (m >= EMAX - 1) return 0;
    int u = pick_side(0, 1), v = pick_side(1, 1);
    if (u < 0 || v < 0 || adjm[u][v]) return 0;
    eu[m] = u;
    ev[m] = v;
    m++;
    adjm[u][v] = adjm[v][u] = 1;
    deg_[u]++;
    deg_[v]++;
    mv->type = MV_ADD;
    mv->a = u;
    mv->b = v;
    return 1;
}

/* Degree-preserving switch: (a,b),(c,dd) -> (a,dd),(c,b). */
static int mv_swap(Move *mv) {
    if (m < 2) return 0;
    int i = rndint(m), j = rndint(m);
    if (i == j) return 0;
    int a = eu[i], b = ev[i], c = eu[j], dd = ev[j];
    if (a == c || b == dd || adjm[a][dd] || adjm[c][b]) return 0;
    adjm[a][b] = adjm[b][a] = 0;
    adjm[c][dd] = adjm[dd][c] = 0;
    adjm[a][dd] = adjm[dd][a] = 1;
    adjm[c][b] = adjm[b][c] = 1;
    eu[i] = a;
    ev[i] = dd;
    eu[j] = c;
    ev[j] = b;
    mv->type = MV_SWAP;
    mv->i = i;
    mv->j = j;
    mv->a = a;
    mv->b = b;
    mv->c = c;
    mv->dd = dd;
    return 1;
}

/* Move endpoint b of edge (a,b) to a spare vertex x on b's side. */
static int mv_shift(Move *mv) {
    if (m < 1) return 0;
    int i = rndint(m);
    int a = eu[i], b = ev[i];
    int x = pick_side(side_[b], 1);
    if (x < 0 || x == b || adjm[a][x]) return 0;
    adjm[a][b] = adjm[b][a] = 0;
    adjm[a][x] = adjm[x][a] = 1;
    deg_[b]--;
    deg_[x]++;
    ev[i] = x;
    mv->type = MV_SHIFT;
    mv->i = i;
    mv->a = a;
    mv->b = b;
    mv->x = x;
    return 1;
}

static int propose(Move *mv) {
    mv->type = MV_NONE;
    double r = rnd01();
    if (r < 0.25) return mv_add(mv);
    if (r < 0.65) return mv_swap(mv);
    return mv_shift(mv);
}

static void undo_move(const Move *mv) {
    switch (mv->type) {
    case MV_ADD: {
        int u = mv->a, v = mv->b;
        m--;
        adjm[u][v] = adjm[v][u] = 0;
        deg_[u]--;
        deg_[v]--;
        break;
    }
    case MV_SWAP: {
        int i = mv->i, j = mv->j, a = mv->a, b = mv->b, c = mv->c, dd = mv->dd;
        adjm[a][dd] = adjm[dd][a] = 0;
        adjm[c][b] = adjm[b][c] = 0;
        adjm[a][b] = adjm[b][a] = 1;
        adjm[c][dd] = adjm[dd][c] = 1;
        eu[i] = a;
        ev[i] = b;
        eu[j] = c;
        ev[j] = dd;
        break;
    }
    case MV_SHIFT: {
        int i = mv->i, a = mv->a, b = mv->b, x = mv->x;
        adjm[a][x] = adjm[x][a] = 0;
        adjm[a][b] = adjm[b][a] = 1;
        deg_[x]--;
        deg_[b]++;
        ev[i] = b;
        break;
    }
    default:
        break;
    }
}

static void shake(int K) {
    Move mv;
    for (int k = 0; k < K; k++) (void)propose(&mv);
}

/* Metropolis annealing on the bad-pair cost; stops early at cost 0. */
static long long anneal(long long iters, double T0, double T1) {
    long long cur = cost_eval();
    for (long long it = 0; it < iters && cur > 0; it++) {
        if ((it & 127) == 0 && elapsed() > t_budget) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        Move mv;
        if (!propose(&mv)) continue;
        long long nc = cost_eval();
        long long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            undo_move(&mv);
        }
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed budget\n");
        return 1;
    }
    dmax = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    t_budget = atof(argv[4]);
    t_zero = wall();
    if (dmax < 1) dmax = 1;
    if (D < 1) D = 1;

    int ok = load_input();
    if (ok) {
        for (int v = 0; v < n; v++)
            if (deg_[v] > dmax) ok = 0;
        if (ok) ok = color_graph();
        if (ok) orient_edges();
    }
    if (!ok) {
        clear_state();
        add_vertex(0);
        add_vertex(1);
        add_edge_raw(0, 1);
    }

    save_best();
    best_valid = 0;
    if (cost_eval() == 0) {
        best_valid = 1;
    } else if (anneal((long long)ITERS * 6, T_HI, T_LO) == 0) {
        best_valid = 1;
        save_best();
    }

    int fails = 0;
    while (best_valid && elapsed() < t_budget && bn + 2 < CAP) {
        restore_best();
        add_vertex(rndint(2));
        if (fails > 0) shake(SHAKE_MIN + rndint(60));
        long long c2 = anneal(ITERS, T_HI, T_LO);
        if (c2 == 0) {
            save_best();
            fails = 0;
        } else {
            fails++;
        }
    }

    printf("%d %d\n", bn, bm);
    for (int e = 0; e < bm; e++) printf("%d %d\n", bu[e], bv[e]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python construction: arc-extended projective plane graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has spare
# capacity s = d - q - 1. Choose a point set S whose line and point loads are
# at most s; add a new A-vertex on each point of S and a new B-vertex on each
# line of S. The C engine then grows the best result.
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
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
# Build: best construction, then the C annealed-growth engine from it.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.90 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3 and time.monotonic() < deadline:
        arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing to search for.
    if best_n >= lib.moore_bound(d, D):
        return best

    remaining = deadline - time.monotonic()
    if D >= 2 and remaining > 3.0:
        budget = remaining - 1.5  # leave room for C compilation and output
        try:
            txt = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=budget + 25.0)
            consider(*lib.parse_graph_text(txt))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
