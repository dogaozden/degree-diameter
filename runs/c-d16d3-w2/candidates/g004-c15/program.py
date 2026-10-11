import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: grow-and-repair search on bipartite graphs with diameter <= D.
#
# State: a valid bipartite graph with max degree d. A growth step adds one
# vertex on a random side, joined to d opposite-side vertices (stealing edges
# when the opposite side is saturated). Simulated annealing over degree-
# preserving 2-switches, endpoint moves, additions and removals then minimises
# the number of vertex pairs at distance > D (bitset BFS, all pairs). On success
# the larger graph becomes the new base; otherwise the search restores the last
# valid graph and retries with a different random growth.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 800
#define MAXD 40
#define MAXW ((MAXN + 63) / 64)
#define MAXIT 3000

typedef uint64_t u64;

typedef struct {
    int n;
    int side[MAXN];
    int deg[MAXN];
    int nb[MAXN][MAXD];
} Graph;

static Graph G, BEST, SAVE;
static int have_best = 0;
static int dd = 0, DD = 0;
static u64 rs = 88172645463325252ULL;
static u64 bA[MAXN][MAXW], bB[MAXN][MAXW];
static double t_end = 0.0;
static int nlog = 0;
static struct { int t, u, v; } lg[16];

static u64 rng64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(rng64() % (u64)k); }

static double rnd01(void) { return (double)(rng64() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    int k;
    for (k = 0; k < G.deg[u]; k++)
        if (G.nb[u][k] == v) return 1;
    return 0;
}

static void add_e(int u, int v) {
    G.nb[u][G.deg[u]++] = v;
    G.nb[v][G.deg[v]++] = u;
}

static void rem1(int u, int v) {
    int k;
    for (k = 0; k < G.deg[u]; k++) {
        if (G.nb[u][k] == v) {
            G.nb[u][k] = G.nb[u][--G.deg[u]];
            return;
        }
    }
}

static void rem_e(int u, int v) {
    rem1(u, v);
    rem1(v, u);
}

static void L_add(int u, int v) {
    add_e(u, v);
    lg[nlog].t = 1; lg[nlog].u = u; lg[nlog].v = v;
    nlog++;
}

static void L_rem(int u, int v) {
    rem_e(u, v);
    lg[nlog].t = 0; lg[nlog].u = u; lg[nlog].v = v;
    nlog++;
}

static void undo(void) {
    while (nlog > 0) {
        nlog--;
        if (lg[nlog].t) rem_e(lg[nlog].u, lg[nlog].v);
        else add_e(lg[nlog].u, lg[nlog].v);
    }
}

/* Number of unordered vertex pairs at distance > DD (0 means valid). */
static int evalcost(void) {
    int n = G.n, W = (n + 63) >> 6, r, v, k, w;
    u64 (*cur)[MAXW] = bA, (*nxt)[MAXW] = bB, (*tmp)[MAXW];
    long total = 0;
    for (v = 0; v < n; v++) {
        for (w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (r = 0; r < DD; r++) {
        for (v = 0; v < n; v++) {
            for (w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (k = 0; k < G.deg[v]; k++) {
                int u = G.nb[v][k];
                for (w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        tmp = cur; cur = nxt; nxt = tmp;
    }
    for (v = 0; v < n; v++) {
        int c = 0;
        for (w = 0; w < W; w++) c += popc(cur[v][w]);
        total += n - c;
    }
    return (int)(total / 2);
}

static int rand_vertex_deg(int *out) {
    int t;
    for (t = 0; t < 200; t++) {
        int v = rnd(G.n);
        if (G.deg[v] > 0) { *out = v; return 1; }
    }
    return 0;
}

/* Random edge oriented so that *a is on side 0 and *b on side 1. */
static int random_edge(int *a, int *b) {
    int v, u, k;
    if (!rand_vertex_deg(&v)) return 0;
    k = rnd(G.deg[v]);
    u = G.nb[v][k];
    if (G.side[v] == 0) { *a = v; *b = u; }
    else { *a = u; *b = v; }
    return 1;
}

static int pick_spare(int s, int *out) {
    int t;
    for (t = 0; t < 60; t++) {
        int v = rnd(G.n);
        if (G.side[v] == s && G.deg[v] < dd) { *out = v; return 1; }
    }
    return 0;
}

/* Propose one move with logged changes. Returns 0 (with no change made) if none. */
static int propose(void) {
    int r = rnd(100), a = 0, b = 0, a2 = 0, b2 = 0, t;
    nlog = 0;
    if (r < 40) {
        if (!random_edge(&a, &b) || !random_edge(&a2, &b2)) return 0;
        if (a == a2 || b == b2 || has_edge(a, b2) || has_edge(a2, b)) return 0;
        L_rem(a, b); L_rem(a2, b2);
        L_add(a, b2); L_add(a2, b);
    } else if (r < 70) {
        if (!random_edge(&a, &b)) return 0;
        for (t = 0; t < 30; t++) {
            int c = rnd(G.n);
            if (G.side[c] == 1 && c != b && G.deg[c] < dd && !has_edge(a, c)) {
                L_rem(a, b);
                L_add(a, c);
                return 1;
            }
        }
        return 0;
    } else if (r < 92) {
        if (!pick_spare(0, &a) || !pick_spare(1, &b)) return 0;
        if (has_edge(a, b)) return 0;
        L_add(a, b);
    } else {
        if (!random_edge(&a, &b)) return 0;
        L_rem(a, b);
    }
    return 1;
}

/* Add one vertex on a random side, joined to d opposite-side vertices. */
static void grow(void) {
    int s = rnd(2), v = G.n, w, x, tries, guard;
    G.n++;
    G.side[v] = s;
    G.deg[v] = 0;
    for (tries = 0; tries < 2000 && G.deg[v] < dd; tries++) {
        w = rnd(v);
        if (G.side[w] == s || G.deg[w] >= dd || has_edge(v, w)) continue;
        add_e(v, w);
    }
    for (guard = 0; guard < 2000 && G.deg[v] < dd; guard++) {
        w = rnd(v);
        if (G.side[w] == s || G.deg[w] == 0 || has_edge(v, w)) continue;
        x = G.nb[w][rnd(G.deg[w])];
        rem_e(w, x);
        add_e(v, w);
    }
}

/* Simulated annealing at fixed n. Returns 1 iff the graph becomes valid. */
static int anneal(int maxit, double T0, double T1) {
    int c = evalcost(), it, c2, delta;
    if (c == 0) return 1;
    for (it = 0; it < maxit; it++) {
        double T;
        if ((it & 31) == 0 && now() > t_end) break;
        T = T0 * pow(T1 / T0, (double)it / maxit);
        if (!propose()) continue;
        c2 = evalcost();
        delta = c2 - c;
        if (delta <= 0 || rnd01() < exp(-delta / T)) {
            c = c2;
            if (c == 0) { nlog = 0; return 1; }
        } else {
            undo();
        }
        nlog = 0;
    }
    return c == 0;
}

static int load_input(void) {
    int n0 = 0, m0 = 0, i, u, v, col[MAXN], q[MAXN], h, t, k;
    if (scanf("%d %d", &n0, &m0) != 2) return 0;
    if (n0 <= 1 || n0 > MAXN - 2 || m0 < 0) return 0;
    memset(&G, 0, sizeof G);
    G.n = n0;
    for (i = 0; i < m0; i++) {
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) return 0;
        if (has_edge(u, v) || G.deg[u] >= dd || G.deg[v] >= dd) continue;
        add_e(u, v);
    }
    for (i = 0; i < n0; i++) col[i] = -1;
    for (i = 0; i < n0; i++) {
        if (col[i] >= 0) continue;
        col[i] = 0;
        h = 0; t = 0;
        q[t++] = i;
        while (h < t) {
            int x = q[h++];
            for (k = 0; k < G.deg[x]; k++) {
                int y = G.nb[x][k];
                if (col[y] < 0) {
                    col[y] = 1 - col[x];
                    q[t++] = y;
                } else if (col[y] == col[x]) {
                    return 0;
                }
            }
        }
    }
    for (i = 0; i < n0; i++) G.side[i] = col[i];
    return 1;
}

static void output_graph(const Graph *g) {
    int v, k, m = 0;
    for (v = 0; v < g->n; v++) m += g->deg[v];
    printf("%d %d\n", g->n, m / 2);
    for (v = 0; v < g->n; v++)
        for (k = 0; k < g->deg[v]; k++)
            if (g->nb[v][k] > v) printf("%d %d\n", v, g->nb[v][k]);
}

int main(int argc, char **argv) {
    int d = argc > 1 ? atoi(argv[1]) : 3;
    int D = argc > 2 ? atoi(argv[2]) : 3;
    unsigned seed = argc > 3 ? (unsigned)atoi(argv[3]) : 1u;
    double budget = argc > 4 ? atof(argv[4]) : 10.0;
    double repair_end;
    int fails = 0;

    if (d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    dd = d;
    DD = D;
    rs ^= (u64)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    t_end = now() + budget;

    if (!load_input()) {
        memset(&G, 0, sizeof G);
        G.n = 2;
        G.side[0] = 0;
        G.side[1] = 1;
        add_e(0, 1);
    }

    if (evalcost() == 0) {
        have_best = 1;
        BEST = G;
    } else {
        double saved_end = t_end;
        t_end = now() + 0.25 * budget;
        repair_end = t_end;
        if (anneal(200000, 1.0, 0.1)) {
            have_best = 1;
            BEST = G;
        }
        (void)repair_end;
        t_end = saved_end;
    }

    if (have_best) {
        while (now() < t_end && G.n < MAXN - 1 && fails < 100000) {
            SAVE = G;
            grow();
            if (anneal(MAXIT, 1.5, 0.15)) {
                BEST = G;
                have_best = 1;
                fails = 0;
            } else {
                G = SAVE;
                fails++;
            }
        }
    }

    if (have_best) output_graph(&BEST);
    else printf("0 0\n");
    return 0;
}
'''

_LS_ITERS = 8000


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Each old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
# A-side: a set SA of points, each gets a new vertex joined to its q+1 lines,
#         every line holding <= s points of SA.
# B-side: a set SB of lines, symmetric.
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


def _loads_ok(S, s, m, nbr):
    """True if every target t is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy for the load-constrained set problem."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _local_search(m, s, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the load-constrained set problem."""
    if s < 1:
        return list(S)
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= s:
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for q in qs:
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        SA = _local_search(m, s, point_lines, SA, rng, deadline, _LS_ITERS)
        SB = _local_search(m, s, line_points, SB, rng, deadline, _LS_ITERS)

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n_c, e_c))
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
# Build: best algebraic start, then the C grow-and-repair engine.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    if D >= 3:
        arc_deadline = start + 0.25 * time_limit
        cands = _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            if n_c > best_n:
                consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Grow-and-repair search in C, starting from the best valid graph found so far.
    if 1 <= d <= 40 and best_n < lib.moore_bound(d, D):
        remaining = start + 0.9 * time_limit - time.monotonic()
        if remaining > 4.0:
            cbudget = max(1.0, (remaining - 2.0) * 0.8)
            timeout = max(2.0, remaining - 1.0)
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{cbudget:.2f}"],
                                stdin_graph=best, timeout=timeout)
                n_c, e_c = lib.parse_graph_text(out)
                if n_c > best_n and lib.is_valid(n_c, e_c, d, D):
                    best = (n_c, e_c)
                    best_n = n_c
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
