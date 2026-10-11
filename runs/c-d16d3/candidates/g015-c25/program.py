"""Diameter-D bipartite search: arc-extended projective plane starts, then a C
simulated-annealing repair engine that grows the graph one vertex at a time.

Each start is a valid graph (arc-extended PG(2,q) incidence, the generalized quadrangle
for D >= 4, or K_{d,d}). The C engine keeps a valid graph (cost 0 = no pair at distance
more than D). To grow it, it adds one vertex on a random side, joined greedily to
other-side vertices that cover the most vertices within distance D-1. If the cost is
not yet zero, it runs simulated annealing over degree-preserving 2-switches, endpoint
moves and edge additions to drive the number of bad pairs to zero. A failed round is
discarded and the engine restarts from the last valid graph. Python re-checks everything
with lib.is_valid and falls back to a safe graph if anything is wrong.
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
#include <math.h>

#define MAXN 1024
#define WMAX (MAXN / 64)
#define MAXDEG 64
#define STEPS 15000

typedef uint64_t Row[WMAX];

static int Dd, Dist, N, W;
static int deg[MAXN], adj[MAXN][MAXDEG], side[MAXN];
static Row bufA[MAXN], bufB[MAXN];
static Row ballA[MAXN], ballB[MAXN];
static char usedc[MAXN];
static int bN = 0, have_best = 0;
static int bdeg[MAXN], badj[MAXN][MAXDEG], bside[MAXN];
static uint64_t rs = 88172645463325252ULL;
static double t_end;

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

/* Bitsets of the ball of radius r around every vertex. Result is cur (p or q). */
static Row *balls(int r, Row *p, Row *q) {
    Row *cur = p, *nxt = q;
    int v, k, w, it;
    for (v = 0; v < N; v++) {
        for (w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (it = 0; it < r; it++) {
        for (v = 0; v < N; v++) {
            for (w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        Row *t = cur;
        cur = nxt;
        nxt = t;
    }
    return cur;
}

/* Number of unordered pairs at distance greater than Dist. */
static long cost_eval(void) {
    Row *B = balls(Dist, bufA, bufB);
    long miss = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(B[v][w]);
        miss += N - c;
    }
    return miss / 2;
}

static int has_edge(int u, int v) {
    for (int k = 0; k < deg[u]; k++)
        if (adj[u][k] == v) return 1;
    return 0;
}

static void del_one(int u, int v) {
    for (int k = 0; k < deg[u]; k++)
        if (adj[u][k] == v) {
            adj[u][k] = adj[u][--deg[u]];
            return;
        }
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void rem_edge(int u, int v) {
    del_one(u, v);
    del_one(v, u);
}

typedef struct {
    int type, a, b, c, e;
} Move;

/* type 0: (a,b),(c,e) -> (a,e),(c,b)   [side(a)=side(c)]
   type 1: add (a,b)
   type 2: (a,b) -> (c,b)               [side(a)=side(c)] */
static void apply_move(const Move *m) {
    switch (m->type) {
    case 0:
        rem_edge(m->a, m->b);
        rem_edge(m->c, m->e);
        add_edge(m->a, m->e);
        add_edge(m->c, m->b);
        break;
    case 1:
        add_edge(m->a, m->b);
        break;
    default:
        rem_edge(m->a, m->b);
        add_edge(m->c, m->b);
        break;
    }
}

static void undo_move(const Move *m) {
    switch (m->type) {
    case 0:
        rem_edge(m->a, m->e);
        rem_edge(m->c, m->b);
        add_edge(m->a, m->b);
        add_edge(m->c, m->e);
        break;
    case 1:
        rem_edge(m->a, m->b);
        break;
    default:
        rem_edge(m->c, m->b);
        add_edge(m->a, m->b);
        break;
    }
}

static int random_move(Move *m) {
    int r = rndint(100);
    if (r < 50) {
        int a = rndint(N);
        if (!deg[a]) return 0;
        int b = adj[a][rndint(deg[a])];
        int c = rndint(N);
        if (c == a || side[c] != side[a] || !deg[c]) return 0;
        int e = adj[c][rndint(deg[c])];
        if (e == b) return 0;
        if (has_edge(a, e) || has_edge(c, b)) return 0;
        m->type = 0;
        m->a = a;
        m->b = b;
        m->c = c;
        m->e = e;
        return 1;
    } else if (r < 85) {
        int a = rndint(N);
        if (!deg[a]) return 0;
        int b = adj[a][rndint(deg[a])];
        int c = rndint(N);
        if (c == a || side[c] != side[a] || deg[c] >= Dd) return 0;
        if (has_edge(c, b)) return 0;
        m->type = 2;
        m->a = a;
        m->b = b;
        m->c = c;
        m->e = -1;
        return 1;
    } else {
        int a = rndint(N), b = rndint(N);
        if (side[a] == side[b] || deg[a] >= Dd || deg[b] >= Dd || has_edge(a, b)) return 0;
        m->type = 1;
        m->a = a;
        m->b = b;
        m->c = -1;
        m->e = -1;
        return 1;
    }
}

/* Simulated annealing at the current size. Returns 1 as soon as the cost reaches 0. */
static int anneal(long steps) {
    long cur = cost_eval();
    if (cur == 0) return 1;
    double T0 = 1.5, T1 = 0.08;
    double lr = log(T1 / T0);
    for (long s = 0; s < steps; s++) {
        if ((s & 511) == 0 && elapsed() > t_end) break;
        double T = T0 * exp(lr * (double)s / (double)steps);
        Move m;
        if (!random_move(&m)) continue;
        apply_move(&m);
        long nc = cost_eval();
        long delta = nc - cur;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            undo_move(&m);
        }
    }
    return 0;
}

static void save_best(void) {
    bN = N;
    have_best = 1;
    for (int v = 0; v < N; v++) {
        bdeg[v] = deg[v];
        bside[v] = side[v];
        memcpy(badj[v], adj[v], sizeof(int) * (size_t)deg[v]);
    }
}

static void restore_best(void) {
    N = bN;
    W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        deg[v] = bdeg[v];
        side[v] = bside[v];
        memcpy(adj[v], badj[v], sizeof(int) * (size_t)deg[v]);
    }
}

/* Add one vertex on a random side, joined greedily to other-side vertices that cover
   the most vertices within distance Dist-1 (so the new vertex is within Dist of all). */
static int grow(void) {
    if (N + 2 >= MAXN) return 0;
    int X = rndint(2);
    static int cand[MAXN];
    int nc = 0;
    for (int v = 0; v < N; v++)
        if (side[v] != X && deg[v] < Dd) cand[nc++] = v;
    if (nc == 0) return 0;

    Row *B = balls(Dist - 1 < 0 ? 0 : Dist - 1, ballA, ballB);
    Row U;
    for (int w = 0; w < W; w++) U[w] = ~0ULL;
    if (N & 63) U[W - 1] = (1ULL << (N & 63)) - 1ULL;

    int chosen[MAXDEG];
    int nch = 0;
    while (nch < Dd) {
        int best = -1;
        long bestsc = -1;
        for (int i = 0; i < nc; i++) {
            int c = cand[i];
            if (usedc[c]) continue;
            long g = 0;
            for (int w = 0; w < W; w++) g += popc(B[c][w] & U[w]);
            if (g <= 0) continue;
            long sc = g * 8 + rndint(8);
            if (sc > bestsc) {
                bestsc = sc;
                best = c;
            }
        }
        if (best < 0) break;
        usedc[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) U[w] &= ~B[best][w];
    }
    for (int i = 0; i < nch; i++) usedc[chosen[i]] = 0;
    if (nch == 0) return 0;

    int x = N;
    N++;
    W = (N + 63) / 64;
    side[x] = X;
    deg[x] = 0;
    for (int i = 0; i < nch; i++) add_edge(x, chosen[i]);
    return 1;
}

static void print_current(void) {
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
    Dist = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 64 || Dist < 1 || Dd < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    W = (N + 63) / 64;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= Dd || deg[v] >= Dd) continue;
        if (has_edge(u, v)) continue;
        add_edge(u, v);
    }

    /* 2-colour the graph by BFS. */
    static int q[MAXN];
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
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

    t_end = elapsed() + budget;
    if (cost_eval() == 0) save_best();

    int stall = 0;
    while (elapsed() < t_end) {
        if (have_best) {
            restore_best();
            if (!grow()) {
                if (++stall > 1000) break;
                continue;
            }
        }
        if (anneal(STEPS)) {
            save_best();
            stall = 0;
        }
    }

    if (have_best) restore_best();
    print_current();
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

def _sa(start, d, D, seed, budget):
    """Run the C annealing engine from a valid start graph and parse its output."""
    n0, e0 = start
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=budget + 3.0)
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
    start_deadline = t0 + 0.15 * time_limit
    if D >= 3:
        starts.extend(_arc_extensions(d, start_deadline, rng))
    if D >= 4 and time.monotonic() < start_deadline:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    starts = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    if lib.is_valid(fallback[0], fallback[1], d, D):
        starts.append(fallback)
    if not starts:
        return 1, []
    best = max(starts, key=lambda g: g[0])

    # The Moore bound is a hard ceiling: nothing larger is possible.
    if best[0] >= lib.moore_bound(d, D):
        return best

    # Annealing repair engine grows the best start one vertex at a time.
    remaining = hard_end - time.monotonic() - 2.0
    if remaining > 2.0:
        try:
            n1, e1 = _sa(best, d, D, seed, remaining)
            if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                best = (n1, e1)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
