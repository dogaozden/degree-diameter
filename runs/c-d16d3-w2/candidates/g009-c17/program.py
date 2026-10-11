import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C local search that adds one vertex at a time to a valid graph (diameter D).
#
# State: a valid graph G plus one new vertex X on a chosen side. The cost is the
# number of vertex pairs at distance > D, computed with bitset ball expansion.
# Moves toggle X's neighbours (dropping a neighbour when a degree is full) or
# rewire an existing edge to another vertex on the same side. Simulated
# annealing drives the cost to zero; on success X is kept and the next vertex
# is attempted. The output is always the last valid graph reached.
# ----------------------------------------------------------------------------

C_REPAIR_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXD 32
#define MAXW 16
#define ITERS 4000
#define T0 2.0
#define TEND 0.05
#define GIVEUP 60

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int side[MAXN];
} Graph;

static Graph G, W;
static int dd, DD;
static uint64_t rs;
static uint64_t R1[MAXN][MAXW], R2[MAXN][MAXW];
static int sl[2][MAXN], cnt[2];

typedef struct { int type, a, b; } Op;
static Op lg[256];
static int nlg;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int has_edge(const Graph *g, int a, int b) {
    for (int i = 0; i < g->deg[a]; i++) if (g->adj[a][i] == b) return 1;
    return 0;
}
static void add_e(Graph *g, int a, int b) {
    g->adj[a][g->deg[a]++] = b;
    g->adj[b][g->deg[b]++] = a;
}
static void del_from(Graph *g, int a, int b) {
    for (int i = 0; i < g->deg[a]; i++) {
        if (g->adj[a][i] == b) {
            g->adj[a][i] = g->adj[a][--g->deg[a]];
            return;
        }
    }
}
static void del_e(Graph *g, int a, int b) {
    del_from(g, a, b);
    del_from(g, b, a);
}

static long cost(const Graph *g) {
    int N = g->n, Wd = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        memset(R1[v], 0, sizeof(uint64_t) * Wd);
        R1[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < DD; it++) {
        for (int v = 0; v < N; v++) {
            memcpy(R2[v], R1[v], sizeof(uint64_t) * Wd);
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *src = R1[g->adj[v][i]];
                for (int k = 0; k < Wd; k++) R2[v][k] |= src[k];
            }
        }
        for (int v = 0; v < N; v++)
            memcpy(R1[v], R2[v], sizeof(uint64_t) * Wd);
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int k = 0; k < Wd; k++) c += pc64(R1[v][k]);
        bad += N - c;
    }
    return bad / 2;
}

static void L_add(Graph *g, int a, int b) {
    add_e(g, a, b);
    lg[nlg].type = 0; lg[nlg].a = a; lg[nlg].b = b; nlg++;
}
static void L_del(Graph *g, int a, int b) {
    del_e(g, a, b);
    lg[nlg].type = 1; lg[nlg].a = a; lg[nlg].b = b; nlg++;
}
static void undo(Graph *g) {
    while (nlg > 0) {
        nlg--;
        if (lg[nlg].type == 0) del_e(g, lg[nlg].a, lg[nlg].b);
        else add_e(g, lg[nlg].a, lg[nlg].b);
    }
}

static void do_move(int X) {
    int sx = W.side[X], os = 1 - sx;
    nlg = 0;
    if (rnd01() < 0.5) {
        if (cnt[os] == 0) return;
        int t = sl[os][rndint(cnt[os])];
        if (has_edge(&W, X, t)) {
            L_del(&W, X, t);
        } else {
            if (W.deg[X] >= dd) {
                int u = W.adj[X][rndint(W.deg[X])];
                L_del(&W, X, u);
            }
            if (W.deg[t] >= dd) {
                int u = W.adj[t][rndint(W.deg[t])];
                L_del(&W, t, u);
            }
            L_add(&W, X, t);
        }
    } else {
        int a = rndint(X);
        if (W.deg[a] == 0) return;
        int b = W.adj[a][rndint(W.deg[a])];
        int s2 = W.side[b];
        if (cnt[s2] == 0) return;
        int c = sl[s2][rndint(cnt[s2])];
        if (c == b || c == a || W.deg[c] >= dd || has_edge(&W, a, c)) return;
        L_del(&W, a, b);
        L_add(&W, a, c);
    }
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int v = 0; v < g->n; v++)
        for (int i = 0; i < g->deg[v]; i++)
            if (g->adj[v][i] > v) m++;
    printf("%d %ld\n", g->n, m);
    for (int v = 0; v < g->n; v++)
        for (int i = 0; i < g->deg[v]; i++)
            if (g->adj[v][i] > v) printf("%d %d\n", v, g->adj[v][i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 2654435761ULL + 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = strtod(argv[4], NULL);
    double t0 = now_s();

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || n0 > MAXN - 2 ||
        dd < 1 || dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    memset(&G, 0, sizeof G);
    G.n = n0;
    for (int i = 0; i < m0; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a < 0 || b < 0 || a >= n0 || b >= n0 || a == b) continue;
        if (G.deg[a] >= dd || G.deg[b] >= dd || has_edge(&G, a, b)) continue;
        add_e(&G, a, b);
    }

    int col[MAXN], stk[MAXN], ok = 1;
    for (int i = 0; i < n0; i++) col[i] = -1;
    for (int s = 0; s < n0; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int i = 0; i < G.deg[u]; i++) {
                int v = G.adj[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    stk[sp++] = v;
                } else if (col[v] == col[u]) {
                    ok = 0;
                }
            }
        }
    }
    if (!ok) {
        print_graph(&G);
        return 0;
    }
    for (int i = 0; i < n0; i++) G.side[i] = col[i];
    if (cost(&G) != 0) {
        print_graph(&G);
        return 0;
    }

    long fails = 0;
    while (now_s() - t0 < budget && fails < GIVEUP) {
        W = G;
        int X = W.n;
        W.n = X + 1;
        W.deg[X] = 0;
        W.side[X] = rndint(2);
        int sx = W.side[X], os = 1 - sx;
        cnt[0] = cnt[1] = 0;
        for (int v = 0; v < X; v++) {
            int s = W.side[v];
            sl[s][cnt[s]++] = v;
        }
        if (cnt[os] == 0) {
            fails++;
            continue;
        }
        for (int i = cnt[os] - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = sl[os][i];
            sl[os][i] = sl[os][j];
            sl[os][j] = tmp;
        }
        for (int i = 0; i < cnt[os] && W.deg[X] < dd; i++) {
            int t = sl[os][i];
            if (W.deg[t] < dd) add_e(&W, X, t);
        }
        long cur = cost(&W);
        for (int it = 0; it < ITERS && cur > 0; it++) {
            double T = T0 * pow(TEND / T0, (double)it / ITERS);
            do_move(X);
            if (nlg == 0) continue;
            long c2 = cost(&W);
            long delta = c2 - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cur = c2;
            } else {
                undo(&W);
            }
            nlg = 0;
        }
        if (cur == 0) {
            G = W;
            fails = 0;
        } else {
            fails++;
        }
    }
    print_graph(&G);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare capacity
# s = d - q - 1. Choose a point set S such that every line contains at most s
# points of S and every point lies on at most s lines indexed by S. For each
# P in S add a new A-vertex joined to all q+1 lines through P; for each j in S
# add a new B-vertex joined to all q+1 points on line j. Diameter stays 3.
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


def _arc_graph(m, edges, point_lines, S, line_points):
    """Build the extended graph: old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):  # S is also a set of line indices (same vectors)
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
        n_c, e_c = _arc_graph(m, edges, point_lines, S, line_points)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Spare-capacity fill (diameter 3).
#
# A new vertex x is valid if its neighbourhood T covers the whole opposite-
# from-x side (every vertex of x's side has a neighbour in T). Candidates are
# chosen greedily and each addition is checked with lib.is_valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """2-colouring of a bipartite graph given by adjacency lists."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _fill(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover the opposite side; return (n, edges)."""
    edges = list(edges)
    fails = 0
    while time.monotonic() < deadline and fails < 400:
        adj = [[] for _ in range(n)]
        for u, v in edges:
            adj[u].append(v)
            adj[v].append(u)
        deg = [len(a) for a in adj]
        col = _bipartition(n, adj)
        c = rng.randrange(2)
        uncovered = {v for v in range(n) if col[v] == 1 - c}
        cand = [v for v in range(n) if col[v] == c and deg[v] < d]
        chosen = []
        chosen_set = set()
        while uncovered and len(chosen) < d:
            best_v = None
            best_key = None
            for v in cand:
                if v in chosen_set:
                    continue
                g = 0
                for u in adj[v]:
                    if u in uncovered:
                        g += 1
                if g == 0:
                    continue
                key = (g, rng.random())
                if best_key is None or key > best_key:
                    best_key = key
                    best_v = v
            if best_v is None:
                break
            chosen.append(best_v)
            chosen_set.add(best_v)
            for u in adj[best_v]:
                uncovered.discard(u)
        if uncovered:
            fails += 1
            continue
        new_edges = edges + [(v, n) for v in chosen]
        if lib.is_valid(n + 1, new_edges, d, D):
            edges = new_edges
            n += 1
            fails = 0
        else:
            fails += 1
    return n, edges


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
# Simulated annealing over bi-Cayley voltage lifts (used for D != 3).
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
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

    # Arc-extended projective plane graphs. Diameter 3, so valid for all D >= 3.
    if D >= 3:
        cands = _arc_extensions(d, start + 0.2 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    # Greedy fill of spare degree with extra cover-type vertices (diameter 3).
    if D >= 3 and best_n > 2:
        n_f, e_f = _fill(best_n, best[1], d, D, start + 0.3 * time_limit,
                         random.Random(seed * 104729 + d))
        consider(n_f, e_f)

    # Repair search in C: grow the best valid graph one vertex at a time.
    # Every result is re-validated by lib.is_valid; any failure keeps the fallback.
    if D == 3 and best_n > 2:
        remaining = time_limit * 0.9 - (time.monotonic() - start)
        if remaining > 2.0:
            try:
                out = lib.run_c(C_REPAIR_SOURCE, [d, D, seed, round(0.8 * remaining, 2)],
                                stdin_graph=best, timeout=remaining)
                n_r, e_r = lib.parse_graph_text(out)
                consider(n_r, e_r)
            except Exception:
                pass

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed group voltage lifts for D != 3 (larger bases for D >= 5).
    if D != 3:
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
