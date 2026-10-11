import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: grow-and-repair search on bipartite graphs.
#
# Starting from a valid graph, the engine repeatedly adds one vertex (joined to
# up to d opposite-side vertices, evicting an edge where a neighbour is full),
# then runs simulated annealing on the number of vertex pairs at distance > D.
# Moves are degree-preserving 2-switches, edge additions, endpoint rewires and
# edge deletions, all keeping sides fixed, so the graph stays bipartite with
# max degree d. Whenever the cost reaches 0 the graph is saved. If annealing
# fails within a step budget, the engine restores the last valid graph and
# tries a different growth. Output is the largest valid graph seen.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXDEG 64

static int d, D;
static int N, CAP, W;
static int side[MAXN];
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static uint64_t *bufA, *bufB;

static int best_ok = 0;
static int bestN = 0;
static int bestDeg[MAXN];
static int bestSide[MAXN];
static int bestAdj[MAXN][MAXDEG];

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adj[a][i] == b) return 1;
    return 0;
}
static void add_arc(int a, int b) { adj[a][deg[a]++] = b; }
static void del_arc(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adj[a][i] == b) {
            adj[a][i] = adj[a][--deg[a]];
            return;
        }
}

typedef struct { int t, a, b; } Op;
static Op oplog[16];
static int nop = 0;

static void do_add(int a, int b) {
    add_arc(a, b);
    add_arc(b, a);
    oplog[nop].t = 1; oplog[nop].a = a; oplog[nop].b = b; nop++;
}
static void do_del(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
    oplog[nop].t = 0; oplog[nop].a = a; oplog[nop].b = b; nop++;
}
static void undo_all(void) {
    while (nop > 0) {
        nop--;
        Op o = oplog[nop];
        if (o.t) { del_arc(o.a, o.b); del_arc(o.b, o.a); }
        else { add_arc(o.a, o.b); add_arc(o.b, o.a); }
    }
}

/* Number of unordered pairs at distance > D (unreachable counts). */
static long long bad_pairs(void) {
    uint64_t *cur = bufA, *nxt = bufB;
    size_t tot = (size_t)N * W;
    memset(cur, 0, tot * sizeof(uint64_t));
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            memcpy(o, c, (size_t)W * sizeof(uint64_t));
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *u = cur + (size_t)adj[v][i] * W;
                for (int w = 0; w < W; w++) o[w] |= u[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int cnt = 0;
        const uint64_t *c = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) cnt += popc64(c[w]);
        bad += N - cnt;
    }
    return bad / 2;
}

static int rand_edge(int *ea, int *eb) {
    for (int t = 0; t < 1000; t++) {
        int x = rndint(N);
        if (deg[x] == 0) continue;
        int y = adj[x][rndint(deg[x])];
        if (side[x] == 0) { *ea = x; *eb = y; }
        else { *ea = y; *eb = x; }
        return 1;
    }
    return 0;
}

/* Degree-preserving 2-switch: (a,b),(c,e) -> (a,e),(c,b). a,c on side 0. */
static int move_switch(void) {
    int a, b, c, e;
    if (!rand_edge(&a, &b) || !rand_edge(&c, &e)) return 0;
    if (a == c || b == e) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    do_del(a, b);
    do_del(c, e);
    do_add(a, e);
    do_add(c, b);
    return 1;
}

static int move_add(void) {
    for (int t = 0; t < 50; t++) {
        int a = rndint(N), b = rndint(N);
        if (side[a] != 0 || side[b] != 1) continue;
        if (deg[a] >= d || deg[b] >= d || has_edge(a, b)) continue;
        do_add(a, b);
        return 1;
    }
    return 0;
}

/* Move one endpoint of an edge to a vertex with spare degree on the same side. */
static int move_rewire(void) {
    int a, b;
    if (!rand_edge(&a, &b)) return 0;
    int which = rndint(2);
    for (int t = 0; t < 50; t++) {
        if (which == 0) {
            int bb = rndint(N);
            if (side[bb] != 1 || bb == b || deg[bb] >= d || has_edge(a, bb)) continue;
            do_del(a, b);
            do_add(a, bb);
            return 1;
        } else {
            int aa = rndint(N);
            if (side[aa] != 0 || aa == a || deg[aa] >= d || has_edge(aa, b)) continue;
            do_del(a, b);
            do_add(aa, b);
            return 1;
        }
    }
    return 0;
}

static int move_delete(void) {
    int a, b;
    if (!rand_edge(&a, &b)) return 0;
    do_del(a, b);
    return 1;
}

/* Add vertex N with up to d neighbours on the opposite side. Full neighbours lose one edge. */
static void grow_vertex(void) {
    int v = N;
    N++;
    side[v] = rndint(2);
    deg[v] = 0;
    for (int i = 0; i < d; i++) {
        int u = -1;
        for (int t = 0; t < 400 && u < 0; t++) {
            int c = rndint(v);
            if (side[c] != side[v] && deg[c] < d && !has_edge(v, c)) u = c;
        }
        if (u < 0) {
            for (int t = 0; t < 400 && u < 0; t++) {
                int c = rndint(v);
                if (side[c] != side[v] && !has_edge(v, c)) u = c;
            }
            if (u < 0) break;
            if (deg[u] >= d) {
                int x = adj[u][rndint(deg[u])];
                del_arc(u, x);
                del_arc(x, u);
            }
        }
        add_arc(v, u);
        add_arc(u, v);
    }
}

static void save_best(void) {
    bestN = N;
    memcpy(bestDeg, deg, sizeof(int) * (size_t)N);
    memcpy(bestSide, side, sizeof(int) * (size_t)N);
    memcpy(bestAdj, adj, sizeof(int) * (size_t)MAXDEG * (size_t)N);
    best_ok = 1;
}

static void restore_best(void) {
    N = bestN;
    memcpy(deg, bestDeg, sizeof(int) * (size_t)N);
    memcpy(side, bestSide, sizeof(int) * (size_t)N);
    memcpy(adj, bestAdj, sizeof(int) * (size_t)MAXDEG * (size_t)N);
    nop = 0;
}

static double moore_bound(void) {
    if (d <= 1) return 2.0;
    if (d == 2) return 2.0 * D;
    double s = 0, p = 1;
    for (int i = 0; i < D; i++) { s += p; p *= (d - 1); }
    return 2.0 * s;
}

static void emit(int n, int A[][MAXDEG], const int *dg, const int *sd) {
    long m = 0;
    for (int v = 0; v < n; v++)
        if (sd[v] == 0) m += dg[v];
    printf("%d %ld\n", n, m);
    for (int v = 0; v < n; v++) {
        if (sd[v] != 0) continue;
        for (int i = 0; i < dg[v]; i++) printf("%d %d\n", v, A[v][i]);
    }
}

static void echo_input(int n, int m, const int *eu, const int *ev) {
    printf("%d %d\n", n, m);
    for (int i = 0; i < m; i++) printf("%d %d\n", eu[i], ev[i]);
}

static int load_graph(int n, int m, const int *eu, const int *ev) {
    if (n < 2 || n > MAXN - 512 || d < 1 || d > MAXDEG) return 0;
    N = n;
    memset(deg, 0, sizeof(deg));
    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (has_edge(u, v)) return 0;
        if (deg[u] >= d || deg[v] >= d) return 0;
        add_arc(u, v);
        add_arc(v, u);
    }
    for (int v = 0; v < N; v++) side[v] = -1;
    int *q = malloc(sizeof(int) * (size_t)N);
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int x = q[h++];
            for (int i = 0; i < deg[x]; i++) {
                int y = adj[x][i];
                if (side[y] < 0) {
                    side[y] = 1 - side[x];
                    q[t++] = y;
                } else if (side[y] == side[x]) {
                    free(q);
                    return 0;
                }
            }
        }
    }
    free(q);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    rs ^= 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    clock_t c0 = clock();

    int n_in = 0, m_in = 0;
    if (scanf("%d %d", &n_in, &m_in) != 2) { n_in = 0; m_in = 0; }
    if (m_in < 0) m_in = 0;
    int *eu = malloc(sizeof(int) * (size_t)(m_in + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m_in + 1));
    int got = 0;
    for (int i = 0; i < m_in; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) break;
        got++;
    }
    m_in = got;

    if (D < 1 || !load_graph(n_in, m_in, eu, ev)) {
        echo_input(n_in, m_in, eu, ev);
        return 0;
    }

    CAP = n_in + 400;
    if (CAP > MAXN) CAP = MAXN;
    W = (CAP + 63) / 64;
    bufA = calloc((size_t)CAP * W, sizeof(uint64_t));
    bufB = calloc((size_t)CAP * W, sizeof(uint64_t));
    double moore = moore_bound();

    long long cost = bad_pairs();
    const int STEP = 6000;
    const double T0 = 2.5, T1 = 0.15;
    int step = 0;
    long long it = 0;

    while (1) {
        if ((it++ & 15) == 0 && (double)(clock() - c0) / CLOCKS_PER_SEC > tl) break;

        if (cost == 0) {
            save_best();
            if ((double)N >= moore || N >= CAP) break;
            grow_vertex();
            cost = bad_pairs();
            step = 0;
            continue;
        }

        if (step >= STEP) {
            step = 0;
            if (best_ok) {
                restore_best();
                cost = 0;
                continue;
            }
        }

        double frac = (double)step / (double)STEP;
        double T = T0 * pow(T1 / T0, frac);
        nop = 0;
        double r = rnd01();
        int ok;
        if (r < 0.40) ok = move_switch();
        else if (r < 0.60) ok = move_add();
        else if (r < 0.85) ok = move_rewire();
        else ok = move_delete();
        step++;
        if (!ok) { nop = 0; continue; }

        long long c2 = bad_pairs();
        long long delta = c2 - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cost = c2;
        else undo_all();
        nop = 0;
    }

    if (cost == 0) save_best();
    if (best_ok) emit(bestN, bestAdj, bestDeg, bestSide);
    else echo_input(n_in, m_in, eu, ev);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence. Each old vertex has spare capacity
# s = d - q - 1. Choose S with every line holding <= s points of S and every
# point on <= s lines of S. For each P in S add a new A-vertex joined to the
# lines through P; for each j in S add a new B-vertex joined to the points on j.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points, pts


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
    """Conic (plus nucleus for even q) as a point-index set."""
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
        m, edges, point_lines, line_points, pts = _pg_data(q)
        index = {p: i for i, p in enumerate(pts)}
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
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
    """W(q) for the largest prime power q with q + 1 <= d, with q <= 7 for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 4).
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


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Algebraic starts. Diameter 3 for the arc graphs; GQ gives diameter 4.
    if D >= 3:
        for cand in _arc_extensions(d, t0 + 0.2 * time_limit, random.Random(seed * 7919 + d)):
            consider(cand)
    if D >= 4:
        consider(_best_gq(d))
        lift_deadline = t0 + 0.3 * time_limit
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < lift_deadline:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, lift_deadline, iters=400)
            if res is not None:
                consider(res)

    # Main search: grow-and-repair in C, starting from the best valid graph.
    remaining = t0 + 0.8 * time_limit - 1.5 - time.monotonic()
    if remaining > 1.0 and d <= 60:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 15.0)
            consider(lib.parse_graph_text(text))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
