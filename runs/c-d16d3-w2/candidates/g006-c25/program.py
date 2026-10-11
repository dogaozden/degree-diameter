import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# A-side: a set SA of points. Each SA point P gets a new vertex joined to all
#         q+1 lines through P. Constraint: every line holds <= s points of SA.
# B-side: a set SB of lines. Each j in SB gets a new vertex joined to all
#         q+1 points on j. Constraint: every point lies on <= s lines of SB.
# ----------------------------------------------------------------------------

_LS_ITERS = 30000


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
    """True if every target t is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements x so that every target is hit by <= s chosen elements."""
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
    """Plateau/improvement local search for the same load-constrained set problem."""
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
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
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
# Simulated annealing over bi-Cayley voltage lifts (fallback for D >= 4).
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
# C engine: bipartite graph growth by annealing on the bad-pair count.
#
# Given a valid bipartite graph, add one vertex on a chosen side and anneal
# with degree-preserving 2-switches, rewires, adds and removes until every
# pair is within distance D again. Cost = number of unordered pairs at
# distance > D, computed with bitset ball expansion. On success the grown
# graph becomes the new incumbent. Output is always the best valid graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1500
#define MAXDEG 40
#define MAXW ((MAXN + 63) / 64)
#define MAXE (MAXN * MAXDEG / 2 + 16)

static int D = 3;
static int DEGMAX = 3;
static int n = 0;
static int nw = 1;
static int side[MAXN];
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static unsigned char M[MAXN][MAXN];
static uint64_t bufA[MAXN][MAXW];
static uint64_t bufB[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static int best_n = 0;
static int best_m = 0;
static int best_side[MAXN];
static int best_eu[MAXE];
static int best_ev[MAXE];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rnd(int k) { return (int)(rnd64() % (uint64_t)k); }
static double urand(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double clk(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long cost_full(void) {
    uint64_t (*cur)[MAXW] = bufA;
    uint64_t (*nxt)[MAXW] = bufB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < nw; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int step = 0; step < D; step++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < nw; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < nw; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += pc64(cur[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static void rem_adj(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][--deg[u]];
            return;
        }
    }
}

static void add_edge(int u, int v) {
    M[u][v] = 1;
    M[v][u] = 1;
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_edge(int u, int v) {
    M[u][v] = 0;
    M[v][u] = 0;
    rem_adj(u, v);
    rem_adj(v, u);
}

static void clear_graph(void) {
    for (int u = 0; u < n; u++) {
        for (int i = 0; i < deg[u]; i++) M[u][adj[u][i]] = 0;
        deg[u] = 0;
    }
}

/* Replace the current graph by (nn vertices, sides s, m edges). Returns 0 on violation. */
static int set_graph(int nn, const int *s, int m, const int *eu, const int *ev) {
    clear_graph();
    n = nn;
    nw = (n + 63) / 64;
    if (nw < 1) nw = 1;
    for (int u = 0; u < n; u++) {
        side[u] = s[u];
        deg[u] = 0;
    }
    for (int i = 0; i < m; i++) {
        int a = eu[i], b = ev[i];
        if (a < 0 || b < 0 || a >= n || b >= n || a == b) return 0;
        if (side[a] == side[b] || M[a][b]) return 0;
        if (deg[a] >= DEGMAX || deg[b] >= DEGMAX) return 0;
        add_edge(a, b);
    }
    return 1;
}

static int color_graph(void) {
    static int col[MAXN];
    static int stack[MAXN];
    for (int u = 0; u < n; u++) col[u] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        stack[sp++] = s;
        while (sp > 0) {
            int u = stack[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    stack[sp++] = v;
                } else if (col[v] == col[u]) {
                    return 0;
                }
            }
        }
    }
    for (int u = 0; u < n; u++) side[u] = col[u];
    return 1;
}

static void snapshot(void) {
    best_n = n;
    best_m = 0;
    for (int u = 0; u < n; u++) best_side[u] = side[u];
    for (int u = 0; u < n; u++) {
        for (int v = u + 1; v < n; v++) {
            if (M[u][v]) {
                if (best_m >= MAXE) return;
                best_eu[best_m] = u;
                best_ev[best_m] = v;
                best_m++;
            }
        }
    }
}

static void print_best(void) {
    if (best_n <= 0) {
        printf("0 0\n");
        return;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", best_eu[i], best_ev[i]);
}

typedef struct {
    int nr, na;
    int ru[2], rv[2], au[2], av[2];
} Move;

static void apply_move(const Move *m) {
    for (int i = 0; i < m->nr; i++) del_edge(m->ru[i], m->rv[i]);
    for (int i = 0; i < m->na; i++) add_edge(m->au[i], m->av[i]);
}

static void undo_move(const Move *m) {
    for (int i = 0; i < m->na; i++) del_edge(m->au[i], m->av[i]);
    for (int i = 0; i < m->nr; i++) add_edge(m->ru[i], m->rv[i]);
}

static int propose(Move *m, int focus) {
    m->nr = 0;
    m->na = 0;
    int r = rnd(100);
    if (r < 25) {
        int u = (focus >= 0 && rnd(10) < 3) ? focus : rnd(n);
        int v = rnd(n);
        if (u == v || side[u] == side[v] || M[u][v] || deg[u] >= DEGMAX || deg[v] >= DEGMAX) return 0;
        m->na = 1;
        m->au[0] = u;
        m->av[0] = v;
        return 1;
    }
    if (r < 35) {
        int u = rnd(n);
        if (deg[u] == 0) return 0;
        int v = adj[u][rnd(deg[u])];
        m->nr = 1;
        m->ru[0] = u;
        m->rv[0] = v;
        return 1;
    }
    if (r < 75) {
        int a = rnd(n), c = rnd(n);
        if (a == c || deg[a] == 0 || deg[c] == 0 || side[a] != side[c]) return 0;
        int b = adj[a][rnd(deg[a])];
        int e = adj[c][rnd(deg[c])];
        if (b == e || M[a][e] || M[c][b]) return 0;
        m->nr = 2;
        m->ru[0] = a;
        m->rv[0] = b;
        m->ru[1] = c;
        m->rv[1] = e;
        m->na = 2;
        m->au[0] = a;
        m->av[0] = e;
        m->au[1] = c;
        m->av[1] = b;
        return 1;
    }
    /* rewire one endpoint of an edge to another vertex on the same side */
    int a = rnd(n);
    if (deg[a] == 0) return 0;
    int b = adj[a][rnd(deg[a])];
    int e = (focus >= 0 && rnd(10) < 3) ? focus : rnd(n);
    if (e == a || e == b || side[e] != side[b] || M[a][e] || deg[e] >= DEGMAX) return 0;
    m->nr = 1;
    m->ru[0] = a;
    m->rv[0] = b;
    m->na = 1;
    m->au[0] = a;
    m->av[0] = e;
    return 1;
}

static int anneal(double t_end, int focus) {
    long long cost = cost_full();
    if (cost == 0) return 1;
    double t0 = clk();
    double span = t_end - t0;
    if (span <= 0.0) return 0;
    double T = 2.0;
    Move mv;
    long long it = 0;
    for (;;) {
        if ((it & 31) == 0) {
            double now = clk();
            if (now >= t_end) break;
            double f = (now - t0) / span;
            T = 2.0 * pow(0.01, f);
        }
        it++;
        if (!propose(&mv, focus)) continue;
        apply_move(&mv);
        long long c2 = cost_full();
        long long delta = c2 - cost;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            cost = c2;
            if (cost == 0) return 1;
        } else {
            undo_move(&mv);
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    DEGMAX = d < MAXDEG ? d : MAXDEG;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 16; i++) rnd64();

    int rn = 0, rm = 0;
    if (scanf("%d %d", &rn, &rm) != 2) {
        printf("0 0\n");
        return 0;
    }
    if (rn <= 0 || rn > MAXN || rm < 0 || rm > MAXE) {
        printf("0 0\n");
        return 0;
    }
    static int eu[MAXE];
    static int ev[MAXE];
    static int zero_side[MAXN];
    for (int i = 0; i < rm; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) {
            printf("0 0\n");
            return 0;
        }
    }
    if (!set_graph(rn, zero_side, rm, eu, ev)) {
        printf("0 0\n");
        return 0;
    }
    if (!color_graph()) {
        printf("0 0\n");
        return 0;
    }

    double t_end = clk() + limit;
    if (cost_full() > 0) {
        anneal(clk() + (t_end - clk()) * 0.3, -1);
    }
    if (cost_full() > 0) {
        printf("0 0\n");
        return 0;
    }
    snapshot();

    static int ns[MAXN];
    int parity = 0;
    while (clk() < t_end - 0.02) {
        double remaining = t_end - clk();
        int grew = 0;
        for (int t = 0; t < 2 && !grew; t++) {
            if (clk() >= t_end - 0.02) break;
            int s_new = (parity + t) & 1;
            for (int i = 0; i < best_n; i++) ns[i] = best_side[i];
            ns[best_n] = s_new;
            if (!set_graph(best_n + 1, ns, best_m, best_eu, best_ev)) break;
            double budget = remaining * 0.5;
            if (anneal(clk() + budget, best_n)) {
                grew = 1;
                snapshot();
            }
        }
        parity ^= 1;
    }

    print_best();
    return 0;
}
"""


def build(d, D, seed, time_limit):
    start = time.monotonic()
    arc_deadline = start + 0.25 * time_limit
    c_deadline = start + 0.85 * time_limit
    deadline = start + 0.93 * time_limit
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

    # Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        cands = _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    if D >= 4 and time.monotonic() < arc_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # New: grow the incumbent in C by annealing extra vertices into it.
    if best_n < lib.moore_bound(d, D):
        now = time.monotonic()
        rem = c_deadline - now
        if rem > 1.5:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(rem * 0.85 - 0.3, 2)],
                                stdin_graph=best,
                                timeout=max(1.0, deadline - now))
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except (RuntimeError, ValueError):
                pass

    # Voltage-lift annealing for the remaining time (mainly useful for D >= 4).
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
