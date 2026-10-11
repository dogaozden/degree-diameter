import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: vertex insertion with ball-cover certificates, plus a NEW repair
# step. When a greedy insertion fails, the engine attaches a fresh vertex w to
# the best available opposite-colour vertices and then runs simulated annealing
# over degree-preserving bipartite double-edge swaps and spare-slide moves
# (move one endpoint of an edge onto a vertex with spare degree). The annealing
# cost is the number of vertex pairs at distance > D (bad pairs). If the cost
# reaches 0 the new vertex is kept; otherwise the state is restored. Every
# accepted state is a valid graph, so the output is always valid and never
# smaller than the input.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 4096
#define MAXD 64
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int col[MAXN];
} State;

static int n, d, D, W;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];
static unsigned char pc16[65536];
static uint64_t rs = 88172645463325252ULL;
static clock_t t0;
static double budget_s = 1.0;
static State save_r, save_start;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static int pcw(uint64_t x) {
    return pc16[x & 0xffffu] + pc16[(x >> 16) & 0xffffu]
         + pc16[(x >> 32) & 0xffffu] + pc16[(x >> 48) & 0xffffu];
}

static int time_left(void) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC < budget_s;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void rem_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) { adj[u][i] = adj[u][--deg[u]]; break; }
    }
    for (int i = 0; i < deg[v]; i++) {
        if (adj[v][i] == u) { adj[v][i] = adj[v][--deg[v]]; break; }
    }
}

static void save_state(State *s) {
    s->n = n;
    memcpy(s->deg, deg, sizeof(int) * (size_t)n);
    memcpy(s->adj, adj, sizeof(int) * MAXD * (size_t)n);
    memcpy(s->col, col, sizeof(int) * (size_t)n);
}

static void load_state(const State *s) {
    n = s->n;
    memcpy(deg, s->deg, sizeof(int) * (size_t)n);
    memcpy(adj, s->adj, sizeof(int) * MAXD * (size_t)n);
    memcpy(col, s->col, sizeof(int) * (size_t)n);
}

static void shuffle(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = (int)(rnd() % (uint32_t)(i + 1));
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

static void compute_balls(int R) {
    W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        memset(reach[v], 0, sizeof(uint64_t) * (size_t)W);
        reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            memcpy(nxt[v], reach[v], sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *ru = reach[adj[v][i]];
                for (int w = 0; w < W; w++) nxt[v][w] |= ru[w];
            }
        }
        for (int v = 0; v < n; v++)
            memcpy(reach[v], nxt[v], sizeof(uint64_t) * (size_t)W);
    }
}

static long bad_pairs(void) {
    compute_balls(D);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pcw(reach[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static int covers_all(const uint64_t *cov) {
    for (int w = 0; w < W; w++) {
        uint64_t want;
        if (w < W - 1) {
            want = ~0ULL;
        } else {
            int r = n - 64 * (W - 1);
            want = (r >= 64) ? ~0ULL : ((1ULL << r) - 1);
        }
        if ((cov[w] & want) != want) return 0;
    }
    return 1;
}

/* Greedy insertion certified by radius D-1 balls (reach must be current). */
static int try_insert(int side) {
    static int cand[MAXN];
    static char usedv[MAXN];
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (col[u] != side && deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    shuffle(cand, nc);
    memset(usedv, 0, (size_t)n);
    uint64_t cov[MAXW];
    memset(cov, 0, sizeof(cov));
    int chosen[MAXD];
    int nch = 0;
    while (nch < d && !covers_all(cov)) {
        int best = -1, bg = 0;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (usedv[u]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += pcw(reach[u][w] & ~cov[w]);
            if (g > bg) { bg = g; best = u; }
        }
        if (best < 0) break;
        usedv[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) cov[w] |= reach[best][w];
    }
    if (!covers_all(cov)) return 0;
    int w = n;
    n++;
    col[w] = side;
    deg[w] = 0;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], w);
    return 1;
}

/* Degree-preserving bipartite double-edge swap: remove (a,b),(c,e), add (a,e),(c,b). */
static int pick_swap(int *ra, int *rb, int *rc, int *re) {
    int a = (int)(rnd() % (uint32_t)n);
    if (deg[a] == 0) return 0;
    int b = adj[a][rnd() % (uint32_t)deg[a]];
    int c = -1;
    for (int t = 0; t < 8 && c < 0; t++) {
        int x = (int)(rnd() % (uint32_t)n);
        if (x != a && col[x] == col[a] && deg[x] > 0) c = x;
    }
    if (c < 0) return 0;
    int e = adj[c][rnd() % (uint32_t)deg[c]];
    if (e == b || has_edge(a, e) || has_edge(c, b)) return 0;
    *ra = a; *rb = b; *rc = c; *re = e;
    return 1;
}

static void apply_swap(int a, int b, int c, int e) {
    rem_edge(a, b);
    rem_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
}

/* Spare-slide: move the edge (a,b) to (a,c) where c has spare degree. */
static int pick_slide(int *ra, int *rb, int *rc) {
    int c = (int)(rnd() % (uint32_t)n);
    if (deg[c] >= d) return 0;
    int a = (int)(rnd() % (uint32_t)n);
    if (col[a] == col[c] || deg[a] == 0) return 0;
    int b = adj[a][rnd() % (uint32_t)deg[a]];
    if (b == c || has_edge(a, c)) return 0;
    *ra = a; *rb = b; *rc = c;
    return 1;
}

static void apply_slide(int a, int b, int c) {
    rem_edge(a, b);
    add_edge(a, c);
}

static void undo_slide(int a, int b, int c) {
    rem_edge(a, c);
    add_edge(a, b);
}

/* Attach a new vertex on `side`, then anneal bad-pair cost to zero. */
static int repair_try(int side, int iters) {
    if (n >= MAXN - 2) return 0;
    save_state(&save_r);
    compute_balls(D - 1);
    static int cand[MAXN];
    static char usedv[MAXN];
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (col[u] != side && deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    shuffle(cand, nc);
    memset(usedv, 0, (size_t)n);
    uint64_t cov[MAXW];
    memset(cov, 0, sizeof(cov));
    int chosen[MAXD];
    int nch = 0;
    while (nch < d) {
        int best = -1, bg = -1;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (usedv[u]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += pcw(reach[u][w] & ~cov[w]);
            if (g > bg) { bg = g; best = u; }
        }
        if (best < 0) break;
        usedv[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) cov[w] |= reach[best][w];
    }
    int w = n;
    n++;
    col[w] = side;
    deg[w] = 0;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], w);

    long cost = bad_pairs();
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 31) == 0 && !time_left()) break;
        double T = 1.5 * (1.0 - (double)it / (double)iters) + 0.15;
        int x1 = 0, x2 = 0, x3 = 0, x4 = 0;
        int is_swap = ((rnd() % 100u) < 60u);
        int ok = is_swap ? pick_swap(&x1, &x2, &x3, &x4)
                         : pick_slide(&x1, &x2, &x3);
        if (!ok) continue;
        if (is_swap) apply_swap(x1, x2, x3, x4);
        else apply_slide(x1, x2, x3);
        long c2 = bad_pairs();
        long delta = c2 - cost;
        int acc = (delta <= 0);
        if (!acc) {
            double p = exp(-(double)delta / T);
            acc = ((double)(rnd() % 1000000u) / 1000000.0) < p;
        }
        if (acc) {
            cost = c2;
        } else {
            if (is_swap) apply_swap(x1, x4, x3, x2);
            else undo_slide(x1, x2, x3);
        }
    }
    if (cost == 0) return 1;
    load_state(&save_r);
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    budget_s = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 1; i < 65536; i++) pc16[i] = (unsigned char)(pc16[i >> 1] + (i & 1));
    t0 = clock();

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2) { printf("0 0\n"); return 0; }
    if (N0 < 1 || N0 >= MAXN - 2) { printf("0 0\n"); return 0; }
    n = N0;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    /* Bipartition by BFS; reject if an edge joins equal colours. */
    static int queue[MAXN];
    for (int s = 0; s < n; s++) col[s] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) { col[v] = 1 - col[u]; queue[qt++] = v; }
            }
        }
    }
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (col[adj[u][i]] == col[u]) { printf("0 0\n"); return 0; }

    /* Start must already be valid. */
    if (bad_pairs() != 0) { printf("0 0\n"); return 0; }
    save_state(&save_start);

    int fails = 0;
    const int maxfails = 150;
    const int iters = 1500;
    while (fails < maxfails && n < MAXN - 2 && time_left()) {
        compute_balls(D - 1);
        int sides[2] = {0, 1};
        if (rnd() & 1u) { sides[0] = 1; sides[1] = 0; }
        int ok = 0;
        for (int k = 0; k < 2 && !ok; k++) ok = try_insert(sides[k]);
        if (ok) { fails = 0; continue; }
        for (int k = 0; k < 2 && !ok && time_left(); k++)
            ok = repair_try(sides[k], iters);
        if (ok) { fails = 0; continue; }
        fails++;
        /* Plateau walk: spare-slides that keep the graph valid. */
        for (int t = 0; t < 20 && time_left(); t++) {
            int x1, x2, x3;
            if (!pick_slide(&x1, &x2, &x3)) continue;
            apply_slide(x1, x2, x3);
            if (bad_pairs() != 0) undo_slide(x1, x2, x3);
        }
    }

    if (bad_pairs() != 0) load_state(&save_start);
    int m2 = 0;
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) m2++;
    printf("%d %d\n", n, m2);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) printf("%d %d\n", u, adj[u][i]);
    return 0;
}
"""


def _c_augment(graph, d, D, seed, budget):
    """Run the C engine on graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 0.5 or d > 64:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 4.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# A-side: a set SA of points. Each SA point P gets a new vertex joined to the
#         q+1 lines through P. Each line holds <= s points of SA.
# B-side: a set SB of lines. Each j in SB gets a new vertex joined to the q+1
#         points on j. Each point lies on <= s lines of SB.
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
    """True if every target is hit by <= s elements of S, where element x hits nbr[x]."""
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
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
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
# Driver. Time plan (fractions of time_limit):
#   0.00-0.25  arc-extended PG graphs with local search
#   D >= 4:    GQ baseline, then annealed group voltage lifts until 0.60
#   final:     C insertion + bad-pair annealing repair on the best graph,
#              until 0.90 (minus a compile allowance)
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    def el():
        return time.monotonic() - start

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        cands = _arc_extensions(d, start + 0.25 * time_limit,
                                random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for g in cands[:3]:
            consider(g)

    if D >= 4 and el() < 0.50 * time_limit:
        consider(_best_gq(d))
        anneal_end = start + 0.60 * time_limit
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < anneal_end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, anneal_end, iters=400)
            if res is not None:
                consider(res)

    # Final C pass: insertion plus repair search from the best graph so far.
    cbudget = 0.90 * time_limit - el() - 2.0
    if cbudget >= 0.5:
        consider(_c_augment(best, d, D, seed + 1, cbudget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
