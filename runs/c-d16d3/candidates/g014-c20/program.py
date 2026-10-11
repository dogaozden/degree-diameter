import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset-cost annealing with vertex insertion by edge stealing.
#
# Input: a bipartite graph valid for (d, D), as "n m" plus edges (or "0 0").
# The engine keeps max degree <= d and bipartiteness. It grows the graph by
# adding a pair of new vertices (one on each side). Each new vertex takes d
# edges by stealing: remove (u, v) and add (x, v), so the other endpoint keeps
# its degree. This leaves deficiencies that the moves fill. The cost is the
# number of unordered pairs at distance > D, computed with bitset balls. Moves
# are 2-switches, edge additions, endpoint moves and rare removals. When the
# cost reaches 0 the state is snapshotted and the graph grows again. After
# repeated failures it reverts to the best valid snapshot.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 2048
#define WMAX ((NMAX + 63) / 64)
#define DMAX 64
#define EMAX (NMAX * DMAX / 2 + 64)
#define STAGE_ITERS 25000LL
#define MAXFAIL 6

static int N = 0;
static int DEG_CAP = 3;
static int DIST = 3;
static double TLIM = 1.0;
static clock_t T_START;

static int deg[NMAX];
static int nb[NMAX][DMAX];
static unsigned char A[NMAX][NMAX];
static int side[NMAX];
static uint64_t RA[NMAX * WMAX], RB[NMAX * WMAX];
static uint64_t rs = 88172645463325252ULL;

static int inU[EMAX], inV[EMAX];
static int tmpU[EMAX], tmpV[EMAX];
static int bestN = 0, bestM = 0;
static int bestU[EMAX], bestV[EMAX];

static int mk, ma, mb, mc, md;

static uint64_t rnd64(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static int rnd_int(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) { return (double)(clock() - T_START) / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void del_from(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nb[u][i] == v) {
            nb[u][i] = nb[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void add_edge(int u, int v) {
    A[u][v] = 1;
    A[v][u] = 1;
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
}

static void del_edge(int u, int v) {
    A[u][v] = 0;
    A[v][u] = 0;
    del_from(u, v);
    del_from(v, u);
}

/* Number of unordered pairs at distance > DIST (including unreachable). */
static long long bad_pairs(void) {
    int W = (N + 63) >> 6;
    uint64_t *cur = RA, *nxt = RB;
    for (int v = 0; v < N; v++) {
        uint64_t *r = cur + (size_t)v * W;
        memset(r, 0, sizeof(uint64_t) * (size_t)W);
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < DIST; it++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s = cur + (size_t)nb[v][i] * W;
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *r = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(r[w]);
        tot += N - c;
    }
    return tot / 2;
}

static int collect_edges(int *U, int *V) {
    int m = 0;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = nb[v][i];
            if (v < u) {
                U[m] = v;
                V[m] = u;
                m++;
            }
        }
    }
    return m;
}

static void snapshot(void) {
    bestN = N;
    bestM = collect_edges(bestU, bestV);
}

static void clear_graph(void) {
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg[v]; i++) A[v][nb[v][i]] = 0;
        deg[v] = 0;
    }
}

static void load_best(void) {
    clear_graph();
    N = bestN;
    for (int i = 0; i < bestM; i++) add_edge(bestU[i], bestV[i]);
}

static int color_graph(void) {
    static int q[NMAX];
    static int seen[NMAX];
    for (int v = 0; v < N; v++) seen[v] = 0;
    for (int s = 0; s < N; s++) {
        if (seen[s]) continue;
        seen[s] = 1;
        side[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int v = q[qh++];
            for (int i = 0; i < deg[v]; i++) {
                int u = nb[v][i];
                if (!seen[u]) {
                    seen[u] = 1;
                    side[u] = 1 - side[v];
                    q[qt++] = u;
                } else if (side[u] == side[v]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Insert one new vertex on each side; each takes DEG_CAP edges by stealing. */
static int add_pair(void) {
    if (N + 2 > NMAX) return 0;
    int x = N, y = N + 1;
    side[x] = 0;
    side[y] = 1;
    deg[x] = 0;
    deg[y] = 0;
    N += 2;
    int tries = 0;
    while (deg[x] < DEG_CAP && tries < 100000) {
        tries++;
        int u = rnd_int(N);
        if (u == x || u == y || side[u] != 0 || deg[u] == 0) continue;
        int v = nb[u][rnd_int(deg[u])];
        if (v == y || A[x][v]) continue;
        del_edge(u, v);
        add_edge(x, v);
    }
    tries = 0;
    while (deg[y] < DEG_CAP && tries < 100000) {
        tries++;
        int v = rnd_int(N);
        if (v == x || v == y || side[v] != 1 || deg[v] == 0) continue;
        int u = nb[v][rnd_int(deg[v])];
        if (u == x || A[u][y]) continue;
        del_edge(u, v);
        add_edge(u, y);
    }
    return 1;
}

static int pick(int s, int mindeg) {
    for (int t = 0; t < 200; t++) {
        int v = rnd_int(N);
        if (side[v] == s && deg[v] >= mindeg) return v;
    }
    return -1;
}

static int pick_free(int s) {
    for (int t = 0; t < 200; t++) {
        int v = rnd_int(N);
        if (side[v] == s && deg[v] < DEG_CAP) return v;
    }
    return -1;
}

static int apply_move(int kind) {
    mk = kind;
    if (kind == 0) {  /* 2-switch, degrees preserved */
        int a = pick(0, 1);
        if (a < 0) return 0;
        int b = nb[a][rnd_int(deg[a])];
        int a2 = pick(0, 1);
        if (a2 < 0 || a2 == a) return 0;
        int b2 = nb[a2][rnd_int(deg[a2])];
        if (b2 == b || A[a][b2] || A[a2][b]) return 0;
        del_edge(a, b);
        del_edge(a2, b2);
        add_edge(a, b2);
        add_edge(a2, b);
        ma = a; mb = b; mc = a2; md = b2;
        return 1;
    }
    if (kind == 1) {  /* add an edge between deficient vertices */
        int a = pick_free(0);
        int b = pick_free(1);
        if (a < 0 || b < 0 || A[a][b]) return 0;
        add_edge(a, b);
        ma = a; mb = b;
        return 1;
    }
    if (kind == 2) {  /* move one endpoint of an edge */
        int a = pick(0, 1);
        if (a < 0) return 0;
        int b = nb[a][rnd_int(deg[a])];
        int b2 = pick_free(1);
        if (b2 < 0 || b2 == b || A[a][b2]) return 0;
        del_edge(a, b);
        add_edge(a, b2);
        ma = a; mb = b; mc = b2;
        return 1;
    }
    {  /* remove an edge */
        int a = pick(0, 1);
        if (a < 0) return 0;
        int b = nb[a][rnd_int(deg[a])];
        del_edge(a, b);
        ma = a; mb = b;
        return 1;
    }
}

static void undo_move(void) {
    if (mk == 0) {
        del_edge(ma, md);
        del_edge(mc, mb);
        add_edge(ma, mb);
        add_edge(mc, md);
    } else if (mk == 1) {
        del_edge(ma, mb);
    } else if (mk == 2) {
        del_edge(ma, mc);
        add_edge(ma, mb);
    } else {
        add_edge(ma, mb);
    }
}

static long long anneal(long long iters, double T0, double T1) {
    long long cur = bad_pairs();
    for (long long it = 0; it < iters && cur > 0; it++) {
        if ((it & 127) == 0 && elapsed() > TLIM) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        double r = rnd_unit();
        int kind = r < 0.55 ? 0 : (r < 0.85 ? 1 : (r < 0.98 ? 2 : 3));
        if (!apply_move(kind)) continue;
        long long nc = bad_pairs();
        long long delta = nc - cur;
        if (delta <= 0 || rnd_unit() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            undo_move();
        }
    }
    return cur;
}

static void print_graph(int n, int m, const int *U, const int *V) {
    printf("%d %d\n", n, m);
    for (int i = 0; i < m; i++) printf("%d %d\n", U[i], V[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    int d = atoi(argv[1]);
    DIST = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 5; i++) rnd64();
    T_START = clock();
    TLIM = budget * 0.9 - 0.2;
    if (TLIM < 0.05) TLIM = 0.05;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (m0 < 0 || m0 > EMAX) m0 = 0;
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &inU[i], &inV[i]) != 2) { m0 = i; break; }
    }
    if (d < 1 || d > DMAX || DIST < 1) {
        print_graph(n0, m0, inU, inV);
        return 0;
    }
    DEG_CAP = d;
    if (n0 > NMAX - 64) {
        print_graph(n0, m0, inU, inV);
        return 0;
    }

    if (n0 == 0) {
        N = 2 * d;
        for (int i = 0; i < d; i++) {
            side[i] = 0;
            side[d + i] = 1;
        }
        for (int i = 0; i < d; i++)
            for (int j = 0; j < d; j++)
                add_edge(i, d + j);
    } else {
        N = n0;
        for (int i = 0; i < m0; i++) {
            int u = inU[i], v = inV[i];
            if (u < 0 || v < 0 || u >= N || v >= N || u == v || A[u][v]) continue;
            if (deg[u] >= DEG_CAP || deg[v] >= DEG_CAP) continue;
            add_edge(u, v);
        }
        if (!color_graph()) {
            int m = collect_edges(tmpU, tmpV);
            print_graph(N, m, tmpU, tmpV);
            return 0;
        }
    }

    long long cur = bad_pairs();
    if (cur == 0) snapshot();
    int fails = 0;
    while (elapsed() < TLIM) {
        if (cur == 0) {
            snapshot();
            if (!add_pair()) break;
            fails = 0;
            cur = bad_pairs();
            continue;
        }
        cur = anneal(STAGE_ITERS, 1.5, 0.08);
        if (cur == 0) continue;
        fails++;
        if (fails >= MAXFAIL && bestN > 0) {
            load_best();
            cur = bad_pairs();
            fails = 0;
        }
    }
    if (cur == 0) snapshot();
    if (bestN > 0) {
        print_graph(bestN, bestM, bestU, bestV);
    } else {
        int m = collect_edges(tmpU, tmpV);
        print_graph(N, m, tmpU, tmpV);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Projective-plane arc extensions (diameter 3), from the parent.
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


_LP = None


def _arc_graph(m, edges, point_lines, S):
    """Build the extended graph: old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in _LP[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    global _LP
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        _LP = line_points
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
        n_c, e_c = _arc_graph(m, edges, point_lines, S)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4), from the parent.
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
# Group voltage lift annealing (D >= 5), from the parent, small time share.
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
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

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
        cands = _arc_extensions(d, start + 0.15 * time_limit,
                                random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    if D >= 4 and time.monotonic() < start + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Group voltage lifts, only for larger diameters and a small time share.
    if D >= 5:
        g_deadline = start + 0.25 * time_limit
        grng = random.Random(seed + 17)
        ks = [1, 2, 2, 3, 4]
        while time.monotonic() < g_deadline:
            k = grng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + grng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, grng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, grng, g_deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # Main search: C vertex insertion with bitset-cost annealing.
    remaining = time_limit - (time.monotonic() - start)
    c_budget = min(remaining * 0.85 - 1.0, remaining - 5.0)
    if c_budget >= 1.0 and d <= 60 and best[0] <= 1984:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                             stdin_graph=best, timeout=c_budget + 4.0)
            n, e = lib.parse_graph_text(text)
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
