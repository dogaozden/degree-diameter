import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset simulated annealing that grows a valid graph by one vertex
# at a time. Cost = number of vertex pairs at distance > D. Moves keep max
# degree <= d and bipartiteness (fixed sides), and each time cost reaches 0
# the engine snapshots the graph and adds a new vertex with degree 0.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int d, D, n, cap, W;
static int *deg, *adj, *side, *degS, *adjS, *sDeg, *sAdj, *A, *B, *Q;
static int nA, nB;
static int *eu, *ev, n0g, m0g;
static uint64_t *R, *R2;
static uint64_t rs;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int irand(int k) { return (int)(rnd() % (uint64_t)k); }

static int pop64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int find_idx(int v, int u) {
    for (int k = 0; k < deg[v]; k++) if (adj[v * d + k] == u) return k;
    return -1;
}
static int is_adj(int a, int b) { return find_idx(a, b) >= 0; }
static void add_edge(int a, int b) {
    adj[a * d + deg[a]++] = b;
    adj[b * d + deg[b]++] = a;
}
static void remove_edge(int a, int b) {
    int k = find_idx(a, b), j = find_idx(b, a);
    deg[a]--; adj[a * d + k] = adj[a * d + deg[a]];
    deg[b]--; adj[b * d + j] = adj[b * d + deg[b]];
}

static long cost(void) {
    for (int v = 0; v < n; v++) {
        uint64_t *r = R + (size_t)v * W;
        memset(r, 0, sizeof(uint64_t) * W);
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = R2 + (size_t)v * W;
            memcpy(dst, R + (size_t)v * W, sizeof(uint64_t) * W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = R + (size_t)adj[v * d + k] * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t *tmp = R; R = R2; R2 = tmp;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *r = R + (size_t)v * W;
        for (int w = 0; w < W; w++) c += pop64(r[w]);
        bad += n - c;
    }
    return bad / 2;
}

static void print_graph(int N, const int *ad, const int *dg) {
    long m = 0;
    for (int v = 0; v < N; v++) m += dg[v];
    m /= 2;
    printf("%d %ld\n", N, m);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < dg[v]; k++) {
            int u = ad[v * d + k];
            if (u > v) printf("%d %d\n", v, u);
        }
}

static void print_input(void) {
    printf("%d %d\n", n0g, m0g);
    for (int i = 0; i < m0g; i++) printf("%d %d\n", eu[i], ev[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    if (D < 1) D = 1;
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (!rs) rs = 1;
    double tl = atof(argv[4]);

    if (scanf("%d %d", &n0g, &m0g) != 2 || n0g < 1 || d < 1) {
        printf("0 0\n");
        return 0;
    }
    eu = malloc(sizeof(int) * (m0g + 1));
    ev = malloc(sizeof(int) * (m0g + 1));
    for (int i = 0; i < m0g; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { m0g = i; break; }
    }

    cap = n0g + 128;
    W = (cap + 63) / 64;
    deg = calloc(cap, sizeof(int));
    degS = calloc(cap, sizeof(int));
    sDeg = calloc(cap, sizeof(int));
    adj = calloc((size_t)cap * d, sizeof(int));
    adjS = calloc((size_t)cap * d, sizeof(int));
    sAdj = calloc((size_t)cap * d, sizeof(int));
    side = calloc(cap, sizeof(int));
    A = malloc(sizeof(int) * cap);
    B = malloc(sizeof(int) * cap);
    Q = malloc(sizeof(int) * cap);
    R = calloc((size_t)cap * W, sizeof(uint64_t));
    R2 = calloc((size_t)cap * W, sizeof(uint64_t));

    n = n0g;
    int ok = 1;
    for (int i = 0; i < m0g; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v ||
            deg[u] >= d || deg[v] >= d || is_adj(u, v)) { ok = 0; break; }
        add_edge(u, v);
    }
    if (!ok) { print_input(); return 0; }

    for (int v = 0; v < n; v++) side[v] = -1;
    int bip = 1, qh = 0, qt = 0;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        Q[qt++] = s;
        while (qh < qt) {
            int u = Q[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int w = adj[u * d + k];
                if (side[w] < 0) { side[w] = 1 - side[u]; Q[qt++] = w; }
                else if (side[w] == side[u]) bip = 0;
            }
        }
    }
    if (!bip) { print_input(); return 0; }

    nA = nB = 0;
    for (int v = 0; v < n; v++) {
        if (side[v] == 0) A[nA++] = v; else B[nB++] = v;
    }

    int bestN = -1;
    long cur = cost();
    long it = 0, cyc = 60000;
    const double lnlo = log(0.04);
    clock_t t0 = clock();

    while (1) {
        if ((it & 63) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > tl) break;
        }
        it++;

        if (cur == 0) {
            memcpy(sAdj, adj, sizeof(int) * (size_t)cap * d);
            memcpy(sDeg, deg, sizeof(int) * cap);
            bestN = n;
            if (n >= cap) break;
            int s = (nA <= nB) ? 0 : 1;
            side[n] = s;
            deg[n] = 0;
            if (s == 0) A[nA++] = n; else B[nB++] = n;
            n++;
            cur = cost();
            continue;
        }
        if (nA == 0 || nB == 0) break;

        double phase = (double)(it % cyc) / (double)cyc;
        double T = exp(lnlo * phase);

        memcpy(adjS, adj, sizeof(int) * (size_t)cap * d);
        memcpy(degS, deg, sizeof(int) * cap);

        if (urand() < 0.5) {
            int a1 = A[irand(nA)], a2 = A[irand(nA)];
            if (a1 == a2 || deg[a1] == 0 || deg[a2] == 0) continue;
            int b1 = adj[a1 * d + irand(deg[a1])];
            int b2 = adj[a2 * d + irand(deg[a2])];
            if (b1 == b2 || is_adj(a1, b2) || is_adj(a2, b1)) continue;
            adj[a1 * d + find_idx(a1, b1)] = b2;
            adj[a2 * d + find_idx(a2, b2)] = b1;
            adj[b1 * d + find_idx(b1, a1)] = a2;
            adj[b2 * d + find_idx(b2, a2)] = a1;
        } else {
            int a = A[irand(nA)], b = B[irand(nB)];
            if (is_adj(a, b)) continue;
            if (deg[a] < d && deg[b] < d) {
                add_edge(a, b);
            } else if (deg[a] == d && deg[b] < d) {
                int c = adj[a * d + irand(deg[a])];
                remove_edge(a, c);
                add_edge(a, b);
            } else if (deg[b] == d && deg[a] < d) {
                int c = adj[b * d + irand(deg[b])];
                remove_edge(b, c);
                add_edge(a, b);
            } else {
                continue;
            }
        }

        long c2 = cost();
        long delta = c2 - cur;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            cur = c2;
        } else {
            memcpy(adj, adjS, sizeof(int) * (size_t)cap * d);
            memcpy(deg, degS, sizeof(int) * cap);
        }
    }

    if (bestN < 0) print_input();
    else print_graph(bestN, sAdj, sDeg);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Projective-plane arc extensions (diameter 3).
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
    """Old PG incidence plus a new A-vertex per point of S and a new B-vertex per line index in S."""
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
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
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
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Build: best structured start, then C growth search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        cands = _arc_extensions(d, t_start + 0.1 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Growth search in C, started from the best structured graph.
    elapsed = time.monotonic() - t_start
    budget = 0.8 * time_limit - elapsed - 1.0
    if budget >= 1.0 and best_n >= 2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 1.5)
            n2, e2 = lib.parse_graph_text(text)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
