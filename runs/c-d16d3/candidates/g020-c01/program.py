import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing that grows a valid bipartite graph one vertex at
# a time. The state is always a graph with max degree <= d and sides fixed by
# 2-colouring. The cost is the number of unordered vertex pairs at distance > D.
# Moves: degree-preserving 2-switches, edge additions, edge removals. When the
# cost reaches zero the graph is recorded and a new vertex is attached to spare
# capacity on the opposite side. Stalled runs restart from the best graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static int DEG, DIA, N, CAP, W;
static int *side, *deg, *adj;
static int *bdeg, *badj, *bside, bestN = -1;
static int *sdeg, *sadj, *sside, snapN;
static u64 *bufA, *bufB;
static int *tmpv;
static u64 rs = 88172645463325252ULL;

static u64 rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int k) { return (int)(rnd() % (u64)k); }

static double rndd(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void fail_out(void) {
    printf("0 0\n");
    exit(0);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a * DEG + k] == b) return 1;
    return 0;
}

static void add_arc(int a, int b) {
    adj[a * DEG + deg[a]] = b;
    deg[a]++;
}

static void add_edge(int a, int b) {
    add_arc(a, b);
    add_arc(b, a);
}

static void del_arc(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adj[a * DEG + k] == b) {
            adj[a * DEG + k] = adj[a * DEG + deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void del_edge(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
}

/* Number of unordered pairs of current vertices at distance > DIA. */
static long long eval_bad(void) {
    u64 *cur = bufA, *nxt = bufB;
    size_t bytes = (size_t)W * sizeof(u64);
    memset(cur, 0, (size_t)CAP * bytes);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < DIA; t++) {
        for (int v = 0; v < N; v++) {
            u64 *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, bytes);
            for (int k = 0; k < deg[v]; k++) {
                const u64 *c = cur + (size_t)adj[v * DEG + k] * W;
                for (int w = 0; w < W; w++) o[w] |= c[w];
            }
        }
        u64 *tp = cur;
        cur = nxt;
        nxt = tp;
    }
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        int cnt = 0;
        const u64 *c = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) cnt += popc(c[w]);
        tot += N - cnt;
    }
    return tot / 2;
}

static void copy_out(int *dg, int *ad, int *sd) {
    memcpy(dg, deg, sizeof(int) * (size_t)CAP);
    memcpy(ad, adj, sizeof(int) * (size_t)CAP * DEG);
    memcpy(sd, side, sizeof(int) * (size_t)CAP);
}

static void copy_in(const int *dg, const int *ad, const int *sd) {
    memcpy(deg, dg, sizeof(int) * (size_t)CAP);
    memcpy(adj, ad, sizeof(int) * (size_t)CAP * DEG);
    memcpy(side, sd, sizeof(int) * (size_t)CAP);
}

static void save_best(void) {
    copy_out(bdeg, badj, bside);
    bestN = N;
}

static void restore_best(void) {
    copy_in(bdeg, badj, bside);
    N = bestN;
}

/* Add vertex N on one side, joined to up to DEG spare vertices of the other side. */
static int add_vertex(void) {
    if (N >= CAP) return 0;
    int spare[2] = {0, 0};
    for (int u = 0; u < N; u++)
        if (deg[u] < DEG) spare[side[u]]++;
    int opts[2], no = 0;
    for (int s = 0; s < 2; s++)
        if (spare[1 - s] > 0) opts[no++] = s;
    if (no == 0) return 0;
    int s = opts[rndi(no)];
    int m = 0;
    for (int u = 0; u < N; u++)
        if (side[u] == 1 - s && deg[u] < DEG) tmpv[m++] = u;
    for (int i = m - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = tmpv[i];
        tmpv[i] = tmpv[j];
        tmpv[j] = t;
    }
    int want = m < DEG ? m : DEG;
    int v = N;
    side[v] = s;
    deg[v] = 0;
    N++;
    for (int i = 0; i < want; i++) add_edge(v, tmpv[i]);
    return 1;
}

/* Degree-preserving 2-switch keeping the bipartition. */
static int move_2switch(void) {
    int x1 = rndi(N), x2 = rndi(N);
    if (deg[x1] == 0 || deg[x2] == 0) return 0;
    int y1 = adj[x1 * DEG + rndi(deg[x1])];
    int y2 = adj[x2 * DEG + rndi(deg[x2])];
    int a, b, c, e;
    if (side[x1] == 0) { a = x1; b = y1; } else { a = y1; b = x1; }
    if (side[x2] == 0) { c = x2; e = y2; } else { c = y2; e = x2; }
    if (a == c) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    return 1;
}

static int move_add(void) {
    int a = rndi(N), b = rndi(N);
    if (side[a] == side[b]) return 0;
    if (deg[a] >= DEG || deg[b] >= DEG) return 0;
    if (has_edge(a, b)) return 0;
    add_edge(a, b);
    return 1;
}

static int move_remove(void) {
    int x = rndi(N);
    if (deg[x] == 0) return 0;
    int y = adj[x * DEG + rndi(deg[x])];
    del_edge(x, y);
    return 1;
}

static double elapsed(clock_t t0) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

int main(int argc, char **argv) {
    clock_t t0 = clock();
    if (argc < 5) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIA = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { printf("0 0\n"); return 0; }
    if (DEG < 1 || DIA < 1 || n0 < 1 || n0 > 4000 || m0 < 0) { printf("0 0\n"); return 0; }

    /* Moore bound for bipartite graphs: 2 * sum_{i<DIA} (DEG-1)^i. */
    double ms = 0.0, p = 1.0;
    for (int i = 0; i < DIA; i++) {
        ms += p;
        p *= (double)(DEG - 1);
        if (ms > 1e6) break;
    }
    CAP = n0 + 200;
    if (2.0 * ms >= n0 && 2.0 * ms < CAP) CAP = (int)(2.0 * ms);
    if (CAP > 2048) CAP = 2048;
    if (CAP < n0) CAP = n0;

    W = (CAP + 63) / 64;
    side = calloc((size_t)CAP, sizeof(int));
    deg = calloc((size_t)CAP, sizeof(int));
    adj = calloc((size_t)CAP * DEG, sizeof(int));
    bdeg = calloc((size_t)CAP, sizeof(int));
    badj = calloc((size_t)CAP * DEG, sizeof(int));
    bside = calloc((size_t)CAP, sizeof(int));
    sdeg = calloc((size_t)CAP, sizeof(int));
    sadj = calloc((size_t)CAP * DEG, sizeof(int));
    sside = calloc((size_t)CAP, sizeof(int));
    tmpv = calloc((size_t)CAP, sizeof(int));
    bufA = calloc((size_t)CAP * W, sizeof(u64));
    bufB = calloc((size_t)CAP * W, sizeof(u64));
    if (!side || !deg || !adj || !bdeg || !badj || !bside || !sdeg || !sadj ||
        !sside || !tmpv || !bufA || !bufB) {
        printf("0 0\n");
        return 0;
    }

    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) fail_out();
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) fail_out();
        if (deg[u] >= DEG || deg[v] >= DEG || has_edge(u, v)) fail_out();
        add_edge(u, v);
    }

    /* 2-colour the start graph; reject if it is not bipartite. */
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s0 = 0; s0 < N; s0++) {
        if (side[s0] != -1) continue;
        side[s0] = 0;
        int h = 0, t = 0;
        tmpv[t++] = s0;
        while (h < t) {
            int u = tmpv[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u * DEG + k];
                if (side[v] == -1) {
                    side[v] = 1 - side[u];
                    tmpv[t++] = v;
                } else if (side[v] == side[u]) {
                    fail_out();
                }
            }
        }
    }

    long long cost = eval_bad();
    if (cost == 0 && N > bestN) save_best();

    long long it = 0, lastImp = 0;
    const long long STALL = 30000, CYC = 20000;

    while (1) {
        if ((it & 31) == 0 && elapsed(t0) >= budget) break;
        it++;

        if (cost == 0) {
            if (N > bestN) save_best();
            lastImp = it;
            if (N >= CAP) break;
            if (add_vertex()) {
                cost = eval_bad();
                continue;
            }
            if (move_remove()) cost = eval_bad();
            continue;
        }

        if (bestN >= 0 && it - lastImp > STALL) {
            restore_best();
            cost = eval_bad();
            lastImp = it;
            continue;
        }

        double T = 1.5 * pow(0.08 / 1.5, (double)(it % CYC) / (double)CYC);
        copy_out(sdeg, sadj, sside);
        snapN = N;
        double r = rndd();
        int ok;
        if (r < 0.6) ok = move_2switch();
        else if (r < 0.85) ok = move_add();
        else ok = move_remove();
        if (!ok) continue;

        long long c2 = eval_bad();
        long long delta = c2 - cost;
        if (delta <= 0 || rndd() < exp(-(double)delta / T)) {
            cost = c2;
        } else {
            copy_in(sdeg, sadj, sside);
            N = snapN;
        }
    }

    if (bestN < 0) { printf("0 0\n"); return 0; }
    long long M = 0;
    for (int v = 0; v < bestN; v++) M += bdeg[v];
    M /= 2;
    printf("%d %lld\n", bestN, M);
    for (int v = 0; v < bestN; v++)
        for (int k = 0; k < bdeg[v]; k++) {
            int u = badj[v * DEG + k];
            if (u > v) printf("%d %d\n", v, u);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Projective-plane arc extensions (diameter 3).
#
# Start from the incidence graph of PG(2, q). Choose a point set S (indexed
# also as lines by polarity) with every line holding <= s points of S and every
# point on <= s lines indexed by S, where s = d - q - 1. Add an A-vertex for
# each P in S (joined to the lines through P) and a B-vertex for each line j in
# S (joined to the points on j).
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
# Build: best construction first, then the C annealer grows from it.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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
        for n_c, e_c in _arc_extensions(d, t0 + 0.15 * time_limit, random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Stop early if the Moore bound is already met.
    if best_n >= lib.moore_bound(d, D):
        return best

    remaining = time_limit - (time.monotonic() - t0)
    if remaining > 6:
        budget = remaining * 0.85 - 2.0
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=remaining - 2.0)
            n_c, e_c = lib.parse_graph_text(out)
            consider(n_c, e_c)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
