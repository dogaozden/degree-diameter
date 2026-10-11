import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bipartite graphs with vertex insertion.
#
# The state is a bipartite graph with max degree d. The cost is the number of
# ordered vertex pairs at distance > D (bitset balls). Moves are double-edge
# swaps and endpoint moves, which keep bipartiteness and degree bounds. When the
# cost reaches 0, a vertex is inserted with a greedy ball-cover choice. After a
# long stall the search rolls back to the best valid graph and inserts again.
# The best valid graph is always printed, so the output is never worse than the input.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXN 2048
#define MAXD 64
#define MAXW 40

static int d, D, nmax, W, n, n0;
static int deg_[MAXN];
static int adj_[MAXN * MAXD];
static int side_[MAXN];
static int best_deg[MAXN];
static int best_adj[MAXN * MAXD];
static int best_side[MAXN];
static int best_n = -1;
static u64 *bufA, *bufB;
static u64 rs = 88172645463325252ULL;

typedef struct {
    int nr, na;
    int ra[2], rb[2], aa[2], ab[2];
} Move;

static u64 rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int m) { return (int)(rnd() % (u64)m); }
static double rndf(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int has_edge(int a, int b) {
    int k;
    for (k = 0; k < deg_[a]; k++) if (adj_[a * MAXD + k] == b) return 1;
    return 0;
}
static void del_arc(int a, int b) {
    int k;
    for (k = 0; k < deg_[a]; k++) {
        if (adj_[a * MAXD + k] == b) {
            adj_[a * MAXD + k] = adj_[a * MAXD + deg_[a] - 1];
            deg_[a]--;
            return;
        }
    }
}
static void add_arc(int a, int b) { adj_[a * MAXD + deg_[a]] = b; deg_[a]++; }
static void remove_edge(int a, int b) { del_arc(a, b); del_arc(b, a); }
static void add_edge(int a, int b) { add_arc(a, b); add_arc(b, a); }

static u64 *compute_balls(int R) {
    u64 *cur = bufA, *nxt = bufB, *t;
    int v, k, w, it;
    memset(cur, 0, sizeof(u64) * (size_t)n * W);
    for (v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (it = 0; it < R; it++) {
        for (v = 0; v < n; v++) {
            u64 *o = nxt + (size_t)v * W;
            const u64 *c = cur + (size_t)v * W;
            for (w = 0; w < W; w++) o[w] = c[w];
            for (k = 0; k < deg_[v]; k++) {
                const u64 *cu = cur + (size_t)adj_[v * MAXD + k] * W;
                for (w = 0; w < W; w++) o[w] |= cu[w];
            }
        }
        t = cur; cur = nxt; nxt = t;
    }
    return cur;
}

static long long cost_eval(void) {
    u64 *b = compute_balls(D);
    long long cov = 0;
    int i, lim = n * W;
    for (i = 0; i < lim; i++) cov += __builtin_popcountll(b[i]);
    return (long long)n * n - cov;
}

static void insert_vertex(int s) {
    int w = n, v, k, i, nch = 0, chosen[MAXD];
    int best, bestg, ties, g, used;
    u64 cov[MAXW];
    u64 *B = compute_balls(D - 1);
    for (i = 0; i < W; i++) cov[i] = 0;
    while (nch < d) {
        best = -1; bestg = 0; ties = 0;
        for (v = 0; v < n; v++) {
            if (side_[v] == s || deg_[v] >= d) continue;
            used = 0;
            for (k = 0; k < nch; k++) if (chosen[k] == v) { used = 1; break; }
            if (used) continue;
            g = 0;
            {
                const u64 *bv = B + (size_t)v * W;
                for (i = 0; i < W; i++) g += __builtin_popcountll(bv[i] & ~cov[i]);
            }
            if (g > bestg) { bestg = g; best = v; ties = 1; }
            else if (g == bestg && g > 0) {
                ties++;
                if (rndi(ties) == 0) best = v;
            }
        }
        if (best < 0) break;
        chosen[nch++] = best;
        for (i = 0; i < W; i++) cov[i] |= B[(size_t)best * W + i];
    }
    side_[w] = s;
    deg_[w] = 0;
    n++;
    for (k = 0; k < nch; k++) add_edge(chosen[k], w);
}

static void snapshot(void) {
    memcpy(best_deg, deg_, sizeof(deg_));
    memcpy(best_adj, adj_, sizeof(adj_));
    memcpy(best_side, side_, sizeof(side_));
    best_n = n;
}
static void restore(void) {
    memcpy(deg_, best_deg, sizeof(deg_));
    memcpy(adj_, best_adj, sizeof(adj_));
    memcpy(side_, best_side, sizeof(side_));
    n = best_n;
}

static int propose(Move *mv) {
    int tries, a, b, c, e, y;
    mv->nr = 0; mv->na = 0;
    if (rndi(100) < 50) {
        for (tries = 0; tries < 30; tries++) {
            a = rndi(n);
            if (side_[a] != 0 || deg_[a] == 0) continue;
            b = adj_[a * MAXD + rndi(deg_[a])];
            c = rndi(n);
            if (side_[c] != 0 || deg_[c] == 0) continue;
            e = adj_[c * MAXD + rndi(deg_[c])];
            if (c == a) continue;
            if (has_edge(a, e) || has_edge(c, b)) continue;
            mv->nr = 2;
            mv->ra[0] = a; mv->rb[0] = b;
            mv->ra[1] = c; mv->rb[1] = e;
            mv->na = 2;
            mv->aa[0] = a; mv->ab[0] = e;
            mv->aa[1] = c; mv->ab[1] = b;
            return 1;
        }
        return 0;
    }
    for (tries = 0; tries < 30; tries++) {
        a = rndi(n);
        if (deg_[a] == 0) continue;
        b = adj_[a * MAXD + rndi(deg_[a])];
        y = rndi(n);
        if (y == b || side_[y] != side_[b] || deg_[y] >= d || has_edge(a, y)) continue;
        mv->nr = 1; mv->ra[0] = a; mv->rb[0] = b;
        mv->na = 1; mv->aa[0] = a; mv->ab[0] = y;
        return 1;
    }
    return 0;
}

static void apply_move(const Move *mv) {
    int i;
    for (i = 0; i < mv->nr; i++) remove_edge(mv->ra[i], mv->rb[i]);
    for (i = 0; i < mv->na; i++) add_edge(mv->aa[i], mv->ab[i]);
}
static void undo_move(const Move *mv) {
    int i;
    for (i = 0; i < mv->na; i++) remove_edge(mv->aa[i], mv->ab[i]);
    for (i = 0; i < mv->nr; i++) add_edge(mv->ra[i], mv->rb[i]);
}

int main(int argc, char **argv) {
    int m, i, u, v, k, s, x, y, qh, qt, bip;
    static int queue[MAXN];
    long budget;
    time_t t0;
    long long cost, c2, delta, step = 0, last_ins = 0, cnt;
    const double T0 = 2.0, Tend = 0.05;
    const long long CYC = 4000, ROLL = 30000;
    Move mv;

    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    budget = atol(argv[4]);

    if (scanf("%d %d", &n0, &m) != 2 || n0 < 1 || n0 > MAXN - 256 ||
        d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    n = n0;
    memset(deg_, 0, sizeof(deg_));
    for (i = 0; i < m; i++) {
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg_[u] >= d || deg_[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    for (i = 0; i < n; i++) side_[i] = -1;
    bip = 1;
    for (s = 0; s < n; s++) {
        if (side_[s] >= 0) continue;
        side_[s] = 0;
        qh = qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            x = queue[qh++];
            for (k = 0; k < deg_[x]; k++) {
                y = adj_[x * MAXD + k];
                if (side_[y] < 0) {
                    side_[y] = 1 - side_[x];
                    queue[qt++] = y;
                } else if (side_[y] == side_[x]) {
                    bip = 0;
                }
            }
        }
    }
    if (!bip) {
        printf("0 0\n");
        return 0;
    }

    nmax = n0 + 200;
    if (nmax > MAXN) nmax = MAXN;
    W = (nmax + 63) / 64;
    if (W > MAXW) W = MAXW;
    bufA = (u64 *)malloc(sizeof(u64) * (size_t)nmax * W);
    bufB = (u64 *)malloc(sizeof(u64) * (size_t)nmax * W);
    if (!bufA || !bufB) {
        printf("0 0\n");
        return 0;
    }

    snapshot();
    t0 = time(NULL);
    cost = cost_eval();
    if (cost == 0 && n > best_n) snapshot();

    while (1) {
        if ((step & 127) == 0 && (long)(time(NULL) - t0) >= budget) break;
        step++;
        if (cost == 0) {
            if (n > best_n) snapshot();
            if (n >= nmax) break;
            insert_vertex(rndi(2));
            cost = cost_eval();
            last_ins = step;
            continue;
        }
        if (step - last_ins > ROLL) {
            restore();
            if (n >= nmax) break;
            insert_vertex(rndi(2));
            cost = cost_eval();
            last_ins = step;
            continue;
        }
        {
            double ph = (double)((step - last_ins) % CYC) / (double)CYC;
            double T = T0 * pow(Tend / T0, ph);
            if (!propose(&mv)) continue;
            apply_move(&mv);
            c2 = cost_eval();
            delta = c2 - cost;
            if (delta <= 0 || rndf() < exp(-(double)delta / T)) cost = c2;
            else undo_move(&mv);
        }
    }

    restore();
    cnt = 0;
    for (v = 0; v < n; v++) cnt += deg_[v];
    cnt /= 2;
    printf("%d %lld\n", n, cnt);
    for (v = 0; v < n; v++) {
        for (k = 0; k < deg_[v]; k++) {
            u = adj_[v * MAXD + k];
            if (u > v) printf("%d %d\n", v, u);
        }
    }
    free(bufA);
    free(bufB);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions: arc-extended projective planes (D = 3) and W(q) (D = 4).
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
    """W(q) for the largest small prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


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
        arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < start + 0.15 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Bold change: the C annealer grows the best Python start by vertex insertion
    # and double-edge swaps, instead of group voltage lifts.
    elapsed = time.monotonic() - start
    budget = int(0.85 * time_limit - elapsed - 4)
    if budget >= 2:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, budget], stdin_graph=best,
                            timeout=budget + 30)
            n_c, e_c = lib.parse_graph_text(out)
            consider(n_c, e_c)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
