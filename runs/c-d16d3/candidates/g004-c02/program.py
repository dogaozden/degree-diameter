"""Bipartite graphs with max degree d and diameter <= D.

Construction and search:
  * Arc-extended projective plane graphs (diameter 3, the parent's base).
  * For D = 3, a C edge-level annealing search starts from the best graph with
    two new isolated vertices (one per colour class). Moves are 2-switches,
    endpoint shifts and edge insertions between spare vertices. Cost is the
    number of vertex pairs at distance > D. Each time cost reaches 0, the graph
    is saved and one more vertex per side is appended.
  * For D >= 4, the GQ baseline and the parent's voltage-lift annealing.

Honest note: the arc-extension family is saturated. A covering of PG(2,13) by at
most 16 lines must contain a full pencil, so the extra vertices are capped near the
record 394. The C search edits edges directly and may return the start graph.
Every return path is checked with lib.is_valid and falls back to K_{d,d}.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

/* Edge-level annealing for bipartite graphs with max degree d and diameter <= D.
   Input: "n m" then m edges on stdin. Args: d D seed budget_seconds.
   Edges only join the two colour classes, so the graph stays bipartite.
   Cost = number of unordered vertex pairs at distance > D.
   Whenever cost is 0 the graph is saved and one vertex per class is appended. */

static int d_ = 1, D_ = 1;
static int n_ = 0, m_ = 0, ncap_ = 0, mcap_ = 0, W_ = 1, Wmax_ = 1;
static int *side_ = NULL, *deg_ = NULL, *adj_ = NULL;
static int *EA_ = NULL, *EB_ = NULL;
static int *sv0_ = NULL, *sv1_ = NULL;
static int n0_ = 0, n1_ = 0;
static uint64_t *bufA_ = NULL, *bufB_ = NULL;
static int *bestEA_ = NULL, *bestEB_ = NULL;
static int bestm_ = 0, bestn_ = 0;
static uint64_t rs_ = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs_ ^= rs_ << 13;
    rs_ ^= rs_ >> 7;
    rs_ ^= rs_ << 17;
    return rs_;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    const int *p = adj_ + (size_t)a * d_;
    for (int k = 0; k < deg_[a]; k++)
        if (p[k] == b) return 1;
    return 0;
}

static void adj_remove(int v, int u) {
    int *p = adj_ + (size_t)v * d_;
    for (int k = 0; k < deg_[v]; k++) {
        if (p[k] == u) {
            p[k] = p[deg_[v] - 1];
            deg_[v]--;
            return;
        }
    }
}

static void adj_add(int v, int u) {
    adj_[(size_t)v * d_ + deg_[v]] = u;
    deg_[v]++;
}

static void add_pair(int a, int b) { adj_add(a, b); adj_add(b, a); }
static void remove_pair(int a, int b) { adj_remove(a, b); adj_remove(b, a); }

static void rebuild_lists(void) {
    n0_ = n1_ = 0;
    for (int v = 0; v < n_; v++) {
        if (side_[v] == 0) sv0_[n0_++] = v;
        else sv1_[n1_++] = v;
    }
    W_ = (n_ + 63) / 64;
}

static int pick_spare(const int *list, int cnt) {
    if (cnt <= 0) return -1;
    for (int t = 0; t < 40; t++) {
        int v = list[rndint(cnt)];
        if (deg_[v] < d_) return v;
    }
    return -1;
}

static long cost_full(void) {
    int n = n_, W = W_, S = d_;
    uint64_t *cur = bufA_, *nxt = bufB_, *t;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++)
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int step = 0; step < D_; step++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            const int *p = adj_ + (size_t)v * S;
            for (int w = 0; w < W; w++) o[w] = c[w];
            for (int k = 0; k < deg_[v]; k++) {
                const uint64_t *c2 = cur + (size_t)p[k] * W;
                for (int w = 0; w < W; w++) o[w] |= c2[w];
            }
        }
        t = cur; cur = nxt; nxt = t;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *c = cur + (size_t)v * W;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc(c[w]);
        bad += n - pc;
    }
    return bad / 2;
}

static void save_best(void) {
    bestn_ = n_;
    bestm_ = m_;
    memcpy(bestEA_, EA_, sizeof(int) * (size_t)m_);
    memcpy(bestEB_, EB_, sizeof(int) * (size_t)m_);
}

static int grow_pair(void) {
    if (n_ + 2 > ncap_) return 0;
    side_[n_] = 0; deg_[n_] = 0; n_++;
    side_[n_] = 1; deg_[n_] = 0; n_++;
    rebuild_lists();
    return 1;
}

static int accept(long delta, double T) {
    if (delta <= 0) return 1;
    return rnd01() < exp(-(double)delta / T);
}

static int color_graph(int n, int m, const int *A, const int *B, int *col) {
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int v = 0; v < n; v++) {
        if (col[v] >= 0) continue;
        col[v] = 0;
        int changed = 1;
        while (changed) {
            changed = 0;
            for (int i = 0; i < m; i++) {
                int a = A[i], b = B[i];
                if (col[a] >= 0 && col[b] < 0) { col[b] = 1 - col[a]; changed = 1; }
                else if (col[b] >= 0 && col[a] < 0) { col[a] = 1 - col[b]; changed = 1; }
                else if (col[a] >= 0 && col[a] == col[b]) return 0;
            }
        }
    }
    return 1;
}

static void print_graph(int n, int m, const int *A, const int *B) {
    printf("%d %d\n", n, m);
    for (int i = 0; i < m; i++) printf("%d %d\n", A[i], B[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    {
        uint64_t sd = (uint64_t)strtoull(argv[3], NULL, 10);
        rs_ = sd * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
        if (rs_ == 0) rs_ = 88172645463325252ULL;
    }
    double budget = atof(argv[4]);
    int n_in = 0, m_in = 0;
    if (scanf("%d %d", &n_in, &m_in) != 2 || n_in < 1 || m_in < 0 || d_ < 1 || D_ < 1) {
        printf("0 0\n");
        return 0;
    }
    int *RA = malloc(sizeof(int) * (size_t)(m_in + 1));
    int *RB = malloc(sizeof(int) * (size_t)(m_in + 1));
    int *col = malloc(sizeof(int) * (size_t)n_in);
    int *indeg = calloc((size_t)n_in, sizeof(int));
    if (!RA || !RB || !col || !indeg) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m_in; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n_in || v >= n_in || u == v) {
            printf("0 0\n");
            return 0;
        }
        RA[i] = u;
        RB[i] = v;
        indeg[u]++;
        indeg[v]++;
    }
    int degok = 1;
    for (int v = 0; v < n_in; v++)
        if (indeg[v] > d_) degok = 0;
    if (!degok || !color_graph(n_in, m_in, RA, RB, col)) {
        print_graph(n_in, m_in, RA, RB);
        return 0;
    }

    ncap_ = n_in + 256;
    Wmax_ = (ncap_ + 63) / 64;
    mcap_ = ncap_ * d_ + 16;
    side_ = calloc((size_t)ncap_, sizeof(int));
    deg_ = calloc((size_t)ncap_, sizeof(int));
    adj_ = calloc((size_t)ncap_ * (size_t)d_, sizeof(int));
    sv0_ = calloc((size_t)ncap_, sizeof(int));
    sv1_ = calloc((size_t)ncap_, sizeof(int));
    EA_ = calloc((size_t)mcap_, sizeof(int));
    EB_ = calloc((size_t)mcap_, sizeof(int));
    bestEA_ = calloc((size_t)mcap_, sizeof(int));
    bestEB_ = calloc((size_t)mcap_, sizeof(int));
    bufA_ = calloc((size_t)ncap_ * (size_t)Wmax_, sizeof(uint64_t));
    bufB_ = calloc((size_t)ncap_ * (size_t)Wmax_, sizeof(uint64_t));
    if (!side_ || !deg_ || !adj_ || !sv0_ || !sv1_ || !EA_ || !EB_ ||
        !bestEA_ || !bestEB_ || !bufA_ || !bufB_) {
        print_graph(n_in, m_in, RA, RB);
        return 0;
    }

    for (int v = 0; v < n_in; v++) side_[v] = col[v];
    n_ = n_in;
    for (int i = 0; i < m_in; i++) {
        int a = RA[i], b = RB[i];
        if (col[a] == 0) { EA_[i] = a; EB_[i] = b; }
        else { EA_[i] = b; EB_[i] = a; }
        add_pair(a, b);
    }
    m_ = m_in;
    rebuild_lists();
    save_best();

    clock_t t_start = clock();
    long cur = cost_full();
    while (1) {
        if (cur == 0) {
            save_best();
            if (!grow_pair()) break;
            cur = cost_full();
            continue;
        }
        double frac = (double)(clock() - t_start) / ((double)CLOCKS_PER_SEC * budget);
        if (frac >= 1.0) break;
        double T = 1.2 * (1.0 - frac) * (1.0 - frac) + 0.05;
        double r = rnd01();
        long nc = 0;

        if (r < 0.4) {
            /* 2-switch: (a,b),(c,e) -> (a,e),(c,b) */
            if (m_ < 2) continue;
            int i = rndint(m_), j = rndint(m_);
            if (i == j) continue;
            int a = EA_[i], b = EB_[i], c = EA_[j], e = EB_[j];
            if (a == c || b == e) continue;
            if (has_edge(a, e) || has_edge(c, b)) continue;
            remove_pair(a, b);
            remove_pair(c, e);
            add_pair(a, e);
            add_pair(c, b);
            EB_[i] = e;
            EB_[j] = b;
            nc = cost_full();
            if (accept(nc - cur, T)) cur = nc;
            else {
                remove_pair(a, e);
                remove_pair(c, b);
                add_pair(a, b);
                add_pair(c, e);
                EB_[i] = b;
                EB_[j] = e;
            }
        } else if (r < 0.6) {
            /* shift the side-0 endpoint of edge i to a spare vertex x */
            if (m_ < 1) continue;
            int i = rndint(m_);
            int a = EA_[i], b = EB_[i];
            int x = pick_spare(sv0_, n0_);
            if (x < 0 || x == a || has_edge(x, b)) continue;
            remove_pair(a, b);
            add_pair(x, b);
            EA_[i] = x;
            nc = cost_full();
            if (accept(nc - cur, T)) cur = nc;
            else {
                remove_pair(x, b);
                add_pair(a, b);
                EA_[i] = a;
            }
        } else if (r < 0.8) {
            /* shift the side-1 endpoint of edge i to a spare vertex y */
            if (m_ < 1) continue;
            int i = rndint(m_);
            int a = EA_[i], b = EB_[i];
            int y = pick_spare(sv1_, n1_);
            if (y < 0 || y == b || has_edge(a, y)) continue;
            remove_pair(a, b);
            add_pair(a, y);
            EB_[i] = y;
            nc = cost_full();
            if (accept(nc - cur, T)) cur = nc;
            else {
                remove_pair(a, y);
                add_pair(a, b);
                EB_[i] = b;
            }
        } else {
            /* insert an edge between two spare vertices (never increases cost) */
            int x = pick_spare(sv0_, n0_);
            int y = pick_spare(sv1_, n1_);
            if (x < 0 || y < 0 || has_edge(x, y) || m_ >= mcap_) continue;
            add_pair(x, y);
            EA_[m_] = x;
            EB_[m_] = y;
            m_++;
            cur = cost_full();
        }
    }
    print_graph(bestn_, bestm_, bestEA_, bestEB_);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


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
    """PG incidence plus a new A-vertex per element of S (joined to its pencil) and a new B-vertex per element (joined to its line)."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        for L in point_lines[P]:
            E.append((2 * m + t, m + L))
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
        m, edges, point_lines, line_points, index = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# C edge search for D = 3.
# ----------------------------------------------------------------------------

def _c_search(d, D, start, time_limit, t0, seed):
    """Run the C annealer from `start`; return (n, edges) or None. Stays inside the time limit."""
    used = time.monotonic() - t0
    timeout = time_limit - used - 2.0
    budget = min(0.75 * time_limit - used, timeout - 2.0)
    if budget < 0.5:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=start, timeout=timeout)
        return lib.parse_graph_text(out)
    except Exception:
        return None


# ----------------------------------------------------------------------------
# Baselines and search for D >= 4 (parent code).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


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
# Entry point.
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
    bound = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.2 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

    # Calibration cases already at the Moore bound return immediately.
    if best_n < bound:
        if D == 3:
            res = _c_search(d, D, best, time_limit, t0, seed)
            if res is not None:
                consider(res[0], res[1])
        else:
            rng = random.Random(seed)
            deadline = t0 + 0.7 * time_limit
            if D >= 4 and time.monotonic() < deadline:
                gq = _best_gq(d)
                if gq is not None:
                    consider(gq[0], gq[1])
            ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
            while time.monotonic() < deadline and best_n < bound:
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
