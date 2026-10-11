import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: vertex-insertion annealing on a bipartite graph.
#
# Input: a valid bipartite graph with max degree <= d and diameter <= D.
# Move: add a new vertex x on one side, joined to up to d opposite-side
#       vertices that still have spare degree. Adding x never increases any
#       existing distance, so the only condition is that x reaches every old
#       vertex within D. Simulated annealing swaps neighbours of x to drive the
#       number of unreached old vertices to zero. Bitset balls keep each cost
#       evaluation cheap.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1536
#define W 24
#define MAXE 60000

static uint64_t AB[MAXN][W];
static int deg_[MAXN];
static int col_[MAXN];
static int EU[MAXE], EV[MAXE];
static int ne_ = 0;
static int n_ = 0;
static int d_ = 3, D_ = 3;
static uint64_t rs_ = 88172645463325252ULL;
static int S_[MAXN];
static int Ncur[MAXN];
static char inN_[MAXN];

static uint64_t rnd64(void) {
    rs_ ^= rs_ << 13;
    rs_ ^= rs_ >> 7;
    rs_ ^= rs_ << 17;
    return rs_;
}

static int rndint(int k) {
    return (int)(rnd64() % (uint64_t)k);
}

static double rnd01(void) {
    return (double)(rnd64() >> 11) / 9007199254740992.0;
}

static int hasb(int u, int v) {
    return (int)((AB[u][v >> 6] >> (v & 63)) & 1ULL);
}

static void setb2(int u, int v) {
    AB[u][v >> 6] |= 1ULL << (v & 63);
    AB[v][u >> 6] |= 1ULL << (u & 63);
}

/* Number of old vertices (indices < nold) NOT within distance D_ of a new
   vertex x whose neighbours are the k vertices in N. */
static int cost_of(const int *N, int k, int nold) {
    uint64_t ball[W], ring[W], nb[W];
    int nwords = (nold + 63) >> 6;
    int i, t, w, step;
    memset(ball, 0, sizeof ball);
    memset(ring, 0, sizeof ring);
    for (i = 0; i < k; i++) {
        ring[N[i] >> 6] |= 1ULL << (N[i] & 63);
    }
    for (t = 0; t < nwords; t++) ball[t] = ring[t];
    for (step = 1; step < D_; step++) {
        int any = 0;
        memset(nb, 0, sizeof nb);
        for (w = 0; w < nwords; w++) {
            uint64_t x = ring[w];
            while (x) {
                int b = __builtin_ctzll(x);
                int v;
                x &= x - 1;
                v = (w << 6) + b;
                for (t = 0; t < nwords; t++) nb[t] |= AB[v][t];
            }
        }
        for (t = 0; t < nwords; t++) {
            ring[t] = nb[t] & ~ball[t];
            ball[t] |= nb[t];
            if (ring[t]) any = 1;
        }
        if (!any) break;
    }
    {
        int cnt = 0;
        for (t = 0; t < nwords; t++) cnt += __builtin_popcountll(ball[t]);
        return nold - cnt;
    }
}

static int try_add(int nold, int c, int iters, double T0) {
    int ns = 0, v, i, k, cnt = 0, bestp = -1, bestsc = -1, tr, cur, it;
    for (v = 0; v < nold; v++) {
        if (col_[v] != c && deg_[v] < d_) S_[ns++] = v;
    }
    if (ns == 0) return 0;
    k = ns < d_ ? ns : d_;
    if (k <= 0) return 0;

    /* Start from the neighbourhood of a clone-like vertex of colour c. */
    for (tr = 0; tr < 20; tr++) {
        int p = rndint(nold), sc = 0;
        if (col_[p] != c) continue;
        for (v = 0; v < nold; v++) {
            if (hasb(p, v) && col_[v] != c && deg_[v] < d_) sc++;
        }
        if (sc > bestsc) {
            bestsc = sc;
            bestp = p;
        }
    }
    if (bestp >= 0) {
        for (v = 0; v < nold && cnt < k; v++) {
            if (hasb(bestp, v) && col_[v] != c && deg_[v] < d_) {
                Ncur[cnt++] = v;
                inN_[v] = 1;
            }
        }
    }
    while (cnt < k) {
        int w = S_[rndint(ns)];
        if (!inN_[w]) {
            Ncur[cnt++] = w;
            inN_[w] = 1;
        }
    }

    cur = cost_of(Ncur, k, nold);
    for (it = 0; it < iters && cur > 0; it++) {
        double T = T0 * (1.0 - (double)it / (double)iters) + 0.02;
        int idx = rndint(k);
        int w = S_[rndint(ns)];
        int old, c2, delta;
        if (inN_[w]) continue;
        old = Ncur[idx];
        Ncur[idx] = w;
        inN_[old] = 0;
        inN_[w] = 1;
        c2 = cost_of(Ncur, k, nold);
        delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = c2;
        } else {
            Ncur[idx] = old;
            inN_[w] = 0;
            inN_[old] = 1;
        }
    }

    if (cur == 0) {
        int x = nold;
        for (i = 0; i < k; i++) {
            int u = Ncur[i];
            setb2(x, u);
            deg_[u]++;
            if (ne_ < MAXE) {
                EU[ne_] = u;
                EV[ne_] = x;
                ne_++;
            }
        }
        deg_[x] = k;
        col_[x] = c;
        n_ = nold + 1;
        for (i = 0; i < k; i++) inN_[Ncur[i]] = 0;
        return 1;
    }
    for (i = 0; i < k; i++) inN_[Ncur[i]] = 0;
    return 0;
}

int main(int argc, char **argv) {
    int n, m, i;
    double budget;
    unsigned long long seed;
    clock_t t0;
    long fails = 0;

    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    seed = strtoull(argv[3], NULL, 10);
    budget = atof(argv[4]);
    rs_ = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs_ == 0) rs_ = 1;

    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n >= MAXN - 2 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    n_ = n;
    for (i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (hasb(u, v)) continue;
        setb2(u, v);
        deg_[u]++;
        deg_[v]++;
        if (ne_ < MAXE) {
            EU[ne_] = u;
            EV[ne_] = v;
            ne_++;
        }
    }

    /* Bipartition by BFS. */
    for (i = 0; i < n; i++) col_[i] = -1;
    {
        static int q[MAXN];
        int s;
        for (s = 0; s < n; s++) {
            int qh = 0, qt = 0;
            if (col_[s] != -1) continue;
            col_[s] = 0;
            q[qt++] = s;
            while (qh < qt) {
                int u = q[qh++];
                int w;
                for (w = 0; w < n; w++) {
                    if (hasb(u, w) && col_[w] == -1) {
                        col_[w] = 1 - col_[u];
                        q[qt++] = w;
                    }
                }
            }
        }
    }

    if (D_ >= 3 && d_ >= 1) {
        t0 = clock();
        while (1) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            int c;
            if (el >= budget) break;
            if (n_ >= MAXN - 2) break;
            if (ne_ >= MAXE - d_ - 4) break;
            c = rndint(2);
            if (try_add(n_, c, 500, 1.0)) {
                fails = 0;
            } else {
                fails++;
            }
            if (fails > 200000) break;
        }
    }

    printf("%d %d\n", n_, ne_);
    for (i = 0; i < ne_; i++) {
        printf("%d %d\n", EU[i], EV[i]);
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions used as starting graphs.
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


def _loads_ok(S, s, m, nbr):
    """True if every target t is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice of elements so that every target is hit by <= s of them."""
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
    """Yield (n, edges) arc-extended projective plane candidates (diameter 3)."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
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

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
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

    def consider(cand):
        nonlocal best, best_n
        try:
            n, e = cand
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    # Starting graphs from algebra: arc-extended projective planes (D >= 3)
    # and generalized quadrangles (D >= 4).
    starts = []
    if D >= 3:
        starts.extend(_arc_extensions(d, t0 + 0.12 * time_limit,
                                      random.Random(seed * 7919 + d)))
    if D >= 4 and time.monotonic() < t0 + 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    starts.sort(key=lambda t: -t[0])
    for cand in starts:
        consider(cand)

    # Bold step: C vertex-insertion annealing grows the best valid start.
    # The result is validated before use, so any C failure keeps the fallback.
    remaining = t0 + 0.85 * time_limit - time.monotonic() - 3.0
    to = t0 + 0.94 * time_limit - time.monotonic()
    if remaining > 2.0 and to > 3.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                            stdin_graph=best, timeout=to)
            n2, e2 = lib.parse_graph_text(out)
            consider((n2, e2))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
