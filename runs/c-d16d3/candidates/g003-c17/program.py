"""Diameter-3 bipartite search with two constructions.

Construction A (parent): arc-extended projective plane starts, plus a C augmentation engine
that adds vertices whose neighbourhoods cover every existing vertex within distance D-1.
Each start is valid, and adding vertices never increases existing distances.

Construction B (new, D = 3 only): Haar graphs of abelian groups G = Z_m1 x Z_m2. Given a
k-subset S of G with S - S = G, the graph with parts G and G', where a_x ~ b_y iff y - x in S,
has degree k and diameter 3. Same-side pairs are at distance 2 because S - S = G. Opposite-side
pairs are at distance 1 or 3 because S - S + s0 = G for any fixed s0 in S. The C engine searches
for such S by simulated annealing on the number of uncovered differences, for increasing |G|.
The theoretical ceiling is 2(k^2 - k + 1).

build() runs construction A first as a safe fallback, then construction B with the remaining
time. The larger valid result is returned. Everything is checked with lib.is_valid.
"""
import itertools
import random
import time

import lib

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 2048
#define WORDS (MAXN / 64)
#define MAXDEG 64

static int N, Dd, Dist, W;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static uint64_t ball[MAXN][WORDS];
static int mark[MAXN], lev[MAXN], bq[MAXN];
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Bitset of all vertices within distance r of src. */
static void ball_of(int src, int r, uint64_t *bits) {
    int head = 0, t = 0;
    stamp++;
    for (int i = 0; i < W; i++) bits[i] = 0;
    bq[t++] = src;
    mark[src] = stamp;
    lev[src] = 0;
    while (head < t) {
        int u = bq[head++];
        bits[u >> 6] |= 1ULL << (u & 63);
        if (lev[u] >= r) continue;
        for (int k = 0; k < deg[u]; k++) {
            int v = adj[u][k];
            if (mark[v] != stamp) {
                mark[v] = stamp;
                lev[v] = lev[u] + 1;
                bq[t++] = v;
            }
        }
    }
}

static void recompute_balls(void) {
    for (int v = 0; v < N; v++) ball_of(v, Dist - 1, ball[v]);
}

/* Try to add one new vertex on side X. Returns 1 if the graph grew. */
static int try_add(int X) {
    uint64_t U[WORDS];
    int sel[MAXN];
    int T[MAXDEG];
    int nt = 0;
    if (N + 1 >= MAXN) return 0;
    for (int i = 0; i < W; i++) U[i] = ~0ULL;
    if (N & 63) U[W - 1] = (1ULL << (N & 63)) - 1ULL;
    memset(sel, 0, sizeof(sel));
    while (nt < Dd) {
        int best = -1;
        long bestsc = -1;
        for (int v = 0; v < N; v++) {
            if (side[v] == X || deg[v] >= Dd || sel[v]) continue;
            int g = 0;
            for (int i = 0; i < W; i++) g += popc(ball[v][i] & U[i]);
            if (g <= 0) continue;
            long sc = (long)g * 8 + rndint(8);
            if (sc > bestsc) {
                bestsc = sc;
                best = v;
            }
        }
        if (best < 0) break;
        sel[best] = 1;
        T[nt++] = best;
        for (int i = 0; i < W; i++) U[i] &= ~ball[best][i];
    }
    for (int i = 0; i < W; i++)
        if (U[i]) return 0;
    if (nt == 0) return 0;
    int x = N;
    side[x] = X;
    deg[x] = nt;
    for (int k = 0; k < nt; k++) {
        int t = T[k];
        adj[x][k] = t;
        adj[t][deg[t]++] = x;
    }
    N++;
    W = (N + 63) / 64;
    recompute_balls();
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    if (Dd > MAXDEG) Dd = MAXDEG;
    Dist = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 2 || Dist < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= MAXDEG || deg[v] >= MAXDEG) continue;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }

    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, t = 0;
        bq[t++] = s;
        while (head < t) {
            int u = bq[head++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    bq[t++] = v;
                }
            }
        }
    }

    W = (N + 63) / 64;
    recompute_balls();

    double t_end = elapsed() + budget;
    int fails = 0;
    while (elapsed() < t_end && N < MAXN - 2 && fails < 4000) {
        int X = rndint(2);
        if (try_add(X)) fails = 0;
        else fails++;
    }

    int M = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) M++;
    printf("%d %d\n", N, M);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) printf("%d %d\n", v, adj[v][k]);
    return 0;
}
"""

HAAR_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 512
#define MAXK 64

static int K, NG, M1, M2;
static int DIFF[MAXG][MAXG];
static int ADD[MAXG][MAXG];
static int S[MAXK];
static int cnt[MAXG];
static int cost;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double unif(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

/* Group Z_m1 x Z_m2 (m2 divides m1), element a*m2 + b. */
static void setup_group(int m1, int m2) {
    M1 = m1;
    M2 = m2;
    NG = m1 * m2;
    for (int x = 0; x < NG; x++) {
        int a1 = x / m2, b1 = x % m2;
        for (int y = 0; y < NG; y++) {
            int a2 = y / m2, b2 = y % m2;
            DIFF[x][y] = ((a1 - a2 + m1) % m1) * m2 + ((b1 - b2 + m2) % m2);
            ADD[x][y] = ((a1 + a2) % m1) * m2 + ((b1 + b2) % m2);
        }
    }
}

static inline void dec_c(int g) {
    if (--cnt[g] == 0) cost++;
}

static inline void inc_c(int g) {
    if (cnt[g]++ == 0) cost--;
}

/* Add (sgn > 0) or remove (sgn < 0) the differences between v and every other S[j], j != i. */
static void upd(int i, int v, int sgn) {
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        int g1 = DIFF[v][S[j]], g2 = DIFF[S[j]][v];
        if (sgn > 0) {
            inc_c(g1);
            inc_c(g2);
        } else {
            dec_c(g1);
            dec_c(g2);
        }
    }
}

static int in_S(int x, int upto) {
    for (int j = 0; j < upto; j++)
        if (S[j] == x) return 1;
    return 0;
}

/* Simulated annealing for a K-subset S with all nonzero differences covered. */
static int anneal(int iters) {
    memset(cnt, 0, sizeof(int) * (size_t)NG);
    cost = NG - 1;
    for (int i = 0; i < K; i++) {
        int x;
        do {
            x = rndint(NG);
        } while (in_S(x, i));
        S[i] = x;
    }
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            if (i != j) inc_c(DIFF[S[i]][S[j]]);
    if (cost == 0) return 1;

    double T = 1.0, T1 = 0.05;
    double alpha = pow(T1, 1.0 / (double)iters);
    for (int it = 0; it < iters; it++, T *= alpha) {
        int i = rndint(K);
        int old = S[i], x;
        do {
            x = rndint(NG);
        } while (in_S(x, K));
        int c0 = cost;
        upd(i, old, -1);
        S[i] = x;
        upd(i, x, +1);
        int delta = cost - c0;
        if (delta <= 0 || unif() < exp(-(double)delta / T)) {
            if (cost == 0) return 1;
        } else {
            upd(i, x, -1);
            S[i] = old;
            upd(i, old, +1);
        }
    }
    return 0;
}

static void output_graph(int N, int m1, int m2, const int *Sol, int k) {
    setup_group(m1, m2);
    printf("%d %d\n", 2 * N, N * k);
    for (int x = 0; x < N; x++)
        for (int j = 0; j < k; j++)
            printf("%d %d\n", x, N + ADD[x][Sol[j]]);
}

int main(int argc, char **argv) {
    if (argc < 4) return 1;
    K = atoi(argv[1]);
    if (K < 2 || K > MAXK) {
        printf("0 0\n");
        return 0;
    }
    unsigned long seed = strtoul(argv[2], NULL, 10);
    double budget = atof(argv[3]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;

    double t_end = elapsed() + budget;
    int Nmax = K * (K - 1) + 1;
    if (Nmax > MAXG - 1) Nmax = MAXG - 1;

    int bestN = 0, bm1 = 0, bm2 = 0;
    int bestS[MAXK];

    for (int N = K + 1; N <= Nmax && elapsed() < t_end; N++) {
        int gm1[64], gm2[64], ng = 0;
        for (int m2 = 1; m2 <= N; m2++) {
            if (N % m2) continue;
            int m1 = N / m2;
            if (m1 % m2) continue;
            if (ng < 64) {
                gm1[ng] = m1;
                gm2[ng] = m2;
                ng++;
            }
        }
        if (ng == 0) continue;

        double dl = elapsed() + fmax(0.5, (t_end - elapsed()) * 0.4);
        if (dl > t_end) dl = t_end;
        int iters = 400 * N;
        int found = 0;
        while (!found && elapsed() < dl) {
            for (int g = 0; g < ng && !found; g++) {
                setup_group(gm1[g], gm2[g]);
                if (anneal(iters)) {
                    found = 1;
                    bm1 = gm1[g];
                    bm2 = gm2[g];
                    bestN = N;
                    memcpy(bestS, S, sizeof(int) * (size_t)K);
                }
            }
        }
        if (!found) break;
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    output_graph(bestN, bm1, bm2, bestS, K);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Construction A (parent): arc-extended projective plane incidence graphs.
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
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4), used for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
# C augmentation driver (construction A).
# ----------------------------------------------------------------------------

def _augment(n0, e0, d, D, seed, budget, timeout):
    """Run the C engine from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=timeout)
    return lib.parse_graph_text(text)


def _parent_build(d, D, seed, time_limit):
    """Construction A: best valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.80 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))

    starts = []
    if D >= 3:
        starts.extend(_arc_extensions(d, t0 + 0.25 * time_limit, rng))
    if D >= 4 and time.monotonic() < t0 + 0.25 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    starts = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    starts.sort(key=lambda g: -g[0])
    if lib.is_valid(fallback[0], fallback[1], d, D):
        starts.append(fallback)
    if not starts:
        return 1, []
    best = max(starts, key=lambda g: g[0])

    plan = starts[:3]
    for idx in range(len(plan) + 1):
        remaining = hard_end - time.monotonic()
        if remaining < 2.0:
            break
        if idx < len(plan):
            src = plan[idx]
            share = remaining / (len(plan) + 1 - idx)
        else:
            src = best
            share = remaining
        try:
            n1, e1 = _augment(src[0], src[1], d, D, seed * 31 + idx,
                              max(0.3, share - 1.0), share + 3.0)
        except Exception:
            continue
        if n1 > best[0] and lib.is_valid(n1, e1, d, D):
            best = (n1, e1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best


# ----------------------------------------------------------------------------
# Construction B: Haar graphs of abelian groups from covering difference sets.
# ----------------------------------------------------------------------------

def _haar_search(d, seed, budget):
    """Run the C difference-set annealer; returns (n, edges) or (0, []) if nothing was found."""
    text = lib.run_c(HAAR_C, [d, int(seed), f"{budget:.2f}"],
                     stdin_graph=None, timeout=budget + 3.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges): construction A first, then construction B if D == 3."""
    t0 = time.monotonic()
    best = _parent_build(d, D, seed, 0.45 * time_limit)

    if D == 3 and 3 <= d <= 40:
        left = 0.80 * time_limit - (time.monotonic() - t0)
        budget = left - 2.0
        if budget >= 2.0:
            try:
                n, e = _haar_search(d, seed, budget)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
