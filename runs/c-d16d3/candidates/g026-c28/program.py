"""Diameter-3 bipartite search: Haar-graph difference covers, plus arc-extended PG(2,q) starts.

For D = 3, the main construction is the Haar graph of a cyclic group Z_m with connection set
S of size d. Vertices a_i and b_i (i in Z_m) are joined when b_j - a_i is in S. The graph has
diameter <= 3 exactly when every nonzero residue of Z_m is a difference s - t (s != t, both in S),
so |S| = d gives m <= d(d-1)+1 and order at most 2(d(d-1)+1). The C engine runs simulated
annealing on S to find difference covers for increasing m. Each candidate is verified in C
and again in Python with lib.is_valid.

Other starts are kept as fallbacks: arc-extended projective plane incidence graphs for D >= 3,
the generalized quadrangle W(q) for D >= 4, and K_{d,d} (diameter 2, valid for every D >= 2).
For D >= 4, and for any leftover time, the original C augmentation engine adds vertices to the
best start. Python re-checks every returned graph with lib.is_valid.
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

# ----------------------------------------------------------------------------
# Haar-graph difference-cover search (diameter 3).
# Find S in Z_m with |S| = K and every nonzero residue equal to s - t for some s != t in S.
# The Haar graph H(Z_m, S) then has diameter <= 3 and order 2m.
# ----------------------------------------------------------------------------

HAAR_C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 1024
#define MAXK 64

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int M, K;
static int S[MAXK];
static char inS[MAXM];
static int cnt[MAXM];
static int zeros;   /* number of residues r in 1..M-1 with cnt[r] == 0 */

static int dm(int x) {
    x %= M;
    if (x < 0) x += M;
    return x;
}

static void add_diff(int r, int delta) {
    if (r == 0) return;
    if (delta > 0) {
        if (cnt[r] == 0) zeros--;
        cnt[r]++;
    } else {
        cnt[r]--;
        if (cnt[r] == 0) zeros++;
    }
}

static void remove_elem(int i) {
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        add_diff(dm(S[i] - S[j]), -1);
        add_diff(dm(S[j] - S[i]), -1);
    }
}

static void insert_elem(int i) {
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        add_diff(dm(S[i] - S[j]), +1);
        add_diff(dm(S[j] - S[i]), +1);
    }
}

static int verify(void) {
    static char seen[MAXM];
    memset(seen, 0, sizeof(char) * (size_t)M);
    seen[0] = 1;
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            if (i != j) seen[dm(S[i] - S[j])] = 1;
    for (int r = 0; r < M; r++)
        if (!seen[r]) return 0;
    for (int i = 0; i < K; i++)
        for (int j = i + 1; j < K; j++)
            if (S[i] == S[j]) return 0;
    return 1;
}

/* Simulated annealing for a difference cover of Z_m with K elements. */
static int solve_m(int m, double deadline) {
    M = m;
    memset(inS, 0, sizeof(char) * (size_t)m);
    memset(cnt, 0, sizeof(int) * (size_t)m);
    zeros = m - 1;
    for (int i = 0; i < K;) {
        int x = rndint(m);
        if (inS[x]) continue;
        inS[x] = 1;
        S[i++] = x;
    }
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            if (i != j) add_diff(dm(S[i] - S[j]), +1);

    const long CYC = 400000;
    long it = 0;
    double T = 1.0;
    while (zeros > 0) {
        if ((it & 1023) == 0) {
            if (elapsed() > deadline) return 0;
            double f = (double)(it % CYC) / (double)CYC;
            T = pow(0.12, f);            /* reheat from 1.0 down to 0.12 each cycle */
        }
        it++;

        int r = -1;
        for (int t = 0; t < 8; t++) {
            int c = 1 + rndint(m - 1);
            if (cnt[c] == 0) {
                r = c;
                break;
            }
        }
        int i = rndint(K);
        int x;
        if (r > 0 && rnd01() < 0.85) {
            int j = rndint(K - 1);
            if (j >= i) j++;
            x = dm(S[j] + r);            /* creates difference x - S[j] = r */
        } else {
            x = rndint(m);
        }
        if (inS[x]) continue;

        int old = S[i];
        int oldz = zeros;
        remove_elem(i);
        S[i] = x;
        insert_elem(i);
        int delta = zeros - oldz;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            inS[old] = 0;
            inS[x] = 1;
        } else {
            remove_elem(i);
            S[i] = old;
            insert_elem(i);
        }
    }
    if (!verify()) return 0;
    int c = S[0];
    for (int i = 0; i < K; i++) S[i] = dm(S[i] - c);   /* translate so 0 is in S */
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    K = atoi(argv[1]);
    int mstart = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    if (K < 2 || K > MAXK) {
        printf("0 0\n");
        return 0;
    }

    int mmax = K * (K - 1) + 1;
    if (mmax > MAXM - 1) mmax = MAXM - 1;
    double tend = elapsed() + budget;

    int bestm = 0;
    int bestS[MAXK];
    int m = mstart;
    if (m < K + 1) m = K + 1;
    while (m <= mmax) {
        double rem = tend - elapsed();
        if (rem <= 0.05) break;
        double slice = rem * 0.5;
        if (!solve_m(m, elapsed() + slice)) break;
        bestm = m;
        memcpy(bestS, S, sizeof(int) * (size_t)K);
        m++;
    }

    if (bestm == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", 2 * bestm, bestm * K);
    for (int i = 0; i < bestm; i++)
        for (int k = 0; k < K; k++)
            printf("%d %d\n", i, bestm + (i + bestS[k]) % bestm);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has spare capacity s = d - q - 1. Choose a point set S that is an arc, so each
# line holds at most s points of S. Add an A-vertex for each P in S (joined to
# lines through P) and a B-vertex for each j in S (joined to points on line j).
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
# C drivers.
# ----------------------------------------------------------------------------

def _augment(n0, e0, d, D, seed, budget, timeout):
    """Run the augmentation C engine from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=timeout)
    return lib.parse_graph_text(text)


def _haar_search(d, seed, budget):
    """Search for a difference cover of size d (diameter-3 Haar graph); returns (n, edges)."""
    mstart = max(d + 1, (3 * d * (d - 1)) // 4)
    text = lib.run_c(HAAR_C_SOURCE, [d, mstart, seed, f"{budget:.2f}"],
                     timeout=budget + 8.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 80% of time_limit."""
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
        starts.extend(_arc_extensions(d, t0 + 0.15 * time_limit, rng))
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

    # Main bold step for D = 3: difference-cover Haar graphs, which can reach order 2*(d(d-1)+1).
    if D == 3 and d >= 2:
        budget = max(1.0, hard_end - time.monotonic() - 2.0)
        try:
            n1, e1 = _haar_search(d, seed, budget)
            if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                best = (n1, e1)
        except Exception:
            pass

    # Augment the top starts with the C engine while time remains (mainly for D >= 4).
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
