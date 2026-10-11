"""Diameter-3 bipartite search with a difference-covering Haar construction.

Main new idea: a Haar graph H(Z_m, S) with |S| = d is a d-regular bipartite graph on 2m
vertices. Its distance-2 pairs on one side are exactly the differences S - S, so it has
diameter at most 3 whenever S - S covers all of Z_m. The C engine searches for such
covering sets S by simulated annealing, scanning m downward from the Moore-type ceiling
d^2 - d + 1. Python checks each result with lib.is_valid.

The previous approach (arc-extended projective plane plus C augmentation) is kept as a
second candidate and as a source of spare-degree augmentation. K_{d,d} is the safe fallback.
The largest valid graph found is returned.
"""
import itertools
import random
import time

import lib

# ----------------------------------------------------------------------------
# C engine 1: difference-covering search for Haar graphs (diameter 3).
# Output: "M K" then K lines, the elements of S (S contains 0). Or "0 0".
# ----------------------------------------------------------------------------

C_HAAR = r"""
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

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int K, M, unc;
static int S[MAXK];
static int inS[MAXM];
static int cnt[MAXM];

static int md(int x) {
    x %= M;
    if (x < 0) x += M;
    return x;
}

/* cnt[x] = number of ordered pairs (s, t), s != t in S, with s - t = x (x != 0).
   unc = number of nonzero residues with cnt = 0. */
static void bump(int x, int d) {
    if (x == 0) return;
    if (d > 0) {
        if (cnt[x] == 0) unc--;
        cnt[x] += d;
    } else {
        cnt[x] += d;
        if (cnt[x] == 0) unc++;
    }
}

static void remove_el(int i) {
    int x = S[i];
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        bump(md(x - S[j]), -1);
        bump(md(S[j] - x), -1);
    }
    inS[x] = 0;
}

static void add_el(int i, int y) {
    S[i] = y;
    inS[y] = 1;
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        bump(md(y - S[j]), 1);
        bump(md(S[j] - y), 1);
    }
}

/* One simulated-annealing attempt for the current M. Returns 1 if S - S covers Z_M. */
static int attempt(long iters, double T0, double T1) {
    memset(inS, 0, sizeof(int) * M);
    memset(cnt, 0, sizeof(int) * M);
    unc = M - 1;
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < K; i++) {
        int y;
        do {
            y = 1 + rndint(M - 1);
        } while (inS[y]);
        S[i] = y;
        inS[y] = 1;
    }
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            if (i != j) bump(md(S[i] - S[j]), 1);

    for (long it = 0; it < iters && unc > 0; it++) {
        int i = 1 + rndint(K - 1);
        int y = rndint(M);
        if (inS[y]) continue;
        int x = S[i];
        int old = unc;
        remove_el(i);
        add_el(i, y);
        int delta = unc - old;
        if (delta <= 0) continue;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        if (rnd01() < exp(-(double)delta / T)) continue;
        remove_el(i);
        add_el(i, x);
    }
    return unc == 0;
}

int main(int argc, char **argv) {
    if (argc < 4) {
        printf("0 0\n");
        return 0;
    }
    K = atoi(argv[1]);
    double budget = atof(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    if (K < 2 || K > MAXK) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    double end = now() + budget;
    int hi = K * K - K + 1;
    if (hi > MAXM - 1) hi = MAXM - 1;
    int lo = 2 * K;
    for (int m = hi; m >= lo; m--) {
        if (now() >= end) break;
        M = m;
        double slice = now() + 0.3;
        if (slice > end) slice = end;
        int ok = 0;
        while (!ok && now() < slice) ok = attempt(1500000L, 1.0, 0.05);
        if (ok) {
            printf("%d %d\n", M, K);
            for (int i = 0; i < K; i++) printf("%d\n", S[i]);
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}
"""

# ----------------------------------------------------------------------------
# C engine 2: augmentation (kept from the previous program). Adds one vertex on a
# random side, joined to spare vertices on the other side, if every existing vertex
# stays within distance D-1 of the chosen neighbours.
# ----------------------------------------------------------------------------

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
# Python constructions.
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


def _haar_search(d, seed, budget):
    """Run the difference-covering search; return the Haar graph (2m, edges) or None."""
    text = lib.run_c(C_HAAR, [d, f"{budget:.2f}", seed], timeout=budget + 10.0)
    nums = [int(x) for x in text.split()]
    if len(nums) < 2 or nums[0] <= 0 or nums[1] != d:
        return None
    m, k = nums[0], nums[1]
    S = nums[2:2 + k]
    if len(S) != k or len(set(s % m for s in S)) != k:
        return None
    return lib.haar_graph(m, S)


def _augment(n0, e0, d, D, seed, budget, timeout):
    """Run the augmentation C engine from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=timeout)
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

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    if not lib.is_valid(fallback[0], fallback[1], d, D):
        return 1, []
    best = [fallback]

    def consider(g):
        if g is not None and g[0] > best[0][0] and lib.is_valid(g[0], g[1], d, D):
            best[0] = g

    # Phase 1: difference-covering Haar graph search (diameter 3 by construction).
    if D >= 3:
        try:
            consider(_haar_search(d, seed, 0.40 * time_limit))
        except Exception:
            pass

    # Phase 2: arc-extended projective plane starts.
    arcs = []
    if D >= 3:
        try:
            arcs = _arc_extensions(d, time.monotonic() + 0.10 * time_limit, rng)
        except Exception:
            arcs = []
    arcs = [g for g in arcs if lib.is_valid(g[0], g[1], d, D)]
    for g in arcs:
        consider(g)

    # Phase 3: generalized quadrangle start for D >= 4.
    if D >= 4:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq)
        except Exception:
            pass

    # Phase 4: augment the largest arc start with the remaining time.
    if arcs:
        src = max(arcs, key=lambda g: g[0])
        remaining = hard_end - time.monotonic()
        if remaining > 2.0:
            try:
                n1, e1 = _augment(src[0], src[1], d, D, seed * 31 + 1,
                                  max(0.3, remaining - 1.5), remaining + 3.0)
                consider((n1, e1))
            except Exception:
                pass

    best_g = best[0]
    if not lib.is_valid(best_g[0], best_g[1], d, D):
        best_g = fallback
    return best_g
