"""Diameter-3 search with a new difference-cover construction, plus the earlier arc-extension and C augmentation pipeline.

New construction (D = 3): the cyclic Haar graph H(M, S) on Z_M x {A, B}, with a_i adjacent to b_{i+s}
for s in S and |S| = d. Vertices are at distance <= 3 exactly when S - S covers Z_M. Then even distances
reach every same-side vertex (within 2), and odd distances reach every other-side vertex (within 3, since
S - S + S covers Z_M whenever S - S does). So the search asks for a difference cover of size d in Z_M
with M as large as possible, which gives 2M vertices and degree d. C runs a local search over S, minimising
the number of uncovered differences. Haar graphs stay valid when the search fails, because K_{d,d} is the
fallback.

Older pipeline (kept as a secondary source): arc-extended projective plane starts plus a C augmentation
engine that adds vertices whose neighbourhoods keep every pair within distance D. Every candidate is
re-checked with lib.is_valid, and the largest valid graph is returned.
"""
import itertools
import random
import time

import lib

# ----------------------------------------------------------------------------
# C engine 1: difference-cover search for cyclic Haar graphs (diameter 3).
# ----------------------------------------------------------------------------

HAAR_C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXK 64
#define MAXM 1024

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int M, K;
static int S[MAXK];
static int inS[MAXM];
static int cnt[MAXM];
static int uncov;  /* number of x in [1, M-1] with cnt[x] == 0 */

static int md(int x) { x %= M; if (x < 0) x += M; return x; }

/* Add (sgn=+1) or remove (sgn=-1) the ordered differences a-b and b-a. */
static void pair_op(int a, int b, int sgn) {
    int x = md(a - b), y = md(b - a);
    if (sgn > 0) {
        if (cnt[x] == 0) uncov--;
        cnt[x]++;
        if (cnt[y] == 0) uncov--;
        cnt[y]++;
    } else {
        cnt[x]--; if (cnt[x] == 0) uncov++;
        cnt[y]--; if (cnt[y] == 0) uncov++;
    }
}

/* Replace S[i] by x (x not in S). */
static void replace_at(int i, int x) {
    int old = S[i];
    for (int j = 0; j < K; j++) if (j != i) pair_op(old, S[j], -1);
    inS[old] = 0;
    for (int j = 0; j < K; j++) if (j != i) pair_op(x, S[j], +1);
    inS[x] = 1;
    S[i] = x;
}

static int search(long iters, double t_end, int *out) {
    memset(cnt, 0, sizeof(int) * (size_t)M);
    memset(inS, 0, sizeof(int) * (size_t)M);
    for (int i = 0; i < K; i++) {
        int x;
        do x = rndint(M); while (inS[x]);
        S[i] = x;
        inS[x] = 1;
    }
    uncov = M - 1;
    for (int i = 0; i < K; i++)
        for (int j = i + 1; j < K; j++) pair_op(S[i], S[j], +1);

    for (long it = 0; it < iters; it++) {
        if (uncov == 0) break;
        if ((it & 4095) == 0 && elapsed() > t_end) break;
        int i = rndint(K);
        int x;
        do x = rndint(M); while (inS[x]);
        int old = S[i];
        int before = uncov;
        replace_at(i, x);
        if (uncov > before && rndint(100) >= 3) replace_at(i, old);
    }
    if (uncov == 0) {
        memcpy(out, S, sizeof(int) * (size_t)K);
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 4) return 1;
    K = atoi(argv[1]);
    unsigned long seed = strtoul(argv[2], NULL, 10);
    double budget = atof(argv[3]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    if (K < 2 || K >= MAXK) {
        printf("0 0\n");
        return 0;
    }

    int mmax = K * (K - 1) + 1;
    if (mmax >= MAXM) mmax = MAXM - 1;
    double t_end = elapsed() + budget;

    int bestM = 0;
    int bestS[MAXK];
    int tmp[MAXK];
    int m = K * (K - 1) / 2;
    if (m < K + 1) m = K + 1;
    int fails = 0;
    while (m <= mmax && elapsed() < t_end && fails < 3) {
        M = m;
        if (search(2000000L, t_end, tmp)) {
            bestM = m;
            memcpy(bestS, tmp, sizeof(int) * (size_t)K);
            fails = 0;
        } else {
            fails++;
        }
        m++;
    }

    if (bestM == 0) {
        printf("0 0\n");
        return 0;
    }
    M = bestM;
    long E = (long)M * K;
    printf("%d %ld\n", 2 * M, E);
    for (int i = 0; i < M; i++)
        for (int k = 0; k < K; k++)
            printf("%d %d\n", i, M + (i + bestS[k]) % M);
    return 0;
}
"""

# ----------------------------------------------------------------------------
# C engine 2: augmentation (from the earlier pipeline).
# ----------------------------------------------------------------------------

AUG_C_SOURCE = r"""
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

def _haar_search(d, seed, budget):
    """Difference-cover search for a cyclic Haar graph with degree d; returns (n, edges) or (0, [])."""
    text = lib.run_c(HAAR_C_SOURCE, [d, seed, f"{budget:.2f}"],
                     stdin_graph=None, timeout=budget + 10.0)
    return lib.parse_graph_text(text)


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


def _augment(n0, e0, d, D, seed, budget, timeout):
    """Run the augmentation C engine from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(AUG_C_SOURCE, [d, D, seed, f"{budget:.2f}"],
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

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    if not lib.is_valid(fallback[0], fallback[1], d, D):
        return 1, []
    best = fallback

    # New construction: cyclic Haar graph from a difference cover (diameter 3).
    if D == 3 and d >= 3:
        try:
            n1, e1 = _haar_search(d, seed, max(1.0, 0.45 * time_limit - 2.0))
            if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                best = (n1, e1)
        except Exception:
            pass

    # Older pipeline: arc-extended projective planes (and GQ for D >= 4).
    starts = []
    arc_deadline = t0 + 0.55 * time_limit
    if D >= 3:
        starts.extend(_arc_extensions(d, arc_deadline, rng))
    if D >= 4 and time.monotonic() < arc_deadline:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    starts = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    starts.sort(key=lambda g: -g[0])
    for g in starts:
        if g[0] > best[0]:
            best = g

    # Augment the top starts with the C engine, then keep augmenting the best result.
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
            n2, e2 = _augment(src[0], src[1], d, D, seed * 31 + idx,
                              max(0.3, share - 1.0), share + 3.0)
        except Exception:
            continue
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
