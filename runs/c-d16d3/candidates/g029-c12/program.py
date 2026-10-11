"""Diameter-3 search with a cyclic Haar-graph construction, plus the legacy arc-extension path.

For D = 3, the bipartite Haar graph of Z_m with connection set S (|S| = d) has vertices a_i and b_j,
with a_i ~ b_j iff j - i is in S. Every vertex has degree d. Same-side distance is at most 2 iff S - S
covers Z_m, and then every cross-side distance is at most 3 automatically. So a valid graph of order
2m exists whenever a d-subset S of Z_m has S - S = Z_m. The largest such m is near d^2 - d + 1, the
Moore-type ceiling. The C engine searches for S by simulated annealing on the number of uncovered
differences, and bisects on m. The legacy arc-extended projective plane construction with its C
augmentation engine is kept as a second candidate, and K_{d,d} is the last-resort fallback.
Every candidate is checked with lib.is_valid before it is returned.
"""
import itertools
import random
import time

import lib

# ----------------------------------------------------------------------------
# Haar-graph difference-cover search (D = 3).
# ----------------------------------------------------------------------------

HAAR_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXM 4200

static int M, Dg;
static int S[MAXD];
static int inS[MAXM];
static int cnt[MAXM];
static int zeros;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static inline int md(int a) {
    a %= M;
    if (a < 0) a += M;
    return a;
}

/* cnt[r] = number of ordered pairs (s,t) of distinct elements of S with s - t = r.
   zeros = number of residues r in 1..M-1 with cnt[r] == 0 (the uncovered differences). */
static inline void inc(int r) {
    if (cnt[r] == 0) zeros--;
    cnt[r]++;
}
static inline void dec(int r) {
    cnt[r]--;
    if (cnt[r] == 0) zeros++;
}

static void apply_move(int k, int y) {
    int x = S[k];
    for (int j = 0; j < Dg; j++) {
        if (j == k) continue;
        dec(md(S[j] - x));
        dec(md(x - S[j]));
    }
    inS[x] = 0;
    S[k] = y;
    inS[y] = 1;
    for (int j = 0; j < Dg; j++) {
        if (j == k) continue;
        inc(md(S[j] - y));
        inc(md(y - S[j]));
    }
}

static void rebuild(void) {
    for (int r = 0; r < M; r++) cnt[r] = 0;
    zeros = M - 1;
    for (int a = 0; a < Dg; a++)
        for (int b = 0; b < Dg; b++) {
            if (a == b) continue;
            int r = md(S[a] - S[b]);
            if (cnt[r] == 0) zeros--;
            cnt[r]++;
        }
}

/* Try to find a d-subset of Z_m (containing 0) whose differences cover Z_m. */
static int search_m(int m, int d, double tsec) {
    M = m;
    Dg = d;
    for (int r = 0; r < M; r++) inS[r] = 0;
    S[0] = 0;
    inS[0] = 1;
    for (int j = 1; j < d; j++) {
        int y;
        do {
            y = 1 + rndint(M - 1);
        } while (inS[y]);
        S[j] = y;
        inS[y] = 1;
    }
    rebuild();
    if (zeros == 0) return 1;
    if (d >= M) return 0;

    clock_t start = clock();
    double lim = tsec * (double)CLOCKS_PER_SEC;
    long it = 0;
    const long cycle = 200000;
    const double T0 = 0.6, Tmin = 0.04;
    int cur = zeros;
    while (1) {
        if ((it & 1023) == 0) {
            if ((double)(clock() - start) > lim) break;
        }
        it++;
        double phase = (double)(it % cycle) / (double)cycle;
        double T = Tmin + (T0 - Tmin) * (1.0 - phase) * (1.0 - phase);
        int k = 1 + rndint(d - 1);
        int y;
        do {
            y = 1 + rndint(M - 1);
        } while (inS[y]);
        int x = S[k];
        apply_move(k, y);
        int nz = zeros;
        int delta = nz - cur;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            cur = nz;
            if (cur == 0) return 1;
        } else {
            apply_move(k, x);
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) return 1;
    int d = atoi(argv[1]);
    int lo = atoi(argv[2]);
    int hi = atoi(argv[3]);
    unsigned long seed = strtoul(argv[4], NULL, 10);
    double budget = atof(argv[5]);
    if (d < 2 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;
    if (hi >= MAXM) hi = MAXM - 1;
    if (lo < d) lo = d;

    int bestM = 0;
    int bestS[MAXD];
    clock_t t0 = clock();
    double total = budget * (double)CLOCKS_PER_SEC;
    while (lo <= hi) {
        double left = total - (double)(clock() - t0);
        if (left < 0.05 * (double)CLOCKS_PER_SEC) break;
        int mid = (lo + hi) / 2;
        double slice = budget / 10.0;
        double leftSec = left / (double)CLOCKS_PER_SEC;
        if (slice > leftSec) slice = leftSec;
        if (slice < 0.05) break;
        if (search_m(mid, d, slice)) {
            bestM = mid;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
            lo = mid + 1;
        } else {
            hi = mid - 1;
        }
    }

    if (bestM == 0) {
        printf("0 0\n");
        return 0;
    }
    int m = bestM;
    printf("%d %d\n", 2 * m, m * d);
    for (int i = 0; i < m; i++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", i, m + (i + bestS[j]) % m);
    return 0;
}
"""


def _haar_search(d, seed, budget):
    """Return a Haar graph of order 2m with m as large as the C search finds, or None."""
    if d < 3:
        return None
    text = lib.run_c(HAAR_C, [d, d, d * (d - 1) + 1, seed, f"{budget:.2f}"],
                     timeout=budget + 15)
    n, edges = lib.parse_graph_text(text)
    if n <= 0 or not edges:
        return None
    return n, edges


# ----------------------------------------------------------------------------
# Legacy path: arc-extended projective plane incidence graphs plus C augmentation.
# ----------------------------------------------------------------------------

C_SOURCE_LEGACY = r"""
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
    """Run the legacy C augmentation engine from the start graph (n0, e0)."""
    text = lib.run_c(C_SOURCE_LEGACY, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=timeout)
    return lib.parse_graph_text(text)


def _legacy_build(d, D, seed, time_limit):
    """Best valid (n, edges) from the arc-extension and augmentation path."""
    t0 = time.monotonic()
    hard_end = t0 + 0.80 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

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
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    if not lib.is_valid(fallback[0], fallback[1], d, D):
        fallback = (1, [])

    best = fallback
    if D == 3 and d >= 3:
        try:
            g = _haar_search(d, seed, 0.45 * time_limit)
            if g is not None and g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
                best = g
        except Exception:
            pass
        legacy_limit = 0.30 * time_limit
    else:
        legacy_limit = 0.80 * time_limit

    try:
        g = _legacy_build(d, D, seed, legacy_limit)
        if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = g
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return fallback
    return best
