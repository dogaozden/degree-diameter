"""Diameter-3 bipartite search: cyclic Haar-graph difference covers plus arc-extended projective planes.

New in this version: for D >= 3 the main construction is a Haar graph H(M, S) on Z_M with
connection set S of size d. Its vertices a_i = i and b_j = M + j are joined when j - i is in S.
It is d-regular and bipartite. Its diameter is at most 3 exactly when
  (1) S - S covers every nonzero residue mod M (even distances between the same side), and
  (2) S - S + S covers every residue mod M (odd distances between the two sides).
The C engine searches for a set S by simulated annealing on the number of uncovered differences,
for M = d+1, d+2, ... and keeps the largest M that succeeds. Order 2M beats the arc-extended
projective-plane starts whenever M is large. The old arc-extension starts and the old C
augmentation engine are kept as alternatives. K_{d,d} remains the safe fallback. Every candidate
is checked with lib.is_valid and the largest valid graph is returned.
"""
import itertools
import random
import time

import lib

C_HAAR_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 64
#define MAXM 4096

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int K, M, uncovered;
static int S[MAXK];
static char inS[MAXM];
static int cnt[MAXM];

static int md(int x) {
    x %= M;
    if (x < 0) x += M;
    return x;
}

static void upd(int r, int sg) {
    if (sg > 0) {
        if (cnt[r] == 0) uncovered--;
        cnt[r]++;
    } else {
        cnt[r]--;
        if (cnt[r] == 0) uncovered++;
    }
}

/* Add (sg=+1) or remove (sg=-1) the ordered differences between x and every S[j], j != skip. */
static void diffs(int x, int skip, int sg) {
    for (int j = 0; j < K; j++) {
        if (j == skip) continue;
        upd(md(x - S[j]), sg);
        upd(md(S[j] - x), sg);
    }
}

/* Check that S - S + S covers all of Z_M. */
static int check3(void) {
    static char mark[MAXM];
    memset(mark, 0, (size_t)M);
    for (int a = 0; a < K; a++)
        for (int b = 0; b < K; b++)
            for (int c = 0; c < K; c++)
                mark[md(S[a] - S[b] + S[c])] = 1;
    for (int r = 0; r < M; r++)
        if (!mark[r]) return 0;
    return 1;
}

static int anneal(long maxit, double T0, double T1, double deadline) {
    memset(inS, 0, sizeof(inS));
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < K; i++) {
        int y;
        do {
            y = 1 + (int)(rnd() % (uint64_t)(M - 1));
        } while (inS[y]);
        S[i] = y;
        inS[y] = 1;
    }
    memset(cnt, 0, sizeof(int) * (size_t)M);
    uncovered = M - 1;
    for (int i = 0; i < K; i++)
        for (int j = 0; j < i; j++) {
            upd(md(S[i] - S[j]), 1);
            upd(md(S[j] - S[i]), 1);
        }

    for (long it = 0; it < maxit; it++) {
        if (uncovered == 0 && check3()) return 1;
        if ((it & 0xFFFF) == 0 && now() > deadline) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)maxit);
        int i = 1 + (int)(rnd() % (uint64_t)(K - 1));  /* S[0] = 0 stays fixed */
        int x = S[i];
        int y;
        do {
            y = 1 + (int)(rnd() % (uint64_t)(M - 1));
        } while (inS[y]);
        int u0 = uncovered;
        diffs(x, i, -1);
        S[i] = y;
        diffs(y, i, +1);
        int delta = uncovered - u0;
        if (delta <= 0 || urand() < exp(-delta / T)) {
            inS[x] = 0;
            inS[y] = 1;
        } else {
            diffs(y, i, -1);
            S[i] = x;
            diffs(x, i, +1);
        }
    }
    return uncovered == 0 && check3();
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (d < 2 || d > MAXK || D < 3) {
        printf("0 0\n");
        return 0;
    }
    K = d;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;

    double deadline = now() + budget;
    int bestM = 0;
    int bestS[MAXK];
    int fails = 0;
    for (int m = K + 1; m < MAXM / 2 && now() < deadline && fails < 8; m++) {
        M = m;
        int ok = 0;
        for (int rep = 0; rep < 3 && !ok && now() < deadline; rep++)
            ok = anneal(3000000L, 0.8, 0.05, deadline);
        if (ok) {
            fails = 0;
            bestM = m;
            memcpy(bestS, S, sizeof(int) * (size_t)K);
        } else {
            fails++;
        }
    }

    if (bestM == 0) {
        printf("0 0\n");
        return 0;
    }
    M = bestM;
    memcpy(S, bestS, sizeof(int) * (size_t)K);
    int E = M * K;
    printf("%d %d\n", 2 * M, E);
    for (int i = 0; i < M; i++)
        for (int k = 0; k < K; k++)
            printf("%d %d\n", i, M + (i + S[k]) % M);
    return 0;
}
"""

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
# Arc-extended projective plane incidence graphs (diameter 3).
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
# Drivers for the C engines.
# ----------------------------------------------------------------------------

def _haar(d, seed, budget):
    """Run the Haar difference-cover search (D = 3 construction). Returns (n, edges), maybe (0, [])."""
    text = lib.run_c(C_HAAR_SOURCE, [d, 3, seed, f"{budget:.2f}"], timeout=budget + 8.0)
    return lib.parse_graph_text(text)


def _augment(n0, e0, d, D, seed, budget, timeout):
    """Run the augmentation C engine from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=timeout)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the largest valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.80 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    def valid(g):
        return lib.is_valid(g[0], g[1], d, D)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))

    cands = []
    if valid(fallback):
        cands.append(fallback)

    arcs = []
    if D >= 3:
        arc_deadline = t0 + 0.12 * time_limit
        arcs = [g for g in _arc_extensions(d, arc_deadline, rng) if valid(g)]
        if D >= 4 and time.monotonic() < arc_deadline:
            gq = _best_gq(d)
            if gq is not None and valid(gq):
                arcs.append(gq)
        cands.extend(arcs)

        # Main bold construction: Haar graph from a difference cover, given most of the time.
        rem = hard_end - time.monotonic()
        if rem > 3.0:
            try:
                g = _haar(d, seed, 0.55 * rem)
                if g[0] > 0 and valid(g):
                    cands.append(g)
            except Exception:
                pass

    if not cands:
        return 1, []
    best = max(cands, key=lambda g: g[0])

    # Augment the largest arc-type start with the remaining time (parent engine).
    if arcs:
        src = max(arcs, key=lambda g: g[0])
        rem = hard_end - time.monotonic()
        if rem > 2.0:
            try:
                g = _augment(src[0], src[1], d, D, seed * 31 + 7,
                             max(0.3, rem - 1.0), rem + 3.0)
                if g[0] > best[0] and valid(g):
                    best = g
            except Exception:
                pass

    if not valid(best):
        best = fallback
    return best
