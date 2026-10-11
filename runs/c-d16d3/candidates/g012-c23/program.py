"""Diameter-3 search, with two constructions compared per case.

1. Parent pipeline: arc-extended projective plane starts plus the C augmentation engine
   (kept as the safe baseline; it already reaches the record for d=16, D=3).
2. New Haar difference-covering search: a Haar graph H(Z_n, S) with |S| = d is bipartite,
   d-regular, and has diameter 3 exactly when the differences S - S cover all of Z_n.
   Since |S - S| <= d(d-1) + 1, this gives order up to 2(d^2 - d + 1), which equals the
   ceiling for d=16 (482). C runs simulated annealing on S, with a binary search over n.

The best valid graph from either route is returned. K_{d,d} is the final fallback.
"""
import itertools
import random
import time

import lib

PARENT_C = r"""
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

#define MAXK 64
#define MAXN 1024

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int n, k;
static int S[MAXK];
static int inS[MAXN];
static int cnt[MAXN];
static int cost; /* number of residues x in 1..n-1 with no difference equal to x */

static int md(int x) {
    x %= n;
    if (x < 0) x += n;
    return x;
}

static void init_state(void) {
    memset(inS, 0, sizeof(inS));
    memset(cnt, 0, sizeof(cnt));
    for (int i = 0; i < k; i++) inS[S[i]] = 1;
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            if (i != j) cnt[md(S[i] - S[j])]++;
    cost = 0;
    for (int x = 1; x < n; x++)
        if (cnt[x] == 0) cost++;
}

/* Remove the element at idx (its current value is S[idx]). */
static void remove_el(int idx) {
    int s = S[idx];
    for (int j = 0; j < k; j++) {
        if (j == idx) continue;
        int x = md(s - S[j]);
        if (--cnt[x] == 0) cost++;
        int y = md(S[j] - s);
        if (--cnt[y] == 0) cost++;
    }
    inS[s] = 0;
}

/* Put value t at idx and add its differences. */
static void add_el(int idx, int t) {
    S[idx] = t;
    for (int j = 0; j < k; j++) {
        if (j == idx) continue;
        int x = md(t - S[j]);
        if (cnt[x]++ == 0) cost--;
        int y = md(S[j] - t);
        if (cnt[y]++ == 0) cost--;
    }
    inS[t] = 1;
}

static int anneal(double t_end) {
    const long iters = 3000000L;
    const double T0 = 1.5, T1 = 0.08;
    static int pool[MAXN];
    while (now() < t_end) {
        for (int i = 0; i < n; i++) pool[i] = i;
        for (int i = 0; i < k; i++) {
            int r = i + (int)(rnd() % (uint64_t)(n - i));
            int tmp = pool[i];
            pool[i] = pool[r];
            pool[r] = tmp;
            S[i] = pool[i];
        }
        init_state();
        if (cost == 0) return 1;
        double T = T0;
        for (long it = 0; it < iters; it++) {
            if ((it & 4095) == 0) {
                if (now() > t_end) return 0;
                T = T0 * pow(T1 / T0, (double)it / (double)iters);
            }
            int idx = (int)(rnd() % (uint64_t)k);
            int s = S[idx];
            int t;
            do {
                t = (int)(rnd() % (uint64_t)n);
            } while (inS[t]);
            int old = cost;
            remove_el(idx);
            add_el(idx, t);
            int delta = cost - old;
            if (delta <= 0 || rnd01() < exp(-delta / T)) {
                if (cost == 0) return 1;
            } else {
                remove_el(idx);
                add_el(idx, s);
            }
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 4) return 1;
    k = atoi(argv[1]);
    double budget = atof(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    if (k < 1 || k > MAXK) {
        printf("0 0\n");
        return 0;
    }
    int hi = 1 + k * (k - 1);
    if (hi > MAXN / 2 - 1) hi = MAXN / 2 - 1;

    /* Z_k with S = Z_k is always a valid difference covering (order 2k). */
    int best_n = k;
    int best_S[MAXK];
    for (int i = 0; i < k; i++) best_S[i] = i;

    double t_end = now() + budget;
    double slice = budget / 6.0;
    if (slice < 0.5) slice = 0.5;
    int a = k + 1, b = hi;
    while (a <= b && now() < t_end) {
        int mid = (a + b) / 2;
        n = mid;
        double dl = now() + slice;
        if (dl > t_end) dl = t_end;
        int ok = anneal(dl);
        if (ok) {
            best_n = mid;
            for (int i = 0; i < k; i++) best_S[i] = S[i];
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }

    int N = best_n;
    printf("%d %d\n", 2 * N, N * k);
    for (int i = 0; i < N; i++)
        for (int j = 0; j < k; j++)
            printf("%d %d\n", i, N + (i + best_S[j]) % N);
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
# C augmentation driver for the parent pipeline.
# ----------------------------------------------------------------------------

def _augment(n0, e0, d, D, seed, budget, timeout):
    """Run the C augmentation engine from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(PARENT_C, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=timeout)
    return lib.parse_graph_text(text)


def _parent_build(d, D, seed, time_limit):
    """Parent pipeline: arc-extended starts plus C augmentation. Returns a valid (n, edges)."""
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
# New construction: Haar graphs from difference coverings.
# ----------------------------------------------------------------------------

def _haar_search(d, budget, seed):
    """Run the difference-covering annealer; returns (n, edges) of the Haar graph."""
    text = lib.run_c(HAAR_C, [d, f"{budget:.2f}", seed], timeout=budget + 5.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 88% of time_limit."""
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}, valid for every D >= 2
    best = fallback if lib.is_valid(fallback[0], fallback[1], d, D) else (1, [])

    if D >= 3 and d >= 3:
        # Parent pipeline first, so the known baseline is always kept.
        try:
            cand = _parent_build(d, D, seed, 0.40 * time_limit)
            if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
                best = cand
        except Exception:
            pass

        # New Haar difference-covering search with the remaining time.
        remaining = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        if remaining >= 3.0:
            try:
                n1, e1 = _haar_search(d, remaining, seed)
                if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                    best = (n1, e1)
            except Exception:
                pass
    else:
        try:
            cand = _parent_build(d, D, seed, 0.85 * time_limit)
            if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
                best = cand
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
