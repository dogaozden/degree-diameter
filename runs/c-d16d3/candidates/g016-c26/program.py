"""Diameter-3 bipartite search: a cyclic/semidirect difference-cover construction plus the
arc-extended projective plane and C augmentation engine from the parent.

New construction (D = 3). Take a group G of order n and a set S of d elements with
S S^-1 = G and S^-1 S = G. The bi-Cayley graph with a_x ~ b_{xs} (s in S) is d-regular and
bipartite on 2n vertices. Every a-a pair is at distance 2 and every b-b pair at distance 2,
and every a-b pair is at distance at most 3. So the diameter is at most 3. The largest n is
bounded by the Moore-type limit d^2 - d + 1, and d = 16 gives 241 (order 482, the ceiling).
A simulated-annealing C search looks for such S in cyclic and semidirect groups. Orders are
tried in increasing order, and the best valid graph is kept.

The parent pipeline (arc-extended PG(2,q) plus augmentation) still runs and serves as the
fallback. Every candidate is re-checked with lib.is_valid, and K_{d,d} is kept as the last resort.
"""
import itertools
import math
import random
import time

import lib

# ----------------------------------------------------------------------------
# C engine: simulated annealing for a 2-sided difference cover in a finite group.
# stdin: "n m" with m = n*n, then m pairs "u v"; entry k gives mul[k/n][k%n] = u.
# argv: d seed budget. Output: "OK s0 ... s_{d-1}" or "FAIL".
# ----------------------------------------------------------------------------
DC_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 512
#define MAXD 64

static int n, d;
static int mul[MAXG][MAXG];
static int inv[MAXG];
static int S[MAXD];
static int in[MAXG];
static int cnt1[MAXG], cnt2[MAXG];
static uint64_t rs = 1;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* Number of uncovered elements for S S^-1 plus uncovered for S^-1 S. */
static int cost(void) {
    int unc = 0;
    memset(cnt1, 0, sizeof(int) * (size_t)n);
    memset(cnt2, 0, sizeof(int) * (size_t)n);
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) {
            cnt1[mul[S[i]][inv[S[j]]]]++;
            cnt2[mul[inv[S[i]]][S[j]]]++;
        }
    for (int y = 0; y < n; y++) {
        if (!cnt1[y]) unc++;
        if (!cnt2[y]) unc++;
    }
    return unc;
}

int main(int argc, char **argv) {
    if (argc < 4) return 1;
    d = atoi(argv[1]);
    unsigned long seed = strtoul(argv[2], NULL, 10);
    double budget = atof(argv[3]);
    rs = 0x9E3779B97F4A7C15ULL ^ ((uint64_t)seed * 0xBF58476D1CE4E5B9ULL + 17ULL);
    if (rs == 0) rs = 1;

    int m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXG || d < 2 || d > MAXD || d > n || m != n * n) {
        printf("FAIL\n");
        return 0;
    }
    for (int k = 0; k < m; k++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || u >= n) {
            printf("FAIL\n");
            return 0;
        }
        mul[k / n][k % n] = u;
    }
    for (int g = 0; g < n; g++) {
        inv[g] = -1;
        for (int h = 0; h < n; h++)
            if (mul[g][h] == 0) { inv[g] = h; break; }
        if (inv[g] < 0) {
            printf("FAIL\n");
            return 0;
        }
    }

    memset(in, 0, sizeof(in));
    S[0] = 0;
    in[0] = 1;
    for (int k = 1; k < d; k++) {
        int c;
        do c = rndint(n); while (in[c]);
        S[k] = c;
        in[c] = 1;
    }

    clock_t start = clock();
    int cur = cost();
    double T = 0.8;
    long it = 0;
    while (cur > 0) {
        if ((it & 1023) == 0 && (double)(clock() - start) / CLOCKS_PER_SEC > budget) break;
        it++;
        if (it % 2000 == 0) {
            T *= 0.97;
            if (T < 0.1) T = 0.5 + 0.5 * urand();
        }
        int pos = 1 + rndint(d - 1);
        int c = rndint(n);
        if (in[c]) continue;
        int old = S[pos];
        S[pos] = c;
        int nc = cost();
        int acc = (nc <= cur);
        if (!acc) acc = urand() < exp((double)(cur - nc) / T);
        if (acc) {
            in[old] = 0;
            in[c] = 1;
            cur = nc;
        } else {
            S[pos] = old;
        }
    }
    if (cur == 0) {
        printf("OK");
        for (int k = 0; k < d; k++) printf(" %d", S[k]);
        printf("\n");
    } else {
        printf("FAIL\n");
    }
    return 0;
}
"""

# ----------------------------------------------------------------------------
# Parent C engine: augments a valid graph by adding vertices (diameter D).
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
# New construction: bi-Cayley graphs from difference covers in groups (D = 3).
# ----------------------------------------------------------------------------

def _group_candidates(n, rng):
    """Return [(order, mul)] for the cyclic group of order n and one random semidirect option."""
    out = [lib.cyclic_group(n)[:2]]
    opts = []
    for k in range(2, n):
        if n % k:
            continue
        m = n // k
        if m < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    if opts:
        m, k, r = opts[rng.randrange(len(opts))]
        try:
            order, mul, _inv = lib.semidirect_group(m, k, r)
            if order == n:
                out.append((order, mul))
        except ValueError:
            pass
    return out


def _cover_search(order, mul, d, seed, budget):
    """Run the C annealer; return a list of d group elements S, or None."""
    edges = [(mul(x, y), 0) for x in range(order) for y in range(order)]
    try:
        text = lib.run_c(DC_SOURCE, [d, seed, f"{budget:.2f}"],
                         stdin_graph=(order, edges), timeout=budget + 6.0)
    except Exception:
        return None
    tok = text.split()
    if len(tok) < d + 1 or tok[0] != "OK":
        return None
    try:
        S = [int(t) for t in tok[1:1 + d]]
    except ValueError:
        return None
    if len(set(S)) != d or any(not (0 <= s < order) for s in S):
        return None
    return S


def _group_search(d, D, seed, deadline):
    """Try orders n from the Moore-type range upward; return the largest valid (2n, edges) found."""
    rng = random.Random(seed * 1000003 + d * 97 + D)
    hi = d * d - d + 1            # per-side Moore limit for D = 3
    lo = max(d, (hi * 4) // 5)    # start near the parent's level
    best = None
    n = lo
    while n <= hi:
        for order, mul in _group_candidates(n, rng):
            remain = deadline - time.monotonic()
            if remain < 0.8:
                return best
            budget = min(2.0, remain - 0.5)
            S = _cover_search(order, mul, d, rng.randrange(1, 1 << 30), budget)
            if S is None:
                continue
            edges = lib.group_lift(2, [(0, 1, g) for g in S], order, mul)[1]
            if lib.is_valid(2 * order, edges, d, D) and (best is None or 2 * order > best[0]):
                best = (2 * order, edges)
            break
        n += 1
    return best


# ----------------------------------------------------------------------------
# Parent construction: arc-extended projective plane (D = 3) and augmentation.
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


def _augment(n0, e0, d, D, seed, budget, timeout):
    """Run the C augmentation engine from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=timeout)
    return lib.parse_graph_text(text)


def _parent_build(d, D, seed, time_limit):
    """Parent pipeline: arc-extended PG starts, then C augmentation. Returns a valid graph."""
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

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    best = fallback if lib.is_valid(fallback[0], fallback[1], d, D) else (1, [])

    def consider(g):
        nonlocal best
        if g is not None and g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = g

    if D == 3 and d >= 3:
        # Parent pipeline gets a short slice; the difference-cover search gets the rest.
        try:
            consider(_parent_build(d, D, seed, 0.3 * time_limit))
        except Exception:
            pass
        try:
            consider(_group_search(d, D, seed, t0 + 0.8 * time_limit))
        except Exception:
            pass
    else:
        try:
            consider(_parent_build(d, D, seed, time_limit))
        except Exception:
            pass

    return best
