"""Diameter-3 bipartite search: arc-extended projective plane starts, a difference-cover
Haar-graph search, and a C augmentation engine.

Starts (all valid): arc-extended PG(2,q) incidence graphs, the generalized quadrangle W(q)
for D >= 4, and K_{d,d}. For D = 3 there is a substantially different construction: the Haar
graph H(G, S) of a finite group G of order M, with a_g ~ b_{gs} for s in S, |S| = d. It is
d-regular and bipartite on 2M vertices, and has diameter 3 exactly when S S^{-1} = G (a
difference cover). Since S S^{-1} has at most d(d-1)+1 elements, M <= d^2-d+1 and the order is
at most the Moore bound. A C simulated-annealing search looks for difference covers in
cyclic and small semidirect-product groups, scanning orders above the current best. Every
candidate is re-checked with lib.is_valid, and the best valid graph is kept as the fallback.
The C augmentation engine from the previous version still runs on the remaining time.
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

/* ---------------- Part A: difference-cover search in a group of order M ---------------- */

#define MAXM 512
#define MAXK 64
#define PERIOD 300000L

static int M, KS;
static int mulT[MAXM][MAXM];
static int invT[MAXM];
static int cnt[MAXM];
static int cost;
static int S[MAXK];
static int inS[MAXM];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

/* Add (dl = +1) or remove (dl = -1) the ordered pair (a, b): contributes a * b^{-1}. */
static void pair_upd(int a, int b, int dl) {
    int g = mulT[a][invT[b]];
    if (dl > 0) {
        if (cnt[g]++ == 0) cost--;
    } else {
        if (--cnt[g] == 0) cost++;
    }
}

/* Replace S[i] by x, updating coverage counts. Cost = number of g != identity not covered. */
static void replace_at(int i, int x) {
    int old = S[i];
    for (int j = 0; j < KS; j++) {
        if (j == i) continue;
        pair_upd(old, S[j], -1);
        pair_upd(S[j], old, -1);
    }
    for (int j = 0; j < KS; j++) {
        if (j == i) continue;
        pair_upd(x, S[j], 1);
        pair_upd(S[j], x, 1);
    }
    inS[old] = 0;
    inS[x] = 1;
    S[i] = x;
}

/* ---------------- Part B: augmentation engine (distance-based vertex addition) ---------------- */

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
            long sc = (long)g * 8 + (long)(rnd() % 8);
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

static int augment_main(int argc, char **argv) {
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

    double t_end = now() + budget;
    int fails = 0;
    while (now() < t_end && N < MAXN - 2 && fails < 4000) {
        int X = (int)(rnd() % 2);
        if (try_add(X)) fails = 0;
        else fails++;
    }

    int M2 = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) M2++;
    printf("%d %d\n", N, M2);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) printf("%d %d\n", v, adj[v][k]);
    return 0;
}

/* ---------------- main: mode "cover" (args m k2 r KS seed budget) or "augment" ---------------- */

int main(int argc, char **argv) {
    if (argc < 2) return 1;
    if (strcmp(argv[1], "augment") == 0) {
        /* argv: augment d D seed budget (graph on stdin) */
        char *nargv[8];
        nargv[0] = argv[0];
        for (int i = 2; i < argc && i < 6; i++) nargv[i - 1] = argv[i];
        return augment_main(argc - 1, nargv);
    }
    if (argc < 7) {
        printf("FAIL\n");
        return 0;
    }
    int m = atoi(argv[1]);
    int k2 = atoi(argv[2]);
    long long r = atoll(argv[3]);
    KS = atoi(argv[4]);
    uint64_t seed = (uint64_t)strtoull(argv[5], NULL, 10);
    double budget = atof(argv[6]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 99991ULL;
    if (rs == 0) rs = 1;
    if (m < 2 || k2 < 1) {
        printf("FAIL\n");
        return 0;
    }
    M = m * k2;
    if (M > MAXM || KS < 2 || KS > MAXK || KS >= M) {
        printf("FAIL\n");
        return 0;
    }
    r %= m;
    if (r < 0) r += m;
    long long pw[MAXM];
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (pw[b - 1] * r) % m;
    if ((pw[k2 - 1] * r) % m != 1 % m) {
        printf("FAIL\n");
        return 0;
    }
    /* Element (a, b) is coded a*k2 + b; (a,b)(c,d) = (a + r^b c, b + d). Identity is 0. */
    for (int x = 0; x < M; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < M; y++) {
            int c = y / k2, d = y % k2;
            long long A = (a + pw[b] * c) % m;
            mulT[x][y] = (int)(A * k2 + (b + d) % k2);
        }
    }
    for (int x = 0; x < M; x++) {
        invT[x] = -1;
        for (int y = 0; y < M; y++)
            if (mulT[x][y] == 0) {
                invT[x] = y;
                break;
            }
        if (invT[x] < 0) {
            printf("FAIL\n");
            return 0;
        }
    }

    memset(inS, 0, sizeof(inS));
    memset(cnt, 0, sizeof(cnt));
    cost = M - 1;
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < KS; i++) {
        int x;
        do {
            x = (int)(rnd() % (uint64_t)M);
        } while (inS[x]);
        S[i] = x;
        inS[x] = 1;
    }
    for (int i = 0; i < KS; i++)
        for (int j = 0; j < KS; j++)
            if (i != j) pair_upd(S[i], S[j], 1);

    double t_end = now() + budget;
    const double T0 = 1.2, T1 = 0.08;
    double T = T0;
    long iter = 0;
    while (cost > 0) {
        if ((iter & 1023) == 0) {
            if (now() > t_end) break;
            T = T0 * pow(T1 / T0, (double)(iter % PERIOD) / (double)PERIOD);
        }
        iter++;
        int i = 1 + (int)(rnd() % (uint64_t)(KS - 1));
        int x;
        do {
            x = (int)(rnd() % (uint64_t)M);
        } while (inS[x]);
        int old = S[i];
        int before = cost;
        replace_at(i, x);
        int dl = cost - before;
        if (dl > 0 && urand() >= exp(-(double)dl / T)) replace_at(i, old);
    }

    if (cost == 0) {
        printf("OK");
        for (int i = 0; i < KS; i++) printf(" %d", S[i]);
        printf("\n");
    } else {
        printf("FAIL\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Haar graphs from difference covers (diameter 3, bipartite, d-regular).
# ----------------------------------------------------------------------------

def _group_params(M, cap=4):
    """Candidate groups of order M as (k2, r): Z_{M/k2} x|_r Z_k2. Cyclic group first."""
    out = [(1, 1)]
    for k2 in range(2, M + 1):
        if M % k2 or M // k2 < 2:
            continue
        m = M // k2
        picked = []
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                picked.append(r)
                if len(picked) >= 2:
                    break
        for r in picked:
            out.append((k2, r))
    return out[:cap]


def _haar_edges(m, k2, r, S):
    """Haar graph of the group Z_m x|_r Z_k2 (order m*k2) with connection set S."""
    order, mul, _inv = lib.semidirect_group(m, k2, r)
    edges = [(g, order + mul(g, s)) for g in range(order) for s in S]
    return 2 * order, edges


def _haar_search(d, lo, hi, deadline, seed):
    """Search difference covers of size d for orders M in [lo, hi] (ascending). Return the largest found graph or None."""
    best = None
    for M in range(lo, hi + 1):
        remaining = deadline - time.monotonic()
        if remaining < 0.2:
            break
        groups = _group_params(M)
        slot = remaining / (hi + 1 - M)
        per = max(0.08, slot / len(groups))
        for gi, (k2, r) in enumerate(groups):
            remaining = deadline - time.monotonic()
            if remaining < 0.1:
                break
            budget = min(per, remaining)
            m = M // k2
            try:
                text = lib.run_c(C_SOURCE, [m, k2, r, d, seed * 100003 + M * 131 + gi, f"{budget:.3f}"],
                                 timeout=budget + 5.0)
            except Exception:
                continue
            toks = text.split()
            if len(toks) == d + 1 and toks[0] == "OK":
                S = [int(t) for t in toks[1:]]
                best = (M, k2, r, S)
                break
    if best is None:
        return None
    M, k2, r, S = best
    return _haar_edges(M // k2, k2, r, S)


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
# C augmentation driver.
# ----------------------------------------------------------------------------

def _augment(n0, e0, d, D, seed, budget, timeout):
    """Run the C augmentation engine from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, ["augment", d, D, seed, f"{budget:.2f}"],
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

    # New construction for D = 3: difference-cover Haar graphs of order above the current best.
    if D == 3 and d >= 3:
        lo = best[0] // 2 + 1
        hi = d * d - d + 1
        if lo <= hi:
            got = None
            try:
                got = _haar_search(d, lo, hi, t0 + 0.65 * time_limit, seed)
            except Exception:
                got = None
            if got is not None and got[0] > best[0] and lib.is_valid(got[0], got[1], d, D):
                best = got

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
            n1, e1 = _augment(src[0], src[1], d, D, seed * 31 + idx,
                              max(0.3, share - 1.0), share + 3.0)
        except Exception:
            continue
        if n1 > best[0] and lib.is_valid(n1, e1, d, D):
            best = (n1, e1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
