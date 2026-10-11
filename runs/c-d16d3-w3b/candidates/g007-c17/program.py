import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# NEW for D = 3: bi-Cayley (Haar-type) graphs from difference covers.
#
# Pick a finite group G of order N and a set S of d elements. Put a_g ~ b_{gs}
# for s in S. The graph has 2N vertices, is d-regular and bipartite, and has
# diameter 3 exactly when S S^{-1} = G and S^{-1} S = G (a difference-cover
# condition). The C engine searches for such S by annealing on the number of
# uncovered group elements. Groups are Z_m x| Z_k (lib.semidirect_group), so
# the search covers cyclic and non-abelian groups alike.
# The search raises N from about 3/4 of the Moore-type limit d^2-d+1 until it fails.
# The older arc-extended projective plane construction stays as a fallback.
# ----------------------------------------------------------------------------

DIFF_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 512
#define MAXS 64

static int N, M, K, R, d;
static int mul[MAXG][MAXG];
static int invv[MAXG];
static int pw[MAXG];
static int S[MAXS];
static int cnt1[MAXG], cnt2[MAXG];
static int uncov;
static uint64_t rs = 88172645463325252ULL;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double urand(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static int rint_(int n) {
    return (int)(nextr() % (uint64_t)n);
}

/* Add (sg=+1) or remove (sg=-1) the ordered pair (a,b) from both cover counters. */
static void addpair(int a, int b, int sg) {
    int x = mul[a][invv[b]];
    int y = mul[invv[a]][b];
    if (sg > 0) {
        if (cnt1[x]++ == 0) uncov--;
        if (cnt2[y]++ == 0) uncov--;
    } else {
        if (--cnt1[x] == 0) uncov++;
        if (--cnt2[y] == 0) uncov++;
    }
}

static void replace_at(int p, int g) {
    int old = S[p];
    for (int j = 0; j < d; j++) {
        if (j == p) addpair(old, old, -1);
        else { addpair(old, S[j], -1); addpair(S[j], old, -1); }
    }
    S[p] = g;
    for (int j = 0; j < d; j++) {
        if (j == p) addpair(g, g, 1);
        else { addpair(g, S[j], 1); addpair(S[j], g, 1); }
    }
}

int main(int argc, char **argv) {
    if (argc < 7) { printf("FAIL\n"); return 0; }
    M = atoi(argv[1]);
    K = atoi(argv[2]);
    R = atoi(argv[3]);
    d = atoi(argv[4]);
    unsigned long seed = strtoul(argv[5], NULL, 10);
    double budget = atof(argv[6]);
    N = M * K;
    if (M < 2 || K < 1 || N > MAXG || d < 1 || d > MAXS || d > N) { printf("FAIL\n"); return 0; }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;

    pw[0] = 1 % M;
    for (int b = 1; b < K; b++) pw[b] = (int)(((long)pw[b - 1] * R) % M);

    /* Group Z_M x|_R Z_K, element (a,b) coded as a*K+b, same as lib.semidirect_group. */
    for (int x = 0; x < N; x++) {
        int a = x / K, b = x % K;
        for (int y = 0; y < N; y++) {
            int c = y / K, e = y % K;
            long t = ((long)a + (long)pw[b] * c) % M;
            mul[x][y] = (int)(t * K + (b + e) % K);
        }
    }
    for (int x = 0; x < N; x++) {
        int a = x / K, b = x % K;
        int nb = (K - b) % K;
        long t = ((long)pw[nb] * a) % M;
        long ia = (M - t) % M;
        invv[x] = (int)(ia * K + nb);
    }

    clock_t t0 = clock();
    int status = 0;  /* 0 searching, 1 found, 2 timeout */
    long iters = 0;
    const long STALL = 60000;

    while (status == 0) {
        memset(cnt1, 0, sizeof(int) * N);
        memset(cnt2, 0, sizeof(int) * N);
        uncov = 2 * N;
        for (int i = 0; i < d; i++) {
            int g, ok;
            do {
                g = rint_(N);
                ok = 1;
                for (int j = 0; j < i; j++) if (S[j] == g) { ok = 0; break; }
            } while (!ok);
            S[i] = g;
        }
        for (int i = 0; i < d; i++)
            for (int j = 0; j < d; j++)
                addpair(S[i], S[j], 1);

        double T = 0.1 + 0.7 * urand();
        int bestloc = uncov;
        long stall = 0;

        while (status == 0) {
            if (uncov == 0) { status = 1; break; }
            iters++;
            if ((iters & 4095) == 0 &&
                (double)(clock() - t0) / CLOCKS_PER_SEC > budget) {
                status = 2;
                break;
            }
            if (++stall > STALL) break;
            int p = rint_(d);
            int g = rint_(N);
            int dup = 0;
            for (int j = 0; j < d; j++) if (S[j] == g) { dup = 1; break; }
            if (dup) continue;
            int old = S[p];
            int before = uncov;
            replace_at(p, g);
            int delta = uncov - before;
            if (delta <= 0 || urand() < exp(-(double)delta / T)) {
                if (uncov < bestloc) { bestloc = uncov; stall = 0; }
            } else {
                replace_at(p, old);
            }
        }
    }

    if (status == 1) {
        printf("OK\n");
        for (int i = 0; i < d; i++) printf("%d ", S[i]);
        printf("\n");
    } else {
        printf("FAIL\n");
    }
    return 0;
}
"""


def _group_options(N, rng):
    """Candidate groups of order N as (m, K, r): the cyclic group first, then semidirect products."""
    opts = [(N, 1, 1)]
    extra = []
    for K in range(2, 13):
        if N % K:
            continue
        m = N // K
        if m < 2:
            continue
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, K, m) == 1 % m]
        if not cands:
            continue
        picks = []
        for r in (1, m - 1):
            if r in cands and r not in picks:
                picks.append(r)
        rest = [r for r in cands if r not in picks]
        rng.shuffle(rest)
        picks += rest[:2]
        for r in picks:
            extra.append((m, K, r))
    rng.shuffle(extra)
    return opts + extra[:8]


def _c_cover(m, K, r, d, seed, budget):
    """Run the difference-cover engine; return (m, K, r, S) or None."""
    if budget < 0.2:
        return None
    try:
        out = lib.run_c(DIFF_SOURCE, [m, K, r, d, seed, round(budget, 3)],
                        timeout=budget + 5.0)
    except Exception:
        return None
    toks = out.split()
    if len(toks) != d + 1 or toks[0] != "OK":
        return None
    try:
        S = [int(t) for t in toks[1:]]
    except ValueError:
        return None
    if len(set(S)) != d:
        return None
    return (m, K, r, S)


def _cover_search(d, seed, deadline):
    """Raise N while a d-element difference cover exists in some group of order N. Return best valid graph."""
    rng = random.Random(seed * 1009 + 13)
    hi = d * d - d + 1
    N = max(2, hi * 3 // 4)
    best = None
    while N <= hi:
        found = None
        for budget in (0.25, 0.8, 2.0):
            for (m, K, r) in _group_options(N, rng):
                rem = deadline - time.monotonic()
                if rem < 0.5:
                    break
                found = _c_cover(m, K, r, d, rng.randrange(1 << 30),
                                 min(budget, rem - 0.2))
                if found is not None:
                    break
            if found is not None or deadline - time.monotonic() < 0.5:
                break
        if found is None:
            break
        m, K, r, S = found
        order, mul, _ = lib.semidirect_group(m, K, r)
        n = 2 * order
        edges = [(g, order + mul(g, s)) for g in range(order) for s in S]
        if not lib.is_valid(n, edges, d, 3):
            break
        best = (n, edges)
        N += 1
    return best


# ----------------------------------------------------------------------------
# C engine: greedy vertex insertion with ball-cover certificates (diameter D).
#
# Let R = D-1. A new vertex w joined to a set N of opposite-colour vertices is
# within distance D of every old vertex x that lies in the R-ball of some u in N.
# Adding vertices and cross edges never increases old distances, so validity is
# preserved. Each round:
#   1. compute R-balls as bitsets,
#   2. for each colour class, greedily cover all vertices with spare-degree
#      neighbours (randomized tie-breaks) and insert a vertex on success,
#   3. on failure add a random spare cross edge to change the spare pattern.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4096
#define MAXD 64
#define MAXW (MAXN / 64)

static int n, d, D, W;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static int popc(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void compute_balls(int R) {
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) reach[v][w] = 0;
        reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = reach[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= reach[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) reach[v][w] = nxt[v][w];
    }
}

static int covers_all(const uint64_t *cov) {
    for (int w = 0; w < W; w++) {
        uint64_t want;
        if (w < W - 1) {
            want = ~0ULL;
        } else {
            int r = n - 64 * (W - 1);
            want = (r >= 64) ? ~0ULL : ((1ULL << r) - 1);
        }
        if ((cov[w] & want) != want) return 0;
    }
    return 1;
}

static int try_insert(int side) {
    static int cand[MAXN];
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (col[u] == 1 - side && deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = (int)(rnd() % (uint32_t)(i + 1));
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    static int used[MAXN];
    for (int i = 0; i < n; i++) used[i] = 0;
    uint64_t cov[MAXW];
    for (int w = 0; w < W; w++) cov[w] = 0;
    int chosen[MAXD];
    int nch = 0;
    while (nch < d && !covers_all(cov)) {
        int best = -1, bg = 0;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (used[u]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(reach[u][w] & ~cov[w]);
            if (g > bg) { bg = g; best = u; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) cov[w] |= reach[best][w];
    }
    if (!covers_all(cov)) return 0;
    int w = n;
    n++;
    col[w] = side;
    deg[w] = 0;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], w);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2) { printf("0 0\n"); return 0; }
    if (N0 < 1 || N0 > MAXN) { printf("0 0\n"); return 0; }
    n = N0;
    W = (n + 63) >> 6;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    static int queue[MAXN];
    for (int s = 0; s < n; s++) col[s] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    queue[qt++] = v;
                }
            }
        }
    }

    clock_t t0 = clock();
    int fails = 0;
    const int maxfails = 400;
    while (fails < maxfails && n < MAXN) {
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        W = (n + 63) >> 6;
        compute_balls(D - 1);
        int sides[2] = {0, 1};
        if (rnd() & 1u) { sides[0] = 1; sides[1] = 0; }
        int ok = 0;
        for (int k = 0; k < 2 && !ok; k++) ok = try_insert(sides[k]);
        if (ok) { fails = 0; continue; }
        fails++;
        for (int t = 0; t < 50; t++) {
            int u = (int)(rnd() % (uint32_t)n);
            int v = (int)(rnd() % (uint32_t)n);
            if (u == v || col[u] == col[v]) continue;
            if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
            add_edge(u, v);
            break;
        }
    }

    int m2 = 0;
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) m2++;
    printf("%d %d\n", n, m2);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) printf("%d %d\n", u, adj[u][i]);
    return 0;
}
"""


def _c_augment(graph, d, D, seed, budget):
    """Run the C insertion engine on graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 0.5 or d > 64:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 5.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), kept as a fallback.
# ----------------------------------------------------------------------------

_LS_ITERS = 30000


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
    """True if every target is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements x so that every target is hit by <= s chosen elements."""
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


def _local_search(m, s, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the same load-constrained set problem."""
    if s < 1:
        return list(S)
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= s:
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
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
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for q in qs:
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

        SA = _local_search(m, s, point_lines, SA, rng, deadline, _LS_ITERS)
        SB = _local_search(m, s, line_points, SB, rng, deadline, _LS_ITERS)

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
# ----------------------------------------------------------------------------

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
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 4).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Driver.
#   D = 3: arc-extended PG graphs (fallback, up to 0.15), then difference-cover
#          bi-Cayley search until 0.85 of time_limit.
#   D >= 4: GQ baseline, annealed group voltage lifts, then C insertion.
#   D = 2: K_{d,d}.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    def el():
        return time.monotonic() - start

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        arcs = _arc_extensions(d, start + 0.15 * time_limit,
                               random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for g in arcs[:4]:
            consider(g)
        consider(_cover_search(d, seed, start + 0.85 * time_limit))

    elif D >= 4:
        if el() < 0.40 * time_limit:
            consider(_best_gq(d))
        anneal_end = start + 0.70 * time_limit
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < anneal_end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, anneal_end, iters=400)
            if res is not None:
                consider(res)
        rem = 0.88 * time_limit - el()
        if rem >= 0.5:
            consider(_c_augment(best, d, D, seed + 1, rem))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
