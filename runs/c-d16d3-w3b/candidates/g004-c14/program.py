import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine A: greedy vertex insertion with ball-cover certificates (diameter D).
# Adds vertices and cross edges only; old distances never increase.
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


# ----------------------------------------------------------------------------
# C engine B (new, bold): cyclic difference covers -> Haar graphs.
#
# Haar graph H(Z_m, S): a_i ~ b_{i+s} for s in S, |S| = d, so it is d-regular
# on 2m vertices. If S - S = Z_m, every two same-side vertices are at distance
# <= 2 and every a-b pair at distance <= 3, so H has diameter 3. Hence any
# d-element difference cover of Z_m gives a valid graph of order 2m.
# Upper bound m <= d^2 - d + 1 (Moore-type). This engine searches for covers
# of increasing m by simulated annealing on the number of uncovered residues,
# with targeted moves that cover a random uncovered residue.
# Output: "m k" then the k elements of S (or "0 0").
# ----------------------------------------------------------------------------

DIFF_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXK 64
#define MAXM 1024

static int k, m;
static int S[MAXK];
static int inS[MAXM];
static int cnt[MAXM];
static int uncov;
static uint64_t rs = 88172645463325252ULL;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 32);
}

static double rndu(void) { return (rnd() >> 8) / 16777216.0; }

static int md(int x) {
    x %= m;
    if (x < 0) x += m;
    return x;
}

static void random_set(void) {
    for (int i = 0; i < k;) {
        int v = (int)(rnd() % (uint32_t)m);
        int dup = 0;
        for (int j = 0; j < i; j++) if (S[j] == v) { dup = 1; break; }
        if (!dup) S[i++] = v;
    }
}

static void full_init(void) {
    memset(cnt, 0, sizeof(int) * m);
    memset(inS, 0, sizeof(int) * m);
    uncov = m - 1;
    for (int i = 0; i < k; i++)
        for (int j = i + 1; j < k; j++) {
            int x = md(S[i] - S[j]);
            if (cnt[x]++ == 0) uncov--;
            x = md(S[j] - S[i]);
            if (cnt[x]++ == 0) uncov--;
        }
    for (int i = 0; i < k; i++) inS[S[i]] = 1;
}

static void remove_el(int i) {
    int s = S[i];
    for (int j = 0; j < k; j++) {
        if (j == i) continue;
        int t = S[j];
        int x = md(s - t);
        if (--cnt[x] == 0) uncov++;
        x = md(t - s);
        if (--cnt[x] == 0) uncov++;
    }
    inS[s] = 0;
}

static void add_el(int i, int v) {
    for (int j = 0; j < k; j++) {
        if (j == i) continue;
        int t = S[j];
        int x = md(v - t);
        if (cnt[x]++ == 0) uncov--;
        x = md(t - v);
        if (cnt[x]++ == 0) uncov--;
    }
    S[i] = v;
    inS[v] = 1;
}

static int find_uncov(void) {
    int start = (int)(rnd() % (uint32_t)m);
    for (int q = 0; q < m; q++) {
        int x = start + q;
        if (x >= m) x -= m;
        if (x != 0 && cnt[x] == 0) return x;
    }
    return -1;
}

static void anneal(long iters) {
    const double T0 = 1.0, T1 = 0.08;
    double T = T0;
    for (long it = 0; it < iters && uncov > 0; it++) {
        if ((it & 1023) == 0) T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int i, v;
        if (rndu() < 0.7) {
            int x = find_uncov();
            if (x < 0) break;
            int j = (int)(rnd() % (uint32_t)k);
            int t = S[j];
            v = (rnd() & 1u) ? md(t + x) : md(t - x);
            if (inS[v]) continue;
            i = (int)(rnd() % (uint32_t)(k - 1));
            if (i >= j) i++;
        } else {
            i = (int)(rnd() % (uint32_t)k);
            do { v = (int)(rnd() % (uint32_t)m); } while (inS[v]);
        }
        int old_u = uncov;
        int s = S[i];
        remove_el(i);
        add_el(i, v);
        int delta = uncov - old_u;
        if (delta > 0 && rndu() >= exp(-delta / T)) {
            remove_el(i);
            add_el(i, s);
        }
    }
}

static int attempt(double slice, int *outS) {
    clock_t c0 = clock();
    int ok = 0;
    while ((double)(clock() - c0) / CLOCKS_PER_SEC < slice) {
        random_set();
        full_init();
        if (uncov == 0) { ok = 1; break; }
        anneal(300000);
        if (uncov == 0) { ok = 1; break; }
    }
    if (!ok) return 0;
    memcpy(outS, S, sizeof(int) * k);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    k = atoi(argv[1]);
    int mlo = atoi(argv[2]);
    int mhi = atoi(argv[3]);
    unsigned long seed = strtoul(argv[4], NULL, 10);
    double budget = atof(argv[5]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    if (k < 2 || k > MAXK) { printf("0 0\n"); return 0; }
    if (mhi > MAXM - 1) mhi = MAXM - 1;

    clock_t t0 = clock();
    int bestm = 0;
    int bestS[MAXK];
    for (int mm = (mlo < k ? k : mlo); mm <= mhi; mm++) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        double rem = budget - el;
        if (rem <= 0.05) break;
        m = mm;
        int out[MAXK];
        if (!attempt(0.5 * rem, out)) break;
        bestm = mm;
        memcpy(bestS, out, sizeof(int) * k);
    }
    if (bestm == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestm, k);
    for (int i = 0; i < k; i++) printf("%d%c", bestS[i], i + 1 < k ? ' ' : '\n');
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


def _diff_haar(d, seed, m_lo, m_hi, budget):
    """Run the difference-cover engine; return the Haar graph H(Z_m, S) or None."""
    if budget < 0.5 or d < 2 or m_hi < m_lo:
        return None
    try:
        out = lib.run_c(DIFF_SOURCE, [d, m_lo, m_hi, seed, round(budget, 2)],
                        timeout=budget + 5.0)
        nums = out.split()
        if len(nums) < 2:
            return None
        m, k = int(nums[0]), int(nums[1])
        if m < 1 or k != d or len(nums) < 2 + k:
            return None
        S = [int(x) for x in nums[2:2 + k]]
        return lib.haar_graph(m, S)
    except Exception:
        return None


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), kept as the
# baseline and as the source graph for the insertion engine.
#
# Start from PG(2, q) incidence (every vertex has degree q+1). With s = d-q-1
# spare degree, add an A-vertex per point in SA (joined to its q+1 lines) and
# a B-vertex per line in SB (joined to its q+1 points), with load <= s on each
# line/point. Diameter stays 3.
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
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy for the load-constrained set problem."""
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
    """Plateau/improvement local search for the load-constrained set problem."""
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
# Driver.
#   D = 2:  K_{d,d} is optimal (2d vertices).
#   D = 3:  arc-extended PG graph (0.00-0.15), insertion on it (to 0.25),
#           then cyclic difference-cover Haar search (to 0.90). The largest
#           valid graph wins. K_{d,d} is the fallback.
#   D >= 4: K_{d,d} plus insertion (no tuned constructions in this version).
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

    if D == 2:
        return best

    if D == 3:
        cands = _arc_extensions(d, start + 0.15 * time_limit,
                                random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        arc_graph = None
        for g in cands[:4]:
            if lib.is_valid(g[0], g[1], d, D):
                if arc_graph is None or g[0] > arc_graph[0]:
                    arc_graph = g
        consider(arc_graph)

        budget = 0.25 * time_limit - el()
        if arc_graph is not None and budget >= 0.5:
            consider(_c_augment(arc_graph, d, D, seed, budget))

        # New construction: Haar graph over Z_m with a d-element difference cover.
        # Valid for every m in [m_lo, m_hi]; the search stops at the first failure.
        m_hi = d * d - d + 1
        m_lo = max(d, int(0.6 * m_hi))
        budget = 0.90 * time_limit - el()
        if budget >= 0.5:
            consider(_diff_haar(d, seed + 1, m_lo, m_hi, budget))
        return best

    # D >= 4
    budget = 0.85 * time_limit - el()
    consider(_c_augment(best, d, D, seed, budget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
