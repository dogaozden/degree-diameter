import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine A: cyclic Haar graphs from difference covers.
#
# The Haar graph of Z_m with connection set S (|S| = d) joins a_i to b_{i+s}.
# It is d-regular and bipartite. For D = 3 it has diameter <= 3 exactly when
# S - S = Z_m, which needs m <= d^2 - d + 1 (the bipartite Moore bound is
# 2(d^2 - d + 1)). The search is simulated annealing on the number of nonzero
# residues not covered by S - S, with incremental difference counts.
# For D != 3 the cost is the number of vertices not within distance D of a_0
# or b_0. By translation symmetry this decides the diameter.
# Output: the Haar graph in lib text format, or "0 0".
# ----------------------------------------------------------------------------

C_HAAR = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 4096
#define MAXK 64

static int K, M, D;
static int S[MAXK], bestS[MAXK];
static int inS[MAXM];
static int cnt[MAXM];
static int zeros;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu(void) { return (double)clock() / CLOCKS_PER_SEC; }
static int modm(int x) { x %= M; if (x < 0) x += M; return x; }

static void random_init(void) {
    memset(inS, 0, sizeof(int) * M);
    for (int i = 0; i < K; ) {
        int x = rndi(M);
        if (!inS[x]) { inS[x] = 1; S[i++] = x; }
    }
}

static void bump(int r, int dlt) {
    if (r == 0) return;
    if (dlt > 0) {
        if (cnt[r] == 0) zeros--;
        cnt[r]++;
    } else {
        cnt[r]--;
        if (cnt[r] == 0) zeros++;
    }
}

static void touch(int i, int dlt) {
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        bump(modm(S[i] - S[j]), dlt);
        bump(modm(S[j] - S[i]), dlt);
    }
}

static void init_counts(void) {
    memset(cnt, 0, sizeof(int) * M);
    zeros = M - 1;
    for (int i = 0; i < K; i++)
        for (int j = 0; j < i; j++) {
            bump(modm(S[i] - S[j]), 1);
            bump(modm(S[j] - S[i]), 1);
        }
}

static int diff_search(double seconds) {
    double t0 = cpu();
    long it = 0;
    const long L = 300000;
    while (1) {
        random_init();
        init_counts();
        if (zeros == 0) { memcpy(bestS, S, sizeof(int) * K); return 1; }
        for (long r = 0; r < L; r++, it++) {
            if ((it & 4095) == 0 && cpu() - t0 > seconds) return 0;
            int i = rndi(K);
            int a = S[i];
            int x;
            do { x = rndi(M); } while (inS[x]);
            int old = zeros;
            touch(i, -1);
            inS[a] = 0; S[i] = x; inS[x] = 1;
            touch(i, 1);
            int delta = zeros - old;
            if (delta <= 0 || rndu() < exp(-delta / 0.4)) {
                if (zeros == 0) { memcpy(bestS, S, sizeof(int) * K); return 1; }
            } else {
                touch(i, -1);
                inS[x] = 0; S[i] = a; inS[a] = 1;
                touch(i, 1);
            }
        }
    }
}

static int ball_missing(void) {
    static int dist[2 * MAXM];
    static int q[2 * MAXM];
    int missing = 0;
    for (int src = 0; src < 2; src++) {
        int s0 = (src == 0) ? 0 : M;
        for (int v = 0; v < 2 * M; v++) dist[v] = -1;
        int qh = 0, qt = 0, reached = 1;
        q[qt++] = s0;
        dist[s0] = 0;
        while (qh < qt) {
            int u = q[qh++];
            if (dist[u] >= D) continue;
            if (u < M) {
                for (int t = 0; t < K; t++) {
                    int v = M + modm(u + S[t]);
                    if (dist[v] < 0) { dist[v] = dist[u] + 1; q[qt++] = v; reached++; }
                }
            } else {
                int j = u - M;
                for (int t = 0; t < K; t++) {
                    int v = modm(j - S[t]);
                    if (dist[v] < 0) { dist[v] = dist[u] + 1; q[qt++] = v; reached++; }
                }
            }
        }
        missing += 2 * M - reached;
    }
    return missing;
}

static int gen_search(double seconds) {
    double t0 = cpu();
    long it = 0;
    const long L = 20000;
    while (1) {
        random_init();
        int cost = ball_missing();
        if (cost == 0) { memcpy(bestS, S, sizeof(int) * K); return 1; }
        for (long r = 0; r < L; r++, it++) {
            if (cpu() - t0 > seconds) return 0;
            int i = rndi(K);
            int a = S[i];
            int x;
            do { x = rndi(M); } while (inS[x]);
            inS[a] = 0; S[i] = x; inS[x] = 1;
            int c2 = ball_missing();
            int delta = c2 - cost;
            if (delta <= 0 || rndu() < exp(-delta / 0.6)) {
                cost = c2;
                if (cost == 0) { memcpy(bestS, S, sizeof(int) * K); return 1; }
            } else {
                inS[x] = 0; S[i] = a; inS[a] = 1;
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    K = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int cap = atoi(argv[5]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    if (K < 1 || K > MAXK || D < 2) { printf("0 0\n"); return 0; }
    if (cap > MAXM - 1) cap = MAXM - 1;

    double t0 = cpu();
    int lo = K;
    if (D == 3 && cap / 2 > lo) lo = cap / 2;
    int bestM = 0, fails = 0;
    for (M = lo; M <= cap; M++) {
        double rem = budget - (cpu() - t0);
        if (rem < 0.05) break;
        double att = rem < 3.0 ? rem : 3.0;
        int ok = (D == 3) ? diff_search(att) : gen_search(att);
        if (ok) {
            bestM = M;
            memcpy(bestS, bestS, sizeof(int) * K);
            fails = 0;
        } else if (bestM) {
            if (++fails >= 3) break;
        }
    }
    if (!bestM) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * bestM, bestM * K);
    for (int i = 0; i < bestM; i++)
        for (int t = 0; t < K; t++)
            printf("%d %d\n", i, bestM + (i + bestS[t]) % bestM);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine B: greedy vertex insertion with ball-cover certificates (from the
# previous generation). Used as a final polish on the best graph found.
# ----------------------------------------------------------------------------

C_INSERT = r"""
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
    int cand[MAXN];
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
    const int maxfails = 200;
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


def _c_haar(d, D, seed, budget, cap):
    """Run the difference-cover Haar search; return (n, edges) or None."""
    if budget < 0.5 or d > 64:
        return None
    try:
        out = lib.run_c(C_HAAR, [d, D, seed, round(budget, 2), cap],
                        stdin_graph=None, timeout=budget + 5.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    return n2, e2


def _c_augment(graph, d, D, seed, budget):
    """Run the C insertion engine on graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 0.5 or d > 64:
        return None
    try:
        out = lib.run_c(C_INSERT, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 5.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), kept as a
# Python-side candidate so the output never falls below the previous level.
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


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice so that every target is hit <= s times."""
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


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
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
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
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

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


def _pg_fallback(d):
    """Plain PG(2, q) incidence graph with q the largest prime power <= d - 1 (diameter 3, degree q + 1)."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ----------------------------------------------------------------------------
# Driver.
#   0.00-0.05  arc-extended PG graphs and PG(2, q) fallback (D = 3)
#   0.05-0.60  cyclic Haar graphs from difference covers (new main search)
#   0.60-0.80  C insertion polish on the best graph so far
# Every candidate is checked with lib.is_valid before it can replace the best.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def elapsed():
        return time.monotonic() - start

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
        rng = random.Random(seed * 7919 + d)
        for g in _arc_extensions(d, start + 0.05 * time_limit, rng):
            consider(g)
        consider(_pg_fallback(d))

    if d <= 64:
        cap = min(lib.moore_bound(d, D) // 2, 4000)
        budget = 0.55 * time_limit - elapsed()
        if budget > 0.5:
            consider(_c_haar(d, D, seed, budget, cap))

    if D >= 3:
        budget = 0.80 * time_limit - elapsed() - 0.5
        if budget > 0.5:
            consider(_c_augment(best, d, D, seed + 1, budget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
