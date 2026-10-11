import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold construction: cyclic Haar graphs from difference covers (D = 3).
#
# H(N, S) has parts A = Z_N and B = Z_N, with a_i ~ b_{i+s} for s in S, |S| = d.
# It is bipartite and d-regular on 2N vertices. For diameter 3 it suffices that
#   (1) S - S covers Z_N   (A-A and B-B pairs share a neighbour), and
#   (2) S - S + S covers Z_N (every A-B pair is joined by a path of length 3).
# Counting gives N <= d(d-1)+1, so 2N <= 2(d^2-d+1), the Moore-type ceiling.
# C searches for S by annealing on the number of uncovered residues, for
# increasing N, and prints the largest Haar graph it finds.
# ----------------------------------------------------------------------------

C_HAAR = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 64
#define MAXN 512

static uint64_t rs = 88172645463325252ULL;
static int KK;
static int N;
static int S[MAXK];
static unsigned char inS[MAXN];

static uint64_t rnext(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double urand(void) {
    return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0);
}

static int irand(int m) {
    int r = (int)(urand() * (double)m);
    return r >= m ? m - 1 : r;
}

/* Number of uncovered residues: nonzero r missing from S-S, plus r missing from S-S+S. */
static int cost_of(void) {
    static unsigned char d2[MAXN], d3[MAXN];
    static int list2[MAXN];
    int nl = 0;
    memset(d2, 0, (size_t)N);
    memset(d3, 0, (size_t)N);
    for (int i = 0; i < KK; i++)
        for (int j = 0; j < KK; j++) {
            int r = S[i] - S[j];
            if (r < 0) r += N;
            if (!d2[r]) { d2[r] = 1; list2[nl++] = r; }
        }
    for (int t = 0; t < nl; t++)
        for (int c = 0; c < KK; c++) {
            int r = list2[t] + S[c];
            if (r >= N) r -= N;
            d3[r] = 1;
        }
    int bad = 0;
    for (int r = 0; r < N; r++) {
        if (r > 0 && !d2[r]) bad++;
        if (!d3[r]) bad++;
    }
    return bad;
}

/* Simulated annealing for a valid S in Z_N with |S| = KK, S[0] = 0. */
static int try_N(int n, double seconds) {
    N = n;
    memset(inS, 0, (size_t)N);
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < KK; i++) {
        int v;
        do { v = 1 + irand(N - 1); } while (inS[v]);
        S[i] = v;
        inS[v] = 1;
    }
    int cur = cost_of();
    if (cur == 0) return 1;

    clock_t t0 = clock();
    clock_t dl = t0 + (clock_t)(seconds * CLOCKS_PER_SEC);
    double span = (double)(dl - t0);
    if (span < 1.0) span = 1.0;
    double T = 0.9;
    for (long it = 0; ; it++) {
        if ((it & 255) == 0) {
            clock_t now = clock();
            if (now >= dl) break;
            double frac = (double)(now - t0) / span;
            T = 0.9 * (1.0 - frac) + 0.04;
        }
        int idx = 1 + irand(KK - 1);
        int old = S[idx];
        int v;
        do { v = 1 + irand(N - 1); } while (inS[v]);
        inS[old] = 0;
        inS[v] = 1;
        S[idx] = v;
        int c2 = cost_of();
        int delta = c2 - cur;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            cur = c2;
            if (cur == 0) return 1;
        } else {
            inS[v] = 0;
            inS[old] = 1;
            S[idx] = old;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnext();

    if (D != 3 || d < 2 || d > MAXK) { printf("0 0\n"); return 0; }
    KK = d;
    int nmax = d * (d - 1) + 1;
    if (nmax > MAXN - 1) nmax = MAXN - 1;

    clock_t t0 = clock();
    clock_t end = t0 + (clock_t)(budget * CLOCKS_PER_SEC);
    int n = (int)(0.7 * nmax);
    if (n < d + 1) n = d + 1;

    int bestN = 0;
    int bestS[MAXK];
    while (n <= nmax && clock() < end) {
        int ok = 0;
        for (int att = 0; att < 2 && !ok; att++) {
            double left = (double)(end - clock()) / CLOCKS_PER_SEC;
            if (left <= 0.05) break;
            double slice = left < 3.0 ? left : 3.0;
            ok = try_N(n, slice);
        }
        if (ok) {
            bestN = n;
            memcpy(bestS, S, sizeof(int) * (size_t)KK);
            n++;
        } else if (bestN > 0) {
            break;
        } else {
            n++;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * bestN, bestN * KK);
    for (int i = 0; i < bestN; i++)
        for (int k = 0; k < KK; k++)
            printf("%d %d\n", i, bestN + (i + bestS[k]) % bestN);
    return 0;
}
"""


def _haar_search(d, D, seed, budget):
    """Run the difference-cover search; return (n, edges) or None."""
    if budget < 1.0:
        return None
    try:
        out = lib.run_c(C_HAAR, [d, D, seed, round(budget, 2)], timeout=budget + 3.0)
        n, e = lib.parse_graph_text(out)
    except Exception:
        return None
    if n < 1:
        return None
    return n, e


# ----------------------------------------------------------------------------
# C engine: greedy vertex insertion with ball-cover certificates (augmentation).
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
# Arc-extended projective plane incidence graphs (diameter 3, valid for D >= 3).
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
    """Randomized greedy choice of elements so that every target is hit <= s times."""
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


# ----------------------------------------------------------------------------
# Driver. Time plan (fractions of time_limit):
#   D = 3: 0.00-0.55  cyclic Haar graphs from difference covers (main bet)
#          0.55-0.65  arc-extended PG graphs
#          0.65-0.85  greedy C augmentation of the best graph
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = None

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n < 1:
            return
        if best is not None and n <= best[0]:
            return
        if lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3 and d >= 2:
        try:
            consider(_haar_search(d, D, seed, 0.55 * time_limit))
        except Exception:
            pass

    if D >= 3:
        try:
            arcs = _arc_extensions(d, start + 0.65 * time_limit,
                                   random.Random(seed * 7919 + d))
            arcs.sort(key=lambda t: -t[0])
            for g in arcs:
                consider(g)
        except Exception:
            pass
        rem = 0.85 * time_limit - (time.monotonic() - start)
        if rem >= 0.5:
            base = best if best is not None else lib.haar_graph(d, range(d))
            try:
                consider(_c_augment(base, d, D, seed, rem))
            except Exception:
                pass

    if best is None:
        # K_{d,d} has diameter 2, so it is valid for every D >= 2.
        best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])
    return best

