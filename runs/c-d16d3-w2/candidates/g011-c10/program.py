import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: greedy vertex insertion with ball-cover certificates (from parent).
# Adding a vertex never increases distances between old vertices, so validity
# is preserved. Used to add vertices to the arc-extended PG(2,q) graphs.
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


# ----------------------------------------------------------------------------
# C engine 2 (new): difference-cover Haar graphs.
#
# For an abelian group G (here Z_m1 x Z_m2) and a k-set S with S - S = G, the
# Haar graph a_g ~ b_{g+s} (s in S) is bipartite, k-regular, and has diameter 3.
# Proof sketch: a-to-a distances are <= 2 because every difference is in S-S;
# a-to-b distances are <= 3 because b_j = (j - u) + u with u in S, and j - u is
# a difference; the side-swapping map a_g -> b_{-g} gives b-to-b pairs too.
#
# So the task is: find a k-subset S of G with every nonzero element a
# difference s - t. This is simulated annealing on the number of uncovered
# nonzero differences, with O(k) incremental updates per move.
# Output: "n m" plus edges, or "0 0" if no cover is found in time.
# ----------------------------------------------------------------------------

C_COVER = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 8192
#define MAXK 128

static int m1, m2, G, K;
static int S[MAXK];
static unsigned char in_s[MAXG];
static int cnt[MAXG];
static int uncov;
static uint64_t rs = 88172645463325252ULL;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 11);
}

static double rndu(void) {
    return (double)(rnd() & 0xFFFFFFu) / 16777216.0;
}

static int sub_el(int x, int y) {
    int a1 = x / m2, b1 = x % m2, a2 = y / m2, b2 = y % m2;
    int a = (a1 - a2) % m1; if (a < 0) a += m1;
    int b = (b1 - b2) % m2; if (b < 0) b += m2;
    return a * m2 + b;
}

static int add_el(int x, int y) {
    int a = (x / m2 + y / m2) % m1;
    int b = (x % m2 + y % m2) % m2;
    return a * m2 + b;
}

static void inc(int x) {
    if (cnt[x] == 0) uncov--;
    cnt[x]++;
}

static void dec(int x) {
    cnt[x]--;
    if (cnt[x] == 0) uncov++;
}

static void remove_at(int i) {
    int v = S[i];
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        dec(sub_el(v, S[j]));
        dec(sub_el(S[j], v));
    }
    in_s[v] = 0;
}

static void place_at(int i, int v) {
    S[i] = v;
    in_s[v] = 1;
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        inc(sub_el(v, S[j]));
        inc(sub_el(S[j], v));
    }
}

static void init_state(void) {
    memset(cnt, 0, sizeof(int) * (size_t)G);
    memset(in_s, 0, (size_t)G);
    uncov = G - 1;
    for (int i = 0; i < K; i++) {
        int v;
        do { v = (int)(rnd() % (uint32_t)G); } while (in_s[v]);
        S[i] = v;
        in_s[v] = 1;
    }
    for (int i = 0; i < K; i++)
        for (int j = 0; j < i; j++) {
            inc(sub_el(S[i], S[j]));
            inc(sub_el(S[j], S[i]));
        }
}

static int run_sa(clock_t t_end, long iters) {
    init_state();
    const double T0 = 1.5;
    for (long it = 0; it < iters; it++) {
        if (uncov == 0) return 1;
        if ((it & 4095) == 0 && clock() > t_end) return 0;
        double T = T0 * (1.0 - (double)it / (double)iters) + 0.05;
        int i = (int)(rnd() % (uint32_t)K);
        int y = (int)(rnd() % (uint32_t)G);
        if (in_s[y]) continue;
        int old = S[i];
        int cur = uncov;
        remove_at(i);
        place_at(i, y);
        int delta = uncov - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) continue;
        remove_at(i);
        place_at(i, old);
    }
    return uncov == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    m1 = atoi(argv[2]);
    m2 = atoi(argv[3]);
    unsigned long seed = strtoul(argv[4], NULL, 10);
    double budget = atof(argv[5]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 5; w++) rnd();

    K = d;
    if (m1 < 1 || m2 < 1) { printf("0 0\n"); return 0; }
    G = m1 * m2;
    if (K < 1 || K > MAXK || G > MAXG || G <= K) { printf("0 0\n"); return 0; }

    clock_t t_end = clock() + (clock_t)(budget * (double)CLOCKS_PER_SEC);
    int ok = 0;
    while (!ok && clock() < t_end) {
        ok = run_sa(t_end, 150000L);
    }
    if (!ok) { printf("0 0\n"); return 0; }

    printf("%d %d\n", 2 * G, G * K);
    for (int g = 0; g < G; g++)
        for (int i = 0; i < K; i++)
            printf("%d %d\n", g, G + add_el(g, S[i]));
    return 0;
}
"""


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
# Arc-extended projective plane incidence graphs (diameter 3), from parent.
# Start from PG(2, q) incidence. Each old vertex has degree q+1, spare s = d-q-1.
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
# Difference-cover Haar graphs (new construction).
# ----------------------------------------------------------------------------

def _cover_run(d, D, m1, m2, seed, budget):
    """Run the C cover search for group Z_m1 x Z_m2; return a valid (n, edges) or None."""
    if budget < 0.2:
        return None
    try:
        out = lib.run_c(C_COVER, [d, m1, m2, seed, round(budget, 2)],
                        timeout=budget + 5.0)
        n, e = lib.parse_graph_text(out)
    except Exception:
        return None
    if n < 2 or not e:
        return None
    if not lib.is_valid(n, e, d, D):
        return None
    return n, e


def _cover_try(d, D, G, seed, budget, both):
    """Try cyclic Z_G, and Z_2 x Z_(G/2) when G % 4 == 0 and both is set."""
    types = [(G, 1)]
    if both and G % 4 == 0:
        types.append((2, G // 2))
    for m1, m2 in types:
        g = _cover_run(d, D, m1, m2, seed, budget)
        if g is not None:
            return g
    return None


def _cover_search(d, D, lo, hi, seed, deadline, unit):
    """Find the largest group order G in [lo, hi] admitting a d-element difference cover."""
    best = None
    best_G = 0
    failed = []
    q1 = max(0.15, 0.5 * unit / 60.0)
    G = lo
    while G <= hi:
        if deadline - time.monotonic() < q1 + 0.2:
            break
        g = _cover_try(d, D, G, seed + G, q1, False)
        if g is None:
            failed.append(G)
        else:
            best, best_G = g, G
        G += 1

    # Second pass: spend the remaining time on unresolved orders above the best found.
    pending = [x for x in failed if x > best_G] + list(range(G, hi + 1))
    rounds = 0
    while pending:
        left = deadline - time.monotonic()
        share = left / (len(pending) + 1)
        if share < 0.2:
            break
        Gt = pending.pop(0)
        g = _cover_try(d, D, Gt, seed + 7 * Gt + rounds, share, True)
        rounds += 1
        if g is not None:
            best, best_G = g, Gt
            pending = [x for x in pending if x > Gt]
    return best


# ----------------------------------------------------------------------------
# Driver.
#   0.00-0.06  arc-extended PG graphs
#   0.06-0.22  C insertion on the best arc graph (adds vertices; this is what
#              the previous best came from)
#   0.22-0.80  difference-cover Haar graphs with order above the current best
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + 0.80 * T

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def elapsed():
        return time.monotonic() - start

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    arcs = _arc_extensions(d, start + 0.06 * T, random.Random(seed * 7919 + d))
    for g in sorted(arcs, key=lambda t: -t[0]):
        consider(g)

    ins = 0.22 * T - elapsed()
    if ins >= 0.5:
        consider(_c_augment(best, d, D, seed, ins))

    # Haar graph on an abelian group of order G with a d-element difference cover
    # has 2G vertices and diameter 3. Largest possible G is d(d-1)+1.
    lo = best[0] // 2 + 1
    hi = d * (d - 1) + 1
    if lo <= hi:
        consider(_cover_search(d, D, lo, hi, seed, deadline, T))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
