import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: greedy vertex insertion with ball-cover certificates (unchanged).
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
# C engine 2 (new): fixed-order annealing on bad pairs.
# State: a bipartite simple graph on n fixed vertices with max degree d.
# Moves: degree-preserving edge swaps across the colour classes, plus greedy
# addition of spare cross edges (monotone, never hurts). Cost = number of
# unordered pairs at distance > D. Stops as soon as the cost is zero.
# ----------------------------------------------------------------------------

C_SA = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXM 100000
#define MAXD 64
#define MAXW (MAXN / 64)

static int n, m, d, D, W;
static int ea[MAXM], eb[MAXM];
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static int ru[MAXM], rv[MAXM];

static uint32_t rnd32(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 32);
}

static double u01(void) {
    return (double)rnd32() / 4294967296.0;
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void build_adj(void) {
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int e = 0; e < m; e++) {
        int a = ea[e], b = eb[e];
        adj[a][deg[a]++] = b;
        adj[b][deg[b]++] = a;
    }
}

static long eval_cost(void) {
    W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) reach[v][w] = 0;
        reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
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
    long unc = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(reach[v][w]);
        unc += n - c;
    }
    return unc / 2;
}

static void add_edge_raw(int a, int b) {
    ea[m] = a;
    eb[m] = b;
    m++;
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static int greedy_add(void) {
    static int A[MAXN], B[MAXN];
    int na = 0, nb = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] >= d) continue;
        if (col[v] == 0) A[na++] = v; else B[nb++] = v;
    }
    if (na == 0 || nb == 0) return 0;
    for (int i = nb - 1; i > 0; i--) {
        int j = (int)(rnd32() % (uint32_t)(i + 1));
        int t = B[i]; B[i] = B[j]; B[j] = t;
    }
    int added = 0;
    for (int i = 0; i < na; i++) {
        int a = A[i];
        int off = (int)(rnd32() % (uint32_t)nb);
        for (int k = 0; k < nb && deg[a] < d; k++) {
            int b = B[(off + k) % nb];
            if (deg[b] >= d || m >= MAXM) continue;
            if (has_edge(a, b)) continue;
            add_edge_raw(a, b);
            added++;
        }
    }
    return added;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd32();

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2) { printf("0 0\n"); return 0; }
    if (N0 < 1 || N0 > MAXN) { printf("0 0\n"); return 0; }
    n = N0;

    /* read, dedupe and degree-cap the input into a scratch graph */
    int k = 0;
    for (int i = 0; i < M0 && k < MAXM; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
        ru[k] = u;
        rv[k] = v;
        k++;
    }

    /* 2-colour the kept graph; an odd cycle means the input is unusable */
    static int q[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int u = q[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[u][i];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    q[qt++] = w;
                }
            }
        }
    }
    for (int i = 0; i < k; i++)
        if (col[ru[i]] == col[rv[i]]) { printf("0 0\n"); return 0; }

    m = 0;
    for (int i = 0; i < k; i++) {
        if (col[ru[i]] == 0) { ea[m] = ru[i]; eb[m] = rv[i]; }
        else                 { ea[m] = rv[i]; eb[m] = ru[i]; }
        m++;
    }
    build_adj();
    greedy_add();

    long cur = eval_cost();
    clock_t t0 = clock();
    const double T0 = 1.0, T1 = 0.03;
    long iter = 0;
    while (cur > 0 && m >= 2) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (el > budget) break;
        iter++;
        double frac = el / budget;
        if (frac > 1.0) frac = 1.0;
        double T = T0 * pow(T1 / T0, frac);

        if (iter % 50 == 0) {
            int before = m;
            greedy_add();
            if (m != before) { cur = eval_cost(); continue; }
        }

        int i = (int)(rnd32() % (uint32_t)m);
        int j = (int)(rnd32() % (uint32_t)m);
        if (i == j) continue;
        int a1 = ea[i], b1 = eb[i], a2 = ea[j], b2 = eb[j];
        if (a1 == a2 || b1 == b2) continue;
        if (has_edge(a1, b2) || has_edge(a2, b1)) continue;

        eb[i] = b2;
        eb[j] = b1;
        build_adj();
        long c2 = eval_cost();
        long delta = c2 - cur;
        if (delta <= 0 || u01() < exp(-(double)delta / T)) {
            cur = c2;
        } else {
            eb[i] = b1;
            eb[j] = b2;
            build_adj();
        }
    }

    if (cur != 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", n, m);
    for (int e = 0; e < m; e++) printf("%d %d\n", ea[e], eb[e]);
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
# Arc-extended projective plane incidence graphs (diameter 3), unchanged.
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
    """True if every target is hit by <= s elements of S, where element x hits nbr[x]."""
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
# Generalized quadrangle baseline (D = 4), unchanged.
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
# New construction: PG(2, Q) with Q the smallest prime power >= d.
# Its incidence graph has degree Q+1 > d. Remove random vertices to reach a
# target order, cut all degrees down to d, then let C_SA anneal the bad-pair
# count to zero at that fixed order.
# ----------------------------------------------------------------------------

def _smallest_pp_at_least(x):
    """Smallest prime power q >= max(2, x)."""
    q = max(2, x)
    while not lib.is_prime_power(q):
        q += 1
    return q


def _pg_start(Q, n_target, d, seed):
    """PG(2,Q) incidence with random vertices removed to leave n_target, degrees cut to <= d."""
    n2, edges = lib.projective_plane_incidence(Q)
    m = n2 // 2
    k = n2 - n_target
    if k < 0:
        return None
    rng = random.Random(seed)
    kp = k // 2
    removed = set(rng.sample(range(m), kp)) | set(rng.sample(range(m, n2), k - kp))
    alive = [v for v in range(n2) if v not in removed]
    idx = {v: i for i, v in enumerate(alive)}
    E = [(idx[u], idx[v]) for u, v in edges if u in idx and v in idx]
    deg = [0] * len(alive)
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    rng.shuffle(E)
    keep = []
    for u, v in E:
        if deg[u] > d or deg[v] > d:
            deg[u] -= 1
            deg[v] -= 1
        else:
            keep.append((u, v))
    return len(alive), keep


def _sa_extend(d, D, Q, n_target, seed, budget):
    """Anneal a PG-derived start of order n_target to a valid graph; None on failure."""
    st = _pg_start(Q, n_target, d, seed)
    if st is None:
        return None
    n, E = st
    out = lib.run_c(C_SA, [d, D, seed, round(budget, 2)],
                    stdin_graph=(n, E), timeout=budget + 5.0)
    n2, e2 = lib.parse_graph_text(out)
    if n2 < 1:
        return None
    if not lib.is_valid(n2, e2, d, D):
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Driver. Time plan (fractions of time_limit):
#   0.00-0.08  arc-extended PG graphs
#   0.00-0.15  generalized quadrangle baseline (D >= 4 only)
#   0.15-0.72  PG-derived annealing at increasing target orders (stop on failure)
#   end        short insertion pass on the best graph
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

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

    if D >= 3:
        arcs = _arc_extensions(d, start + 0.08 * time_limit,
                               random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for g in arcs:
            consider(g)

    if D >= 4 and elapsed() < 0.15 * time_limit:
        consider(_best_gq(d))

    if D >= 3:
        Q = _smallest_pp_at_least(d)
        n_full = 2 * (Q * Q + Q + 1)
        hi = min(n_full, lib.moore_bound(d, D))
        lo = best_n + 1
        if Q <= 30 and hi >= lo:
            sa_deadline = 0.72 * time_limit
            targets = sorted({lo + (hi - lo) * i // 4 for i in range(1, 5)})
            for t in targets:
                remaining = sa_deadline - elapsed()
                if remaining < 2.0:
                    break
                sa_budget = min(0.22 * time_limit, remaining)
                try:
                    g = _sa_extend(d, D, Q, t, seed * 1000 + t, sa_budget)
                except Exception:
                    g = None
                if g is None:
                    break
                consider(g)
                if best_n < t:
                    break

    if D >= 3 and best_n > 0:
        rem = min(0.08 * time_limit, 0.86 * time_limit - elapsed() - 5.0)
        if rem >= 1.0:
            consider(_c_augment(best, d, D, seed + 1, rem))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
