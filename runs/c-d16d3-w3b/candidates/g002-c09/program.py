import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# NEW (bold): Haar graphs of finite groups with difference covers.
#
# Let G be a group of order N and S a set of d elements containing the identity.
# The bipartite graph with sides A_x, B_y (x, y in G) and edges A_x ~ B_{x s},
# s in S, is d-regular with 2N vertices. A_x reaches A_{x s t^-1} in two steps,
# so if S S^-1 = G then every A-pair is within distance 2 and every A-B pair is
# within distance 3. Diameter 3 therefore needs only a "difference cover" of
# size d in a group of order N. The Moore-type ceiling is N <= d^2 - d + 1.
#
# The C engine below searches for such S by simulated annealing on the number of
# uncovered non-identity elements, for one fixed group Z_m x| Z_k (r^k = 1 mod m).
# It prints the Haar graph on success, or "0 0".
# ----------------------------------------------------------------------------

C_HAAR = r"""
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 320
#define MAXD 64

static int N, d;
static int mt[MAXG][MAXG];
static int invg[MAXG];
static int cnt[MAXG];
static int S[MAXD];
static int inS[MAXG];
static int uncov;
static uint64_t rs = 88172645463325252ULL;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static double urand(void) { return (rnd() & 0xFFFFFFu) / 16777216.0; }

static void build_group(int m, int k, int r) {
    int pw[MAXG];
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (pw[b - 1] * r) % m;
    N = m * k;
    for (int x = 0; x < N; x++) {
        int a1 = x / k, b1 = x % k;
        for (int y = 0; y < N; y++) {
            int a2 = y / k, b2 = y % k;
            int a = (a1 + pw[b1] * a2) % m;
            int b = (b1 + b2) % k;
            mt[x][y] = a * k + b;
        }
    }
    for (int x = 0; x < N; x++) {
        invg[x] = 0;
        for (int y = 0; y < N; y++)
            if (mt[x][y] == 0) { invg[x] = y; break; }
    }
}

/* cnt[g] = number of ordered pairs (s,t), s != t in S, with s t^-1 = g. */
static inline void chg(int g, int delta) {
    if (delta < 0) {
        cnt[g]--;
        if (cnt[g] == 0) uncov++;
    } else {
        if (cnt[g] == 0) uncov--;
        cnt[g]++;
    }
}

static inline void pair_chg(int x, int y, int delta) {
    chg(mt[x][invg[y]], delta);
    chg(mt[y][invg[x]], delta);
}

static void el_chg(int idx, int delta) {
    for (int j = 0; j < d; j++)
        if (j != idx) pair_chg(S[idx], S[j], delta);
}

static void random_init(void) {
    for (int g = 0; g < N; g++) { cnt[g] = 0; inS[g] = 0; }
    uncov = N - 1;
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < d; i++) {
        int y;
        do { y = (int)(rnd() % (uint32_t)N); } while (inS[y]);
        S[i] = y;
        inS[y] = 1;
    }
    for (int i = 0; i < d; i++)
        for (int j = i + 1; j < d; j++)
            pair_chg(S[i], S[j], +1);
}

static int anneal(long iters, double T0, double T1) {
    double T = T0;
    double alpha = pow(T1 / T0, 1.0 / (double)iters);
    for (long it = 0; it < iters; it++) {
        if (uncov == 0) return 1;
        int idx = 1 + (int)(rnd() % (uint32_t)(d - 1));
        int x = S[idx];
        int y;
        do { y = (int)(rnd() % (uint32_t)N); } while (inS[y]);
        int before = uncov;
        el_chg(idx, -1);
        S[idx] = y;
        el_chg(idx, +1);
        int delta = uncov - before;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            inS[x] = 0;
            inS[y] = 1;
        } else {
            el_chg(idx, -1);
            S[idx] = x;
            el_chg(idx, +1);
        }
        T *= alpha;
    }
    return uncov == 0;
}

int main(int argc, char **argv) {
    if (argc < 8) return 1;
    d = atoi(argv[1]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int m = atoi(argv[5]), k = atoi(argv[6]), r = atoi(argv[7]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    if (d < 2 || d > MAXD || m < 1 || k < 1 || m * k >= MAXG || m * k <= d) {
        printf("0 0\n");
        return 0;
    }
    build_group(m, k, r);

    clock_t t0 = clock();
    int found = 0;
    while (!found) {
        double used = (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (used > budget) break;
        random_init();
        found = anneal(150000, 1.2, 0.08);
    }
    if (!found || uncov != 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", 2 * N, N * d);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, N + mt[x][S[i]]);
    return 0;
}
"""


def _haar_c(d, seed, budget, m, k, r):
    """Run the difference-cover search for Z_m x| Z_k; return (n, edges) or None."""
    if budget < 0.2:
        return None
    try:
        out = lib.run_c(C_HAAR, [d, 3, seed, round(budget, 2), m, k, r],
                        timeout=budget + 5.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 2 or not e2:
        return None
    return n2, e2


def _groups_of_order(N, rng, cap=8):
    """Candidate groups of order N as (m, k, r): cyclic first, then sampled semidirect products."""
    cyc = [(N, 1, 1)]
    others = []
    for m in range(2, N + 1):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        units = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not units:
            continue
        for r in rng.sample(units, min(2, len(units))):
            others.append((m, k, r))
    rng.shuffle(others)
    return cyc + others[:cap - 1]


def _haar_search(d, seed, deadline):
    """Increase the group order N while difference covers of size d are found; return best (n, edges)."""
    rng = random.Random(seed * 31 + 7)
    best = None
    N = d + 1
    Nmax = d * d - d + 1          # Moore-type ceiling for diameter-3 Haar graphs
    misses = 0
    while N <= Nmax and misses < 2 and time.monotonic() < deadline:
        found = None
        for rnd_i, b in enumerate((0.35, 1.2)):
            groups = _groups_of_order(N, rng)
            if rnd_i == 1:
                groups = groups[:3]
            for (m, k, r) in groups:
                left = deadline - time.monotonic()
                if left < 0.3:
                    break
                g = _haar_c(d, seed * 1000 + N * 7 + rnd_i, min(b, left), m, k, r)
                if g is not None:
                    found = g
                    break
            if found is not None:
                break
        if found is None:
            misses += 1
        else:
            misses = 0
            best = found
        N += 1
    return best


# ----------------------------------------------------------------------------
# C engine (kept from the parent): greedy vertex insertion with ball-cover
# certificates (diameter D). Used as a final augmentation step on arc graphs.
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
# Arc-extended projective plane incidence graphs (diameter 3). Fallback.
#
# Start from PG(2, q) incidence (degree q+1). With d >= q+1 each vertex has
# spare s = d - q - 1. Add one new A-vertex per point of SA (joined to the lines
# through it) and one new B-vertex per line of SB (joined to its points), with
# each line carrying <= s points of SA and each point <= s lines of SB.
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
    """Conic (plus nucleus for even q) as a point-index set: an arc."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus new A-vertices (per SA point) and B-vertices (per SB line)."""
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
# Generalized quadrangle baseline (D = 4). Other D >= 4 cases use this and the
# K_{d,d} fallback only; the voltage annealer of the parent is not carried over.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
#   D = 2: K_{d,d}.
#   D = 3: difference-cover Haar graphs until 0.55 of the time, then arc graphs
#          until 0.72, then insertion augmentation until 0.88. Every candidate
#          is checked by lib.is_valid; the best valid one is returned.
#   D >= 4: GQ baseline or K_{d,d}.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
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

    if D >= 4:
        consider(_best_gq(d))
        return best

    # D == 3
    consider(_haar_search(d, seed, start + 0.55 * time_limit))

    cands = _arc_extensions(d, start + 0.72 * time_limit,
                            random.Random(seed * 7919 + d))
    cands.sort(key=lambda t: -t[0])
    pool = [g for g in cands[:2] if lib.is_valid(g[0], g[1], d, D)]
    for g in pool:
        consider(g)

    base = pool[0] if pool else best
    budget = 0.88 * time_limit - (time.monotonic() - start)
    if budget >= 0.5:
        consider(_c_augment(base, d, D, seed, budget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
