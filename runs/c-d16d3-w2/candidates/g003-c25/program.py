import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: greedy vertex insertion with ball-cover certificates (from parent).
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


# ----------------------------------------------------------------------------
# C engine 2 (new): simulated annealing over bi-Cayley voltage lifts.
#
# Group G = Z_m x| Z_k2 (element (a,b) coded a*k2+b, product (a + r^b c, b + d)).
# Base: K A-vertices and K B-vertices. Layer L has a permutation P[L] of
# {0..K-1} and a voltage S[L] in G. Edge: A_{i,g} ~ B_{P[L][i], g*S[L]}.
# Lift has 2*K*G vertices and is exactly d-regular and bipartite.
# Left multiplication is an automorphism, so the diameter is at most D iff the
# 2K block representatives reach everything within distance D.
# Cost = total unreached (representative, vertex) pairs. Zero means valid.
# Moves: change one voltage, or swap two entries of one layer's permutation.
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXV 4096
#define MAXD 64
#define MAXK 16
#define MAXB 16

static int m, k2, G, K, d, D, NV;
static int rp[MAXB];
static int P[MAXD][MAXK];
static int S[MAXD];
static int bestP[MAXD][MAXK];
static int bestS[MAXD];
static int adj[MAXV][MAXD];
static int acnt[MAXV];
static int dd[MAXV];
static int stamp[MAXV];
static int cur_stamp = 0;
static int qu[MAXV];
static uint64_t rs = 88172645463325252ULL;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) {
    return (int)(nextr() % (uint64_t)n);
}

static double rnd01(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static int gmul(int x, int y) {
    int a = x / k2, b = x % k2;
    int c = y / k2, e = y % k2;
    long long t = ((long long)a + (long long)rp[b] * c) % m;
    return (int)t * k2 + (b + e) % k2;
}

static void build_adj(void) {
    NV = 2 * K * G;
    for (int v = 0; v < NV; v++) acnt[v] = 0;
    for (int L = 0; L < d; L++) {
        for (int i = 0; i < K; i++) {
            int j = P[L][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, S[L]);
                adj[a][acnt[a]++] = b;
                adj[b][acnt[b]++] = a;
            }
        }
    }
}

static int cost_eval(void) {
    build_adj();
    int total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        cur_stamp++;
        int head = 0, tail = 0;
        stamp[src] = cur_stamp;
        dd[src] = 0;
        qu[tail++] = src;
        while (head < tail) {
            int u = qu[head++];
            if (dd[u] >= D) continue;
            for (int t = 0; t < d; t++) {
                int v = adj[u][t];
                if (stamp[v] != cur_stamp) {
                    stamp[v] = cur_stamp;
                    dd[v] = dd[u] + 1;
                    qu[tail++] = v;
                }
            }
        }
        total += NV - tail;
    }
    return total;
}

static void rand_init(void) {
    for (int L = 0; L < d; L++) {
        for (int i = 0; i < K; i++) P[L][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = P[L][i];
            P[L][i] = P[L][j];
            P[L][j] = t;
        }
        S[L] = rndint(G);
    }
}

static void save_best(void) {
    for (int L = 0; L < d; L++) {
        for (int i = 0; i < K; i++) bestP[L][i] = P[L][i];
        bestS[L] = S[L];
    }
}

int main(int argc, char **argv) {
    if (argc < 10) { printf("1000000000\n"); return 0; }
    m = atoi(argv[1]);
    k2 = atoi(argv[2]);
    long long rr = atoll(argv[3]);
    K = atoi(argv[4]);
    d = atoi(argv[5]);
    D = atoi(argv[6]);
    unsigned long seed = strtoul(argv[7], NULL, 10);
    double budget = atof(argv[8]);
    int iters = atoi(argv[9]);
    if (m < 2 || k2 < 1 || k2 > MAXB || K < 1 || K > MAXK || d < 1 || d > MAXD
        || D < 1 || iters < 1 || (long long)m * k2 * 2 * K > MAXV) {
        printf("1000000000\n");
        return 0;
    }
    G = m * k2;
    NV = 2 * K * G;
    rp[0] = 1 % m;
    for (int b = 1; b < k2; b++)
        rp[b] = (int)(((long long)rp[b - 1] * (rr % m)) % m);

    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) nextr();

    int best = 1000000000;
    clock_t t0 = clock();
    const double T0 = 2.0, T1 = 0.15;
    double alpha = pow(T1 / T0, 1.0 / (double)iters);

    do {
        rand_init();
        int cur = cost_eval();
        if (cur < best) { best = cur; save_best(); }
        double T = T0;
        for (int it = 0; it < iters && cur > 0; it++) {
            int L = rndint(d);
            int oldS = S[L];
            int kind = 0, a = 0, b = 0;
            if (K >= 2 && (nextr() & 1ULL)) {
                kind = 1;
                a = rndint(K);
                do { b = rndint(K); } while (b == a);
                int t = P[L][a];
                P[L][a] = P[L][b];
                P[L][b] = t;
            } else {
                int ns = rndint(G);
                if (ns == oldS) { T *= alpha; continue; }
                S[L] = ns;
            }
            int c2 = cost_eval();
            int delta = c2 - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cur = c2;
                if (cur < best) { best = cur; save_best(); }
            } else {
                if (kind == 1) {
                    int t = P[L][a];
                    P[L][a] = P[L][b];
                    P[L][b] = t;
                } else {
                    S[L] = oldS;
                }
            }
            T *= alpha;
        }
    } while (best > 0 && (double)(clock() - t0) / CLOCKS_PER_SEC < budget);

    printf("%d\n", best);
    for (int L = 0; L < d; L++) {
        for (int i = 0; i < K; i++) printf("%d ", bestP[L][i]);
        printf("%d\n", bestS[L]);
    }
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


def _sample_group(G, rng):
    """Return (m, k2, r) with Z_m x| Z_k2 of order G (r = 1 gives a direct product), or None."""
    k2s = [k for k in range(1, 13) if G % k == 0 and G // k >= 2]
    if not k2s:
        return None
    k2 = 1 if rng.random() < 0.4 else rng.choice(k2s)
    m = G // k2
    if k2 == 1:
        return (m, 1, 1)
    cands = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
    if not cands:
        return None
    return (m, k2, rng.choice(cands))


def _sa_lift(m, k2, r, K, d, D, seed, budget, iters):
    """Run the C annealer; return (n, edges) for a valid lift, or None."""
    try:
        out = lib.run_c(C_LIFT, [m, k2, r, K, d, D, seed, round(budget, 2), iters],
                        timeout=budget + 6.0)
        nums = [int(x) for x in out.split()]
        if not nums or nums[0] != 0:
            return None
        order, mul, _ = lib.semidirect_group(m, k2, r)
        G = order
        E = set()
        idx = 1
        for _ in range(d):
            perm = nums[idx: idx + K]
            idx += K
            s = nums[idx]
            idx += 1
            for i in range(K):
                j = perm[i]
                for g in range(G):
                    a = i * G + g
                    b = (K + j) * G + mul(g, s)
                    E.add((min(a, b), max(a, b)))
        return 2 * K * G, sorted(E)
    except Exception:
        return None


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), from parent.
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
# Generalized quadrangle baseline (D >= 4), from parent.
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
# Driver.
#   0.00-0.08  arc-extended PG graphs (fast, always valid candidates)
#   0.08-0.10  generalized quadrangle baseline when D >= 4
#   0.10-0.75  C annealing over bi-Cayley lifts, targeting order above the best so far
#   0.75-0.90  C greedy insertion on the best graph
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

    moore = lib.moore_bound(d, D)

    if D >= 3:
        arcs = _arc_extensions(d, start + 0.08 * time_limit,
                               random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for g in arcs:
            consider(g)

    if D >= 4 and elapsed() < 0.10 * time_limit:
        consider(_best_gq(d))

    sa_end = start + 0.75 * time_limit
    per_call = max(2.0, 0.10 * time_limit)
    attempt = 0
    Ks = [1, 1, 2, 2, 3, 4]
    while best_n < moore:
        remaining = sa_end - time.monotonic()
        budget = min(per_call, remaining - 0.5)
        if budget < 0.5:
            break
        attempt += 1
        K = rng.choice(Ks)
        gmin = best_n // (2 * K) + 1
        G = gmin + rng.randrange(0, 3)
        if 2 * K * G > moore:
            continue
        grp = _sample_group(G, rng)
        if grp is None:
            continue
        m, k2, r = grp
        res = _sa_lift(m, k2, r, K, d, D, seed * 1000 + attempt, budget, 6000)
        if res is not None:
            consider(res)

    if D >= 3 and best_n < moore:
        rem = 0.90 * time_limit - elapsed()
        if rem > 1.0:
            consider(_c_augment(best, d, D, seed + 1, rem))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
