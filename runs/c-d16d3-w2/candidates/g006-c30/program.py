import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine with two modes.
#
# Mode "S" (new): maximum load-bounded set search by simulated annealing.
#   Input graph: elements 0..E-1 joined to targets E..E+T-1. Find a large set of
#   elements such that every target is hit by at most `cap` chosen elements.
#   Moves insert a random element and evict the (at most two) chosen elements that
#   block it. Reheating cycles escape plateaus. Output: "E k" then k pairs "x x".
#
# Mode "aug" (parent's engine): greedy vertex insertion with ball-cover
#   certificates. A new vertex joined to a set N of vertices on the opposite
#   colour class is valid whenever the R-balls (R = D-1) of N cover all vertices.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXD 64
#define MAXW (MAXN / 64)
#define MAXK 64

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

static double rnd01(void) {
    return (double)rnd() / 4294967296.0;
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

static int aug_main(int argc, char **argv) {
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

/* ---------------- mode S: load-bounded set search ---------------- */

static int se_E, se_T, se_cap;
static int se_ksz[MAXN];
static int se_tg[MAXN][MAXK];
static int se_load[MAXN];
static int se_mem[MAXN][MAXD];
static int se_in[MAXN];
static int se_bestin[MAXN];

static void se_add(int x) {
    se_in[x] = 1;
    for (int i = 0; i < se_ksz[x]; i++) {
        int t = se_tg[x][i];
        se_mem[t][se_load[t]++] = x;
    }
}

static void se_remove(int x) {
    se_in[x] = 0;
    for (int i = 0; i < se_ksz[x]; i++) {
        int t = se_tg[x][i];
        int L = se_load[t];
        for (int j = 0; j < L; j++) {
            if (se_mem[t][j] == x) { se_mem[t][j] = se_mem[t][L - 1]; break; }
        }
        se_load[t] = L - 1;
    }
}

static int set_main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    se_E = atoi(argv[2]);
    se_cap = atoi(argv[3]);
    double budget = atof(argv[4]);
    unsigned long seed = strtoul(argv[5], NULL, 10);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;

    int N, M;
    if (scanf("%d %d", &N, &M) != 2) { printf("0 0\n"); return 0; }
    if (N < 1 || N > MAXN || se_E < 1 || se_E > N || se_cap < 1 || se_cap > MAXD - 1) {
        printf("0 0\n");
        return 0;
    }
    se_T = N - se_E;
    for (int i = 0; i < N; i++) {
        se_ksz[i] = 0; se_load[i] = 0; se_in[i] = 0; se_bestin[i] = 0;
    }
    for (int i = 0; i < M; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= se_E || v < se_E || v >= N) continue;
        if (se_ksz[u] >= MAXK) continue;
        se_tg[u][se_ksz[u]++] = v - se_E;
    }

    clock_t t0 = clock();
    int cur = 0, best = 0;
    long long it = 0;
    const double Thi = 0.9, Tlo = 0.08;
    const long long cyc = 400000;
    int bl[2];
    while (1) {
        if ((it & 1023) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        it++;
        int x = (int)(rnd() % (uint32_t)se_E);
        if (se_in[x]) continue;
        double ph = (double)(it % cyc) / (double)cyc;
        double T = Thi * pow(Tlo / Thi, ph);
        int nb = 0, over = 0;
        for (int i = 0; i < se_ksz[x] && !over; i++) {
            int t = se_tg[x][i];
            if (se_load[t] < se_cap) continue;
            int y = se_mem[t][rnd() % (uint32_t)se_load[t]];
            int seen = 0;
            for (int k = 0; k < nb; k++) if (bl[k] == y) seen = 1;
            if (!seen) {
                if (nb == 2) { over = 1; break; }
                bl[nb++] = y;
            }
        }
        if (over) continue;
        int delta = 1 - nb;
        if (delta < 0 && rnd01() >= exp(delta / T)) continue;
        for (int k = 0; k < nb; k++) se_remove(bl[k]);
        se_add(x);
        cur += delta;
        if (cur > best) {
            best = cur;
            for (int k = 0; k < se_E; k++) se_bestin[k] = se_in[k];
        }
    }

    int cnt = 0;
    for (int k = 0; k < se_E; k++) if (se_bestin[k]) cnt++;
    printf("%d %d\n", se_E, cnt);
    for (int k = 0; k < se_E; k++) if (se_bestin[k]) printf("%d %d\n", k, k);
    return 0;
}

int main(int argc, char **argv) {
    if (argc >= 2 && argv[1][0] == 'S') return set_main(argc, argv);
    return aug_main(argc, argv);
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
# D = 3: arc-extended projective planes, with the arc sets found by C search.
#
# PG(2, q) incidence: points 0..m-1, lines m..2m-1, each vertex of degree q+1.
# Spare s = d - q - 1 per old vertex.
#   A-side: a set SA of points. Each P in SA gets a new vertex joined to the
#           q+1 lines through P. Each line may carry at most s such joins,
#           so SA is a set of points with at most s on every line.
#   B-side: a set SB of lines, symmetric, with at most s per point.
# The two sides are independent. Every distance condition holds for any choice
# (checked by hand: a-to-b pairs are at distance 3 via the line PQ), so the
# only real constraint is the load bound. Maximising |SA| and |SB| is the job
# of the C annealer ("S" mode).
#
# New idea in this version: after the arc sets are placed, the new A and B
# vertices still have spare degree, so they are joined to each other greedily.
# Extra edges never increase distances, so validity is kept.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _max_load_set(m, nbr, s, budget, seed, deadline):
    """Largest set of elements 0..m-1 (targets nbr[x] within 0..m-1) with every target hit <= s times."""
    if s < 1 or m < 1:
        return []
    budget = min(budget, deadline - time.monotonic() - 1.0)
    if budget < 0.5:
        return []
    edges = [(x, m + t) for x in range(m) for t in nbr[x]]
    try:
        out = lib.run_c(C_SOURCE, ["S", m, s, round(budget, 2), seed],
                        stdin_graph=(2 * m, edges), timeout=budget + 10.0)
        _, pairs = lib.parse_graph_text(out)
    except Exception:
        return []
    S = sorted({u for u, _ in pairs if 0 <= u < m})
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    if max(load, default=0) > s:
        return []
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
    new_a = list(range(2 * m, 2 * m + na))
    new_b = list(range(2 * m + na, n))
    return n, E, new_a, new_b


def _cross_fill(n, E, new_a, new_b, d, rng):
    """Greedily add edges between new A and new B vertices while both have spare degree."""
    deg = [0] * n
    have = set()
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
        have.add((min(u, v), max(u, v)))
    A = list(new_a)
    B = list(new_b)
    rng.shuffle(A)
    rng.shuffle(B)
    E = list(E)
    for a in A:
        for b in B:
            if deg[a] >= d:
                break
            if deg[b] >= d:
                continue
            key = (min(a, b), max(a, b))
            if key in have:
                continue
            have.add(key)
            E.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return E


def _arc_candidates(d, budget_total, deadline, seed):
    """Return candidate (n, edges) graphs for the top three prime powers q with q + 1 <= d."""
    out = []
    qs = [q for q in range(min(d - 1, 23), 1, -1) if lib.is_prime_power(q)][:3]
    if not qs:
        return out
    per = budget_total / (2 * len(qs))
    rng = random.Random(seed + 17)
    for q in qs:
        s = d - q - 1
        m, edges, pl, lp = _pg_data(q)
        out.append((2 * m, list(edges)))
        if s < 1:
            continue
        SA = _max_load_set(m, pl, s, per, seed + 3 * q, deadline)
        SB = _max_load_set(m, lp, s, per, seed + 5 * q + 1, deadline)
        n, E, new_a, new_b = _arc_graph(m, edges, pl, lp, SA, SB)
        E = _cross_fill(n, E, new_a, new_b, d, rng)
        out.append((n, E))
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
            nx = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nx.append(v)
            count += len(nx)
            frontier = nx
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
# Driver. Time plan (fractions of time_limit):
#   D == 3: 0.00-0.72 arc sets via C annealing (plus PG and arc graphs)
#           0.72-0.85 C greedy insertion on the best graph
#   D >= 4: 0.00-0.40 generalized quadrangle baseline
#           0.40-0.70 annealed group voltage lifts
#           0.70-0.85 C greedy insertion on the best graph
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

    def at(frac):
        return start + frac * time_limit

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        arc_end = at(0.72)
        for g in _arc_candidates(d, arc_end - time.monotonic(), arc_end, seed):
            consider(g)

    if D >= 4:
        if time.monotonic() < at(0.40):
            consider(_best_gq(d))
        anneal_end = at(0.70)
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

    if D >= 3 and best_n < lib.moore_bound(d, D):
        rem = at(0.85) - time.monotonic()
        if rem > 1.0:
            consider(_c_augment(best, d, D, seed + 1, rem))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
