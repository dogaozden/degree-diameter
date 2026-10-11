import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: greedy vertex insertion with ball-cover certificates, plus a new
# ejection-chain move.
#
# Let R = D-1. A new vertex w joined to a set N (on the opposite colour class)
# is within distance D of every old vertex x that lies in the R-ball of some
# u in N. Adding vertices and cross edges never increases old distances, so
# insertions keep validity.
#
# NEW in this version: when no insertion succeeds, an ejection move is tried.
# It removes a random vertex v, then greedily re-inserts up to three new
# vertices. The move is kept only if the vertex count did not drop and the
# whole graph still has diameter <= D (checked by full R=D balls). Otherwise
# the state is restored from a snapshot. Accepted equal-size moves form a
# plateau random walk that reshapes the spare-degree pattern without losing
# order, which the old random-edge perturbation could not do.
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

static int sv_n;
static int sv_deg[MAXN];
static int sv_adj[MAXN][MAXD];
static int sv_col[MAXN];

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

/* After compute_balls(D): true iff every pair is within distance D. */
static int all_full(void) {
    for (int v = 0; v < n; v++)
        if (!covers_all(reach[v])) return 0;
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
    if (n >= MAXN) return 0;
    int w = n;
    n++;
    col[w] = side;
    deg[w] = 0;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], w);
    return 1;
}

static void save_state(void) {
    sv_n = n;
    memcpy(sv_deg, deg, sizeof(int) * (size_t)n);
    memcpy(sv_adj, adj, sizeof(adj[0]) * (size_t)n);
    memcpy(sv_col, col, sizeof(int) * (size_t)n);
}

static void restore_state(void) {
    n = sv_n;
    memcpy(deg, sv_deg, sizeof(int) * (size_t)n);
    memcpy(adj, sv_adj, sizeof(adj[0]) * (size_t)n);
    memcpy(col, sv_col, sizeof(int) * (size_t)n);
}

/* Delete vertex v; the last vertex is renamed to v so labels stay 0..n-1. */
static void remove_vertex(int v) {
    for (int i = 0; i < deg[v]; i++) {
        int u = adj[v][i];
        for (int j = 0; j < deg[u]; j++)
            if (adj[u][j] == v) { adj[u][j] = adj[u][deg[u] - 1]; deg[u]--; break; }
    }
    int last = n - 1;
    if (v != last) {
        for (int i = 0; i < deg[last]; i++) {
            int u = adj[last][i];
            for (int j = 0; j < deg[u]; j++)
                if (adj[u][j] == last) { adj[u][j] = v; break; }
        }
        deg[v] = deg[last];
        for (int i = 0; i < deg[last]; i++) adj[v][i] = adj[last][i];
        col[v] = col[last];
    }
    deg[last] = 0;
    n--;
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
    long long iters = 0;
    while (n < MAXN) {
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        iters++;
        W = (n + 63) >> 6;
        compute_balls(D - 1);
        int sides[2] = {0, 1};
        if (rnd() & 1u) { sides[0] = 1; sides[1] = 0; }
        int ok = 0;
        for (int k = 0; k < 2 && !ok; k++) ok = try_insert(sides[k]);
        if (ok) continue;

        /* Ejection chain: remove a random vertex, re-insert up to three. */
        int n_before = n;
        save_state();
        if (n > 1) remove_vertex((int)(rnd() % (uint32_t)n));
        for (int t = 0; t < 3; t++) {
            W = (n + 63) >> 6;
            compute_balls(D - 1);
            int s2 = (int)(rnd() & 1u);
            if (!(try_insert(s2) || try_insert(1 - s2))) break;
        }
        int accept = 0;
        if (n >= n_before) {
            W = (n + 63) >> 6;
            compute_balls(D);
            accept = all_full();
        }
        if (accept) continue;

        restore_state();
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
    """Run the C engine on graph; return (n, edges) or None on any failure."""
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
# Arc-extended projective plane incidence graphs (diameter 3).
#
# PG(2, q) incidence: points 0..m-1, lines m..2m-1, each of degree q+1, spare
# s = d - q - 1. New A-vertices attach to q+1 lines through a chosen point, and
# each line may take at most s of them. New B-vertices attach to points on a
# chosen line, with each point taking at most s. Sides are independent.
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
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
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
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
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
# Generalized quadrangle W(q) incidence graph (diameter 4 baseline).
# ----------------------------------------------------------------------------

def _gq_w(q):
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Annealed bi-Cayley voltage lifts over small semidirect products (D >= 5).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
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
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
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
#   0.00-0.08  arc-extended PG graphs
#   0.08-0.12  generalized quadrangle baseline (D = 4)
#   0.12-0.45  annealed group lifts (D >= 5 only)
#   0.45-0.80  C insertion + ejection-chain search on the best graph
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2: always valid for D >= 2
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
        arcs = _arc_extensions(d, start + 0.08 * time_limit, random.Random(seed * 7919 + d))
        for g in sorted(arcs, key=lambda t: -t[0]):
            consider(g)

    if D >= 4 and elapsed() < 0.12 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    if D >= 5:
        anneal_end = start + 0.45 * time_limit
        ks = [1, 2, 2, 3, 4]
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

    if D >= 3:
        rem = 0.80 * time_limit - elapsed() - 1.0
        if rem > 1.0:
            consider(_c_augment(best, d, D, seed, rem))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
