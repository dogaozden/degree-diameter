import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: greedy vertex extension with exact diameter checks.
#
# Starting from the Python graph, it (1) adds any missing edge between opposite
# colour classes whose endpoints have spare degree (this only shortens paths),
# then (2) repeatedly tries to append a new vertex on one side, joined to up to
# d opposite-side vertices that still have spare degree. The vertex is kept only
# if every pair is still within distance D; otherwise it is rolled back.
# Output is the best valid graph found (or "0 0" if the input is unusable).
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXDEG 64
#define MAXM 65536

static int n, dmax, Dmax;
static int deg[MAXN];
static int col[MAXN];
static int adj[MAXN][MAXDEG];
static int vis[MAXN];
static int vstamp = 0;
static unsigned long long rs = 88172645463325252ULL;
static int eu[MAXM], ev[MAXM];

static unsigned long long rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) {
    return (int)(rnd64() % (unsigned long long)k);
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (adj[u][i] == v) return 1;
    return 0;
}

/* BFS from src up to Dmax levels; returns the number of vertices reached. */
static int reach_count(int src) {
    static int q[MAXN];
    int head = 0, tail = 0;
    vstamp++;
    vis[src] = vstamp;
    q[tail++] = src;
    for (int depth = 0; depth < Dmax && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            int u = q[head++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (vis[v] != vstamp) {
                    vis[v] = vstamp;
                    q[tail++] = v;
                }
            }
        }
    }
    return tail;
}

/* True if every pair among the first nn vertices is within distance Dmax. */
static int all_within(int nn) {
    if (reach_count(nn - 1) != nn) return 0;   /* newest vertex first: most likely to fail */
    for (int s = 0; s < nn - 1; s++)
        if (reach_count(s) != nn) return 0;
    return 1;
}

/* Bipartition by BFS; returns 1 if the graph is bipartite. */
static int colour_graph(void) {
    static int q[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        int head = 0, tail = 0;
        col[s] = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] == -1) {
                    col[v] = 1 - col[u];
                    q[tail++] = v;
                } else if (col[v] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void print_graph(void) {
    int m = 0;
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) m++;
    printf("%d %d\n", n, m);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) printf("%d %d\n", u, adj[u][i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dmax = atoi(argv[1]);
    Dmax = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    clock_t c0 = clock();

    int m = 0;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    if (n < 1 || n > MAXN - 700 || m < 0 || m > MAXM || dmax < 1 || dmax > MAXDEG || Dmax < 1) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { printf("0 0\n"); return 0; }
    }

    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || u >= n || v < 0 || v >= n || u == v || has_edge(u, v) ||
            deg[u] >= dmax || deg[v] >= dmax) {
            printf("0 0\n");
            return 0;
        }
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }
    if (!colour_graph() || !all_within(n)) { printf("0 0\n"); return 0; }

    /* Phase 1: fill missing cross edges between vertices with spare degree. */
    for (int pass = 0; pass < 2; pass++) {
        int order[MAXN];
        for (int i = 0; i < n; i++) order[i] = i;
        for (int i = n - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = order[i];
            order[i] = order[j];
            order[j] = t;
        }
        for (int a = 0; a < n; a++) {
            int u = order[a];
            if (deg[u] >= dmax) continue;
            for (int b = 0; b < n && deg[u] < dmax; b++) {
                int v = order[b];
                if (v == u || col[v] == col[u] || deg[v] >= dmax || has_edge(u, v)) continue;
                adj[u][deg[u]++] = v;
                adj[v][deg[v]++] = u;
            }
        }
    }

    /* Phase 2: greedy vertex extension with rollback. */
    static int cand[MAXN];
    while ((double)(clock() - c0) / CLOCKS_PER_SEC < budget) {
        if (n + 1 >= MAXN) break;
        int c = rndint(2);
        int nc = 0;
        for (int w = 0; w < n; w++)
            if (col[w] == 1 - c && deg[w] < dmax) cand[nc++] = w;
        if (nc < 1) break;
        for (int i = nc - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = cand[i];
            cand[i] = cand[j];
            cand[j] = t;
        }
        int k = dmax < nc ? dmax : nc;
        int x = n;
        deg[x] = 0;
        col[x] = c;
        for (int i = 0; i < k; i++) {
            int w = cand[i];
            adj[w][deg[w]++] = x;
            adj[x][deg[x]++] = w;
        }
        n++;
        if (all_within(n)) continue;          /* accepted */
        n--;
        for (int i = 0; i < k; i++) deg[cand[i]]--;
        deg[x] = 0;
    }

    print_graph();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so spare capacity s = d - q - 1. For a point set S, add an A-vertex per P in S
# joined to the lines through P, and a B-vertex per j in S joined to the points
# on line j. Requirement: every line holds <= s points of S and every point lies
# on <= s lines indexed by S. Order is 2(q^2+q+1) + 2|S|.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line meets <= s points of S and every point lies on <= s lines of S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): a set with no three collinear points."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus, per element of S, an A-vertex (on lines through P) and a B-vertex (on points of line P)."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
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
        m, edges, point_lines, line_points, index = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 30, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
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
# Simulated annealing over bi-Cayley voltage lifts.
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
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    T = float(time_limit)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Constructions (fast).
    if D >= 3:
        for n_c, e_c in _arc_extensions(d, t0 + 0.2 * T, random.Random(seed * 7919 + d)):
            consider(n_c, e_c)
    if D >= 4 and time.monotonic() < t0 + 0.2 * T:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Voltage-lift annealing.
    anneal_deadline = t0 + 0.3 * T
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < anneal_deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, anneal_deadline, iters=400)
        if res is not None:
            consider(res[0], res[1])

    # C pass: fill spare capacity and greedily extend with exact diameter checks.
    c_deadline = t0 + 0.85 * T
    budget = c_deadline - time.monotonic() - 1.5
    if budget >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best, timeout=budget + 30.0)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
