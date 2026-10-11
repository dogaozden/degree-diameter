import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare capacity
# s = d - q - 1. Choose a point set S such that every line contains at most s
# points of S and every point lies on at most s lines indexed by S. For each P
# in S add a new A-vertex joined to the q+1 lines through P; for each j in S add
# a new B-vertex joined to the q+1 points on line j. Diameter stays 3.
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


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Build the extended graph: old PG incidence plus a new A and a new B vertex per element of S."""
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
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, S)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# C engine: greedy vertex addition with exact distance bookkeeping.
#
# Starting from a valid bipartite graph, repeatedly tries to add a new vertex x
# whose neighbours all lie in one colour class, with deg <= d. x is valid iff
# every existing vertex is within D-1 of some neighbour of x. Distances are kept
# in an all-pairs matrix and updated in O(n^2) per addition:
# dist'(a,b) = min(dist(a,b), dxa[a] + dxa[b]), dxa[a] = 1 + min_u dist(u,a).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 1200
#define MAXDEG 64
#define INF 200

static int n, DMAX, D;
static unsigned char dist[MAXN][MAXN];
static int deg[MAXN], col[MAXN];
static int adj[MAXN][MAXDEG];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double now(void) {
    return (double)clock() / CLOCKS_PER_SEC;
}

static void bfs_from(int s) {
    static int q[MAXN];
    int h = 0, t = 0;
    for (int i = 0; i < n; i++) dist[s][i] = INF;
    dist[s][s] = 0;
    q[t++] = s;
    while (h < t) {
        int u = q[h++];
        for (int k = 0; k < deg[u]; k++) {
            int v = adj[u][k];
            if (dist[s][v] == INF) {
                dist[s][v] = (unsigned char)(dist[s][u] + 1);
                q[t++] = v;
            }
        }
    }
}

/* Try to add one vertex whose neighbours all have colour c. Returns 1 on success. */
static int attempt(int c, int randfirst) {
    static unsigned char uncov[MAXN];
    static unsigned char used[MAXN];
    static int bestd[MAXN];
    static int dxa[MAXN];
    static int N[MAXDEG];
    int nn = 0, cnt = n;
    int lim = D - 1;
    if (n == 0) return 0;
    for (int a = 0; a < n; a++) {
        uncov[a] = 1;
        used[a] = 0;
        bestd[a] = INF;
    }
    while (cnt > 0 && nn < DMAX) {
        int bu = -1;
        if (nn == 0 && randfirst) {
            int nc = 0;
            for (int u = 0; u < n; u++) {
                if (col[u] == c && deg[u] < DMAX) {
                    nc++;
                    if (rnd() % nc == 0) bu = u;
                }
            }
        } else {
            int bcov = 0, nt = 0;
            for (int u = 0; u < n; u++) {
                if (col[u] != c || deg[u] >= DMAX || used[u]) continue;
                int cov = 0;
                for (int a = 0; a < n; a++)
                    if (uncov[a] && dist[u][a] <= lim) cov++;
                if (cov > bcov) {
                    bcov = cov;
                    bu = u;
                    nt = 1;
                } else if (cov == bcov && cov > 0) {
                    nt++;
                    if (rnd() % nt == 0) bu = u;
                }
            }
        }
        if (bu < 0) return 0;
        used[bu] = 1;
        N[nn++] = bu;
        for (int a = 0; a < n; a++) {
            if (dist[bu][a] < bestd[a]) bestd[a] = dist[bu][a];
            if (uncov[a] && dist[bu][a] <= lim) {
                uncov[a] = 0;
                cnt--;
            }
        }
    }
    if (cnt > 0 || nn == 0) return 0;
    if (n + 1 >= MAXN) return 0;

    /* Commit: new vertex x = n. */
    int x = n;
    for (int a = 0; a < n; a++) dxa[a] = bestd[a] + 1;
    for (int a = 0; a < n; a++) {
        for (int b = 0; b < n; b++) {
            int s = dxa[a] + dxa[b];
            if (s < dist[a][b]) dist[a][b] = (unsigned char)s;
        }
    }
    for (int a = 0; a < n; a++) {
        dist[x][a] = (unsigned char)dxa[a];
        dist[a][x] = (unsigned char)dxa[a];
    }
    dist[x][x] = 0;
    n++;
    deg[x] = nn;
    col[x] = 1 - c;
    for (int k = 0; k < nn; k++) {
        adj[x][k] = N[k];
        adj[N[k]][deg[N[k]]++] = x;
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    DMAX = d;
    if (DMAX > MAXDEG) DMAX = MAXDEG;
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;

    int N0 = 0, M0 = 0;
    if (scanf("%d %d", &N0, &M0) != 2) {
        N0 = 0;
        M0 = 0;
    }
    if (N0 < 0 || N0 > MAXN - 64) {
        printf("0 0\n");
        return 0;
    }
    n = N0;
    for (int i = 0; i < n; i++) {
        deg[i] = 0;
        col[i] = -1;
    }
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= MAXDEG || deg[v] >= MAXDEG) continue;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }

    /* Bipartition by BFS colouring. */
    {
        static int q[MAXN];
        for (int s = 0; s < n; s++) {
            if (col[s] != -1) continue;
            int h = 0, t = 0;
            col[s] = 0;
            q[t++] = s;
            while (h < t) {
                int u = q[h++];
                for (int k = 0; k < deg[u]; k++) {
                    int v = adj[u][k];
                    if (col[v] == -1) {
                        col[v] = 1 - col[u];
                        q[t++] = v;
                    }
                }
            }
        }
    }

    for (int s = 0; s < n; s++) bfs_from(s);

    double t0 = now();
    if (n > 0 && D >= 2) {
        while (now() - t0 < tl && n + 1 < MAXN) {
            int added = 0;
            for (int tr = 0; tr < 60 && !added; tr++) {
                int c = (int)(rnd() & 1);
                added = attempt(c, tr & 1);
            }
            if (!added) break;
        }
    }

    long m = 0;
    for (int u = 0; u < n; u++) m += deg[u];
    m /= 2;
    printf("%d %ld\n", n, m);
    for (int u = 0; u < n; u++) {
        for (int k = 0; k < deg[u]; k++) {
            int v = adj[u][k];
            if (u < v) printf("%d %d\n", u, v);
        }
    }
    return 0;
}
"""


def _grow(n, edges, d, D, seed, budget):
    """Run the C greedy vertex addition from (n, edges); return the best valid graph found."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                        stdin_graph=(n, edges), timeout=budget + 30.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return n, edges
    if n2 > n and lib.is_valid(n2, e2, d, D):
        return n2, e2
    return n, edges


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
# Simulated annealing over bi-Cayley voltage lifts (fallback search).
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Arc-extended projective plane graphs. Diameter 3, so valid for all D >= 3.
    if D >= 3:
        cands = _arc_extensions(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # New: C greedy vertex addition starting from the best graph found so far.
    # Any failure falls back to the current best, so this step cannot lower the score.
    if D >= 2 and d <= 60 and best_n >= 2:
        grow_budget = 0.6 * time_limit - (time.monotonic() - start)
        if grow_budget > 1.0:
            n_g, e_g = _grow(best_n, best[1], d, D, seed, grow_budget)
            consider(n_g, e_g)

    # Annealed group voltage lifts for the remaining time.
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
