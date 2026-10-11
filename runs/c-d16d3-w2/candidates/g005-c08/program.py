import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: incremental cover-extension with exact acceptance.
#
# Key fact used here: adding a vertex never lengthens any existing distance.
# So when we add a new vertex x to a graph that is already valid, the whole
# graph is still valid iff x itself reaches every vertex within D. One BFS
# from x (O(n + E)) therefore replaces a full all-pairs check.
#
# For a new vertex x on side 1-c, its neighbourhood T lies on side c, and it
# must cover every side-(1-c) vertex through N(T) (greedy set cover with
# random tie-breaks and a degree cap d). Restarts run until the CPU budget ends.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 64

static int n, d, D;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static int cov[MAXN];
static int cov_stamp = 0;
static int dist_[MAXN];
static int queue_[MAXN];
static unsigned long long rs = 88172645463325252ULL;

static unsigned long long rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

/* BFS from s: true iff every vertex is within distance D of s. */
static int reach_all_within_D(int s) {
    int i, h = 0, t = 0;
    for (i = 0; i < n; i++) dist_[i] = -1;
    dist_[s] = 0;
    queue_[t++] = s;
    while (h < t) {
        int u = queue_[h++];
        if (dist_[u] >= D) continue;
        for (i = 0; i < deg[u]; i++) {
            int v = adj[u][i];
            if (dist_[v] < 0) {
                dist_[v] = dist_[u] + 1;
                queue_[t++] = v;
            }
        }
    }
    return t == n;
}

static void colour_all(void) {
    int s, i;
    for (i = 0; i < n; i++) col[i] = -1;
    for (s = 0; s < n; s++) {
        int h = 0, t = 0;
        if (col[s] != -1) continue;
        col[s] = 0;
        queue_[t++] = s;
        while (h < t) {
            int u = queue_[h++];
            for (i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] == -1) {
                    col[v] = 1 - col[u];
                    queue_[t++] = v;
                }
            }
        }
    }
}

int main(int argc, char **argv) {
    int m, i, k, u, v;
    clock_t t0;
    double tl;
    unsigned long long seed;
    static char used[MAXN];

    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    seed = strtoull(argv[3], NULL, 10);
    tl = atof(argv[4]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    if (scanf("%d %d", &n, &m) != 2) {
        n = 0;
        m = 0;
    }
    if (n < 0 || n > MAXN - 8) {
        printf("0 0\n");
        return 0;
    }
    for (i = 0; i < m; i++) {
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d) continue;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }
    if (n == 0) {
        printf("0 0\n");
        return 0;
    }

    colour_all();
    t0 = clock();

    while ((double)(clock() - t0) / CLOCKS_PER_SEC < tl) {
        int c, x, nch = 0, target = 0, covered = 0;
        int chosen[MAXD];

        if (n + 1 >= MAXN) break;
        c = (int)(rnd() & 1ULL);
        cov_stamp++;
        for (i = 0; i < n; i++) {
            used[i] = 0;
            if (col[i] == 1 - c) target++;
        }
        if (target == 0) break;

        /* Greedy cover of side (1-c) by neighbourhoods of side-c vertices with spare degree. */
        while (covered < target && nch < d) {
            int best = -1;
            long long bestkey = -1;
            for (i = 0; i < n; i++) {
                int g = 0;
                long long key;
                if (col[i] != c || deg[i] >= d || used[i]) continue;
                for (k = 0; k < deg[i]; k++) {
                    int w = adj[i][k];
                    if (col[w] == 1 - c && cov[w] != cov_stamp) g++;
                }
                if (g == 0) continue;
                key = (long long)g * 1000000LL + (long long)(rnd() % 1000000ULL);
                if (key > bestkey) {
                    bestkey = key;
                    best = i;
                }
            }
            if (best < 0) break;
            used[best] = 1;
            chosen[nch++] = best;
            for (k = 0; k < deg[best]; k++) {
                int w = adj[best][k];
                if (col[w] == 1 - c && cov[w] != cov_stamp) {
                    cov[w] = cov_stamp;
                    covered++;
                }
            }
        }
        if (covered < target || nch == 0) continue;

        /* Tentatively add x = n joined to chosen; accept iff x reaches everything within D. */
        x = n;
        for (k = 0; k < nch; k++) {
            adj[chosen[k]][deg[chosen[k]]++] = x;
            adj[x][k] = chosen[k];
        }
        deg[x] = nch;
        col[x] = 1 - c;
        n++;
        if (!reach_all_within_D(x)) {
            n--;
            for (k = 0; k < nch; k++) deg[chosen[k]]--;
            deg[x] = 0;
        }
    }

    {
        long long me = 0;
        for (u = 0; u < n; u++)
            for (k = 0; k < deg[u]; k++)
                if (adj[u][k] > u) me++;
        printf("%d %lld\n", n, me);
        for (u = 0; u < n; u++)
            for (k = 0; k < deg[u]; k++)
                if (adj[u][k] > u) printf("%d %d\n", u, adj[u][k]);
    }
    return 0;
}
'''

MAX_C_D = 60


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S
# such that every line contains at most s points of S and every point lies on
# at most s lines indexed by S. For each P in S add a new A-vertex joined to
# all q+1 lines through P; for each j in S add a new B-vertex joined to all
# q+1 points on line j. Diameter stays 3.
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


def _arc_graph(m, edges, point_lines, S, line_points):
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
        n_c, e_c = _arc_graph(m, edges, point_lines, S, line_points)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Spare-capacity fill (diameter 3), Python version. Each addition is checked
# with lib.is_valid, so the result stays valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """2-colouring of a bipartite graph given by adjacency lists."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _fill(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover the opposite side; return (n, edges)."""
    edges = list(edges)
    fails = 0
    while time.monotonic() < deadline and fails < 400:
        adj = [[] for _ in range(n)]
        for u, v in edges:
            adj[u].append(v)
            adj[v].append(u)
        deg = [len(a) for a in adj]
        col = _bipartition(n, adj)
        c = rng.randrange(2)
        uncovered = {v for v in range(n) if col[v] == 1 - c}
        cand = [v for v in range(n) if col[v] == c and deg[v] < d]
        chosen = []
        chosen_set = set()
        while uncovered and len(chosen) < d:
            best_v = None
            best_key = None
            for v in cand:
                if v in chosen_set:
                    continue
                g = 0
                for u in adj[v]:
                    if u in uncovered:
                        g += 1
                if g == 0:
                    continue
                key = (g, rng.random())
                if best_key is None or key > best_key:
                    best_key = key
                    best_v = v
            if best_v is None:
                break
            chosen.append(best_v)
            chosen_set.add(best_v)
            for u in adj[best_v]:
                uncovered.discard(u)
        if uncovered:
            fails += 1
            continue
        new_edges = edges + [(v, n) for v in chosen]
        if lib.is_valid(n + 1, new_edges, d, D):
            edges = new_edges
            n += 1
            fails = 0
        else:
            fails += 1
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

    if D >= 3:
        # Arc-extended projective plane graphs (diameter 3).
        cands = _arc_extensions(d, start + 0.15 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

        # Python spare-degree fill.
        if best_n > 2:
            n_f, e_f = _fill(best_n, best[1], d, D, start + 0.25 * time_limit,
                             random.Random(seed * 104729 + d))
            consider(n_f, e_f)

    # New: exact incremental cover-extension in C, seeded with the best graph so far.
    # Adding a vertex never lengthens existing distances, so only the new vertex's
    # BFS needs checking. Final output is still verified by lib.is_valid.
    if D == 3 and 1 <= d <= MAX_C_D and best_n > 2:
        budget = start + 0.88 * time_limit - time.monotonic() - 2.5
        if budget >= 2.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                 stdin_graph=best, timeout=budget + 30.0)
                n_c, e_c = lib.parse_graph_text(text)
                consider(n_c, e_c)
            except (RuntimeError, ValueError, OSError):
                pass

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed group voltage lifts for the remaining time (D >= 4 and fallbacks).
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
