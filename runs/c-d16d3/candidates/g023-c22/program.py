import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C local search: grow a valid diameter-D bipartite graph by one vertex at a time.
# Each attempt adds a vertex, then runs simulated annealing over edge moves
# (rewire, add, remove) that keep max degree <= d and bipartiteness. The cost is
# the number of ordered vertex pairs at distance > D. Failed attempts are rolled back.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXD 64
#define ITERS 3000

static int N, D, DEG;
static int adjl[MAXN][MAXD];
static int deg[MAXN];
static int side[MAXN];
static int snapadj[MAXN][MAXD];
static int snapdeg[MAXN];
static int cand[MAXN];
static uint64_t rs = 88172645463325252ULL;
static clock_t t0;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adjl[a][i] == b) return 1;
    return 0;
}
static void add_e(int a, int b) { adjl[a][deg[a]++] = b; adjl[b][deg[b]++] = a; }
static void del_one(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adjl[a][i] == b) { adjl[a][i] = adjl[a][--deg[a]]; return; }
}
static void rem_e(int a, int b) { del_one(a, b); del_one(b, a); }

static long cost(void) {
    static int dist[MAXN], q[MAXN];
    long bad = 0;
    for (int s = 0; s < N; s++) {
        for (int i = 0; i < N; i++) dist[i] = -1;
        int h = 0, t = 0;
        q[t++] = s;
        dist[s] = 0;
        while (h < t) {
            int u = q[h++];
            if (dist[u] >= D) continue;
            for (int i = 0; i < deg[u]; i++) {
                int v = adjl[u][i];
                if (dist[v] < 0) { dist[v] = dist[u] + 1; q[t++] = v; }
            }
        }
        bad += N - t;
    }
    return bad;
}

static void color_sides(void) {
    static int q[MAXN];
    for (int i = 0; i < N; i++) side[i] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adjl[u][i];
                if (side[v] < 0) { side[v] = 1 - side[u]; q[t++] = v; }
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    t0 = clock();

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN - 2 || DEG >= MAXD - 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a < 0 || a >= n || b < 0 || b >= n || a == b) continue;
        if (deg[a] >= DEG || deg[b] >= DEG) continue;
        add_e(a, b);
    }
    color_sides();

    while (elapsed() < tl && N + 1 < MAXN) {
        int old = N;
        memcpy(snapdeg, deg, sizeof deg);
        memcpy(snapadj, adjl, sizeof adjl);

        int x = N++;
        deg[x] = 0;
        side[x] = rint_(2);
        int nc = 0;
        for (int w = 0; w < old; w++)
            if (side[w] != side[x] && deg[w] < DEG) cand[nc++] = w;
        for (int i = nc - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int tmp = cand[i]; cand[i] = cand[j]; cand[j] = tmp;
        }
        for (int i = 0; i < nc && deg[x] < DEG; i++) add_e(x, cand[i]);

        long cur = cost();
        for (int it = 0; it < ITERS && cur > 0 && elapsed() < tl; it++) {
            double T = 1.5 * (1.0 - (double)it / ITERS) + 0.05;
            int r = rint_(10);
            if (r < 6) {
                int u = -1, w = -1;
                for (int t = 0; t < 50 && u < 0; t++) {
                    int c = rint_(N);
                    if (deg[c] > 0) u = c;
                }
                if (u < 0) continue;
                int v = adjl[u][rint_(deg[u])];
                for (int t = 0; t < 50 && w < 0; t++) {
                    int c = rint_(N);
                    if (c != v && side[c] == side[v] && deg[c] < DEG && !has_edge(u, c)) w = c;
                }
                if (w < 0) continue;
                rem_e(u, v);
                add_e(u, w);
                long nc2 = cost();
                if (nc2 <= cur || rdbl() < exp((double)(cur - nc2) / T)) cur = nc2;
                else { rem_e(u, w); add_e(u, v); }
            } else if (r < 9) {
                int a = -1, b = -1;
                for (int t = 0; t < 50 && a < 0; t++) {
                    int c = rint_(N);
                    if (deg[c] < DEG) a = c;
                }
                if (a < 0) continue;
                for (int t = 0; t < 50 && b < 0; t++) {
                    int c = rint_(N);
                    if (side[c] != side[a] && deg[c] < DEG && !has_edge(a, c)) b = c;
                }
                if (b < 0) continue;
                add_e(a, b);
                long nc2 = cost();
                if (nc2 <= cur || rdbl() < exp((double)(cur - nc2) / T)) cur = nc2;
                else rem_e(a, b);
            } else {
                int u = -1;
                for (int t = 0; t < 50 && u < 0; t++) {
                    int c = rint_(N);
                    if (deg[c] > 0) u = c;
                }
                if (u < 0) continue;
                int v = adjl[u][rint_(deg[u])];
                rem_e(u, v);
                long nc2 = cost();
                if (nc2 <= cur || rdbl() < exp((double)(cur - nc2) / T)) cur = nc2;
                else add_e(u, v);
            }
        }
        if (cur != 0) {
            N = old;
            memcpy(deg, snapdeg, sizeof deg);
            memcpy(adjl, snapadj, sizeof adjl);
        }
    }

    long M = 0;
    for (int i = 0; i < N; i++)
        for (int j = 0; j < deg[i]; j++)
            if (adjl[i][j] > i) M++;
    printf("%d %ld\n", N, M);
    for (int i = 0; i < N; i++)
        for (int j = 0; j < deg[i]; j++)
            if (adjl[i][j] > i) printf("%d %d\n", i, adjl[i][j]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
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
# C repair stage: grow the best graph by annealed vertex insertions.
# ----------------------------------------------------------------------------

def _repair(best, d, D, seed, seconds, time_limit):
    """Run the C growth search from `best` for about `seconds`; return (n, edges) it prints."""
    n, e = best
    budget = max(0.5, min(seconds, 0.5 * time_limit))
    timeout = min(budget + 1.5, 0.9 * time_limit)
    text = lib.run_c(C_SOURCE, [d, D, seed, budget], stdin_graph=(n, e), timeout=timeout)
    return lib.parse_graph_text(text)


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

    # New: C growth search starting from the best graph found so far.
    # It runs in its own budget, and any failure keeps the current best.
    repair_secs = min(start + 0.5 * time_limit - time.monotonic(), 0.5 * time_limit)
    if best_n >= 2 and repair_secs >= 1.0:
        try:
            n_r, e_r = _repair(best, d, D, seed, repair_secs, time_limit)
            consider(n_r, e_r)
        except Exception:
            pass

    # Annealed group voltage lifts for the remaining time. For D >= 5 use larger bases.
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
