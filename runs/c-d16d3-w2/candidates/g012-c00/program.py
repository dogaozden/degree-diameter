import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C repair search (diameter 3 and up).
#
# Input: a valid graph G (bipartite, max degree d). Repeatedly add one vertex x
# on a random side, greedily give it neighbours that cover its own side, then
# run simulated annealing on the bad-pair count (pairs at distance > D).
# Moves: rewire an edge endpoint to another spare vertex on the same side, or
# add an edge between spare vertices on opposite sides. Degrees stay <= d and
# the graph stays bipartite throughout. On reaching zero bad pairs the new
# graph becomes the base for the next vertex; otherwise the state is restored.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 1100
#define MAXD 64
#define MAXW ((MAXN + 63) / 64)
#define ITERS 6000

static int N, Dm, DEG;
static int nb[MAXN][MAXD];
static int deg[MAXN];
static unsigned char adjm[MAXN][MAXN];
static int col[MAXN];
static uint64_t RA[MAXN][MAXW], RB[MAXN][MAXW];
static int BE[MAXN * MAXD][2];
static int BN, BM;
static uint64_t rs = 88172645463325252ULL;
static int SL[2][MAXN], SC[2];

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) / 9007199254740992.0; }
static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }
static int pc64(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static void add_edge(int a, int b) {
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
    adjm[a][b] = adjm[b][a] = 1;
}
static void drop(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (nb[a][i] == b) { nb[a][i] = nb[a][--deg[a]]; return; }
}
static void del_edge(int a, int b) {
    drop(a, b); drop(b, a);
    adjm[a][b] = adjm[b][a] = 0;
}

/* Number of unordered vertex pairs at distance > Dm. */
static long long cost_fn(void) {
    int W = (N + 63) / 64;
    uint64_t (*cur)[MAXW] = RA, (*nx)[MAXW] = RB, (*tmp)[MAXW];
    for (int v = 0; v < N; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * MAXW);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < Dm; t++) {
        for (int v = 0; v < N; v++) {
            memcpy(nx[v], cur[v], sizeof(uint64_t) * W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = cur[nb[v][i]];
                for (int w = 0; w < W; w++) nx[v][w] |= src[w];
            }
        }
        tmp = cur; cur = nx; nx = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(cur[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

static void snapshot(void) {
    BM = 0;
    for (int v = 0; v < N; v++)
        for (int i = 0; i < deg[v]; i++)
            if (nb[v][i] > v) { BE[BM][0] = v; BE[BM][1] = nb[v][i]; BM++; }
    BN = N;
}

static void restore(void) {
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg[v]; i++) adjm[v][nb[v][i]] = 0;
        deg[v] = 0;
    }
    N = BN;
    for (int e = 0; e < BM; e++) add_edge(BE[e][0], BE[e][1]);
}

static void build_sides(void) {
    SC[0] = SC[1] = 0;
    for (int v = 0; v < N; v++) SL[col[v]][SC[col[v]]++] = v;
}

/* Greedy neighbourhood for the new vertex x: cover all other vertices on its side. */
static void seed_vertex(int x) {
    static unsigned char unc[MAXN];
    int c = col[x];
    int nunc = 0;
    for (int v = 0; v < N; v++) unc[v] = 0;
    for (int i = 0; i < SC[c]; i++) {
        int v = SL[c][i];
        if (v != x) { unc[v] = 1; nunc++; }
    }
    while (nunc > 0 && deg[x] < DEG) {
        int best = -1, bg = 0, ties = 0;
        for (int i = 0; i < SC[1 - c]; i++) {
            int t = SL[1 - c][i];
            if (deg[t] >= DEG || adjm[x][t]) continue;
            int g = 0;
            for (int j = 0; j < deg[t]; j++) if (unc[nb[t][j]]) g++;
            if (g > bg) { bg = g; best = t; ties = 1; }
            else if (g == bg && g > 0) { ties++; if (rndint(ties) == 0) best = t; }
        }
        if (best < 0) break;
        add_edge(x, best);
        for (int j = 0; j < deg[best]; j++) {
            int u = nb[best][j];
            if (unc[u]) { unc[u] = 0; nunc--; }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    Dm = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double tl = atof(argv[4]);
    DEG = d;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 0 || n > MAXN || d < 1 || d > MAXD || Dm < 1 || m < 0) { printf("0 0\n"); return 0; }
    N = n;
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (deg[u] >= DEG || deg[v] >= DEG || adjm[u][v]) continue;
        add_edge(u, v);
    }

    /* 2-colour; reject non-bipartite input. */
    static int q[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int i = 0; i < deg[u]; i++) {
                int w = nb[u][i];
                if (col[w] < 0) { col[w] = 1 - col[u]; q[t++] = w; }
                else if (col[w] == col[u]) { printf("0 0\n"); return 0; }
            }
        }
    }

    if (cost_fn() > 0) { printf("0 0\n"); return 0; }
    snapshot();

    double limit = tl * 0.9;
    while (now() < limit) {
        if (N >= MAXN) break;
        int x = N;
        N++;
        deg[x] = 0;
        col[x] = rndint(2);
        build_sides();
        seed_vertex(x);
        long long cur = cost_fn();

        for (int it = 0; it < ITERS && cur > 0; it++) {
            if ((it & 63) == 0 && now() > limit) break;
            double T = 0.05 + 1.5 * (1.0 - (double)it / ITERS);
            int mv = rndint(10);
            if (mv < 7) {
                int v = rndint(N);
                if (deg[v] == 0) continue;
                int u = nb[v][rndint(deg[v])];
                int w = -1;
                for (int tr = 0; tr < 60; tr++) {
                    int c2 = rndint(N);
                    if (col[c2] == col[v] && c2 != v && deg[c2] < DEG && !adjm[u][c2]) { w = c2; break; }
                }
                if (w < 0) continue;
                del_edge(u, v);
                add_edge(u, w);
                long long nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) cur = nc;
                else { del_edge(u, w); add_edge(u, v); }
            } else {
                int a = rndint(N), b = rndint(N);
                if (col[a] == col[b] || deg[a] >= DEG || deg[b] >= DEG || adjm[a][b]) continue;
                add_edge(a, b);
                cur = cost_fn();
            }
        }

        if (cur == 0) snapshot();
        else restore();
    }

    printf("%d %d\n", BN, BM);
    for (int e = 0; e < BM; e++) printf("%d %d\n", BE[e][0], BE[e][1]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare capacity
# s = d - q - 1. Choose a point set S such that every line contains at most s
# points of S and every point lies on at most s lines indexed by S. For each
# P in S add a new A-vertex joined to all q+1 lines through P; for each j in S
# add a new B-vertex joined to all q+1 points on line j. Diameter stays 3.
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
    for t, j in enumerate(S):  # S is also a set of line indices (same vectors)
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
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
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
# C repair driver.
# ----------------------------------------------------------------------------

def _repair(best, d, D, seed, budget):
    """Run the C repair search from `best` for about `budget` seconds; return (n, edges) or None."""
    if budget < 1.0:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=best, timeout=budget + 5.0)
        return lib.parse_graph_text(out)
    except Exception:
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

    # Main change: C annealing repair adds vertices to the best graph (diameter 3).
    # Every candidate is checked with lib.is_valid before it is kept.
    # d <= 3 is skipped: the calibration optimum is already reached.
    if D >= 3 and d > 3 and best_n > 2:
        repair_deadline = start + 0.65 * time_limit
        budget = repair_deadline - time.monotonic()
        res = _repair(best, d, D, seed, budget)
        if res is not None:
            consider(res[0], res[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed group voltage lifts. For D >= 5 use larger bases.
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
