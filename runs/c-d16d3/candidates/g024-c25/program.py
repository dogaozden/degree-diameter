"""Arc-extended projective plane graphs (D = 3), plus a C augmentation search.

Construction: take the incidence graph of PG(2, q) and add pencil vertices A_P (joined to the
lines through P) and dual vertices B_j (joined to the points on j), with P and j taken from
arcs S. Every line may carry at most s = d - q - 1 of the chosen A-points, and every point at
most s of the chosen B-lines. This keeps diameter 3. For d = 16 the conic/oval gives 394.

Limit of this family: both A and B sides need arcs with at most 2 points per line/point, and
an oval in PG(2, 13) has at most 14 points, so 394 is the cap here. The C engine therefore
starts from the 394 graph and tries to add vertices by simulated annealing over edge swaps,
minimising the number of pairs at distance > D. Every output is re-checked with lib.is_valid,
and the Python fallback is kept if the C step fails or times out.
"""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C augmentation engine: adds vertices to a valid graph of diameter <= D,
# maintaining max degree <= d and bipartiteness, using annealed edge swaps.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 1600
#define MAXD 64
#define MAXW ((MAXN + 63) / 64)
#define STEPS 3000
#define SAVEMAX (MAXN * MAXD)

static int n, d, D;
static int deg[MAXN];
static int nb[MAXN][MAXD];
static unsigned char A[MAXN][MAXN];
static int side[MAXN];
static uint64_t Rb[MAXN][MAXW], Rn[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static clock_t T0;

static int sv_n, sv_m;
static int sv_eu[SAVEMAX], sv_ev[SAVEMAX];
static int qbuf[MAXN];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) { return (double)(clock() - T0) / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int u, int v) {
    A[u][v] = 1;
    A[v][u] = 1;
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
}

static void del_nb(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (nb[u][k] == v) {
            nb[u][k] = nb[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void del_edge(int u, int v) {
    A[u][v] = 0;
    A[v][u] = 0;
    del_nb(u, v);
    del_nb(v, u);
}

/* Number of unordered pairs at distance > D (unreachable pairs included). */
static long long bad_pairs(void) {
    int W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) Rb[v][w] = 0;
        Rb[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < D; it++) {
        int changed = 0;
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) Rn[v][w] = Rb[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = nb[v][k];
                for (int w = 0; w < W; w++) Rn[v][w] |= Rb[u][w];
            }
            for (int w = 0; w < W; w++)
                if (Rn[v][w] != Rb[v][w]) changed = 1;
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) Rb[v][w] = Rn[v][w];
        if (!changed) break;
    }
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(Rb[v][w]);
        tot += n - c;
    }
    return tot / 2;
}

static void save_graph(void) {
    sv_n = n;
    sv_m = 0;
    for (int v = 0; v < n; v++) {
        for (int k = 0; k < deg[v]; k++) {
            if (nb[v][k] > v && sv_m < SAVEMAX) {
                sv_eu[sv_m] = v;
                sv_ev[sv_m] = nb[v][k];
                sv_m++;
            }
        }
    }
}

static void load_graph(void) {
    for (int v = 0; v < n; v++) {
        for (int k = 0; k < deg[v]; k++) A[v][nb[v][k]] = 0;
        deg[v] = 0;
    }
    n = sv_n;
    for (int i = 0; i < sv_m; i++) add_edge(sv_eu[i], sv_ev[i]);
}

/* Random bipartite edges between vertices with spare degree. Never increases the cost. */
static void fill_slack(int tries) {
    for (int t = 0; t < tries && n > 1; t++) {
        int a = rndint(n), b = rndint(n);
        if (side[a] == side[b] || deg[a] >= d || deg[b] >= d || A[a][b]) continue;
        add_edge(a, b);
    }
}

/* Add a vertex on one side, joined to d spare-degree vertices of the other side. */
static int add_vertex(void) {
    if (n >= MAXN - 1) return 0;
    int first = rndint(2);
    for (int t = 0; t < 2; t++) {
        int s = (t == 0) ? first : 1 - first;
        int cand[MAXN];
        int nc = 0;
        for (int v = 0; v < n; v++)
            if (side[v] != s && deg[v] < d) cand[nc++] = v;
        if (nc < d) continue;
        int x = n;
        n++;
        side[x] = s;
        deg[x] = 0;
        for (int i = 0; i < d; i++) {
            int j = i + rndint(nc - i);
            int tmp = cand[i];
            cand[i] = cand[j];
            cand[j] = tmp;
            add_edge(x, cand[i]);
        }
        return 1;
    }
    return 0;
}

/* One annealing move: remove a bipartite edge (u,v), add a bipartite edge (a,b) between spare vertices. */
static void sa_step(long long *cost, double T) {
    int u = rndint(n);
    if (deg[u] == 0) return;
    int v = nb[u][rndint(deg[u])];
    if (side[u] == 1) {
        int t = u;
        u = v;
        v = t;
    }
    del_edge(u, v);
    int s0[MAXN], s1[MAXN];
    int n0 = 0, n1 = 0;
    for (int w = 0; w < n; w++) {
        if (deg[w] < d) {
            if (side[w] == 0) s0[n0++] = w;
            else s1[n1++] = w;
        }
    }
    int a = -1, b = -1;
    if (n0 > 0 && n1 > 0) {
        for (int t = 0; t < 30; t++) {
            int x = s0[rndint(n0)];
            int y = s1[rndint(n1)];
            if (A[x][y] || (x == u && y == v)) continue;
            a = x;
            b = y;
            break;
        }
    }
    if (a < 0) {
        add_edge(u, v);
        return;
    }
    add_edge(a, b);
    long long c2 = bad_pairs();
    long long delta = c2 - *cost;
    if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
        *cost = c2;
    } else {
        del_edge(a, b);
        add_edge(u, v);
    }
}

static void print_saved(void) {
    printf("%d %d\n", sv_n, sv_m);
    for (int i = 0; i < sv_m; i++) printf("%d %d\n", sv_eu[i], sv_ev[i]);
}

int main(int argc, char **argv) {
    T0 = clock();
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);

    int n0, m0;
    if (d < 1 || d > MAXD || D < 1 || scanf("%d %d", &n0, &m0) != 2 ||
        n0 <= 0 || n0 > MAXN - 300 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    n = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            u == v || A[u][v] || deg[u] >= d || deg[v] >= d) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    /* Bipartition by BFS; reject non-bipartite input. */
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, tail = 0;
        qbuf[tail++] = s;
        while (head < tail) {
            int x = qbuf[head++];
            for (int k = 0; k < deg[x]; k++) {
                int y = nb[x][k];
                if (side[y] < 0) {
                    side[y] = 1 - side[x];
                    qbuf[tail++] = y;
                } else if (side[y] == side[x]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    if (bad_pairs() != 0) {
        printf("0 0\n");
        return 0;
    }
    save_graph();

    while (elapsed() < tl) {
        if (!add_vertex()) break;
        fill_slack(20000);
        long long cost = bad_pairs();
        int steps = 0;
        while (cost > 0 && steps < STEPS && elapsed() < tl) {
            double T = 0.8 * (1.0 - (double)steps / STEPS) + 0.05;
            sa_step(&cost, T);
            steps++;
        }
        if (cost == 0) save_graph();
        else load_graph();
    }
    print_saved();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare capacity
# s = d - q - 1. Choose a point set S such that every line contains at most s
# points of S and every point lies on at most s lines indexed by S. For each P
# in S add a new A-vertex joined to all q+1 lines through P; for each j in S add
# a new B-vertex joined to all q+1 points on line j.
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
# Simulated annealing over bi-Cayley voltage lifts (Python fallback search).
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
    deadline = start + 0.8 * time_limit
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
        cands = _arc_extensions(d, start + 0.3 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # C augmentation: start from the best valid graph and try to add vertices by annealed
    # edge swaps. The C program prints its best valid graph before its own budget ends.
    # Any failure keeps the Python result.
    if D >= 3 and best_n > 2:
        c_end = start + 0.72 * time_limit
        remaining = c_end - time.monotonic()
        if remaining > 1.0:
            timeout = min(remaining + 3.0, 0.9 * time_limit - (time.monotonic() - start))
            if timeout > remaining + 0.5:
                try:
                    text = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                                     stdin_graph=best, timeout=timeout)
                    n_c, e_c = lib.parse_graph_text(text)
                    consider(n_c, e_c)
                except (RuntimeError, ValueError):
                    pass

    # Remaining time: annealed group voltage lifts.
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
