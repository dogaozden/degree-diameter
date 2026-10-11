import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C repair engine: grows a valid bipartite graph by inserting isolated extra
# vertices and annealing over edge moves (add, remove, endpoint shift,
# degree-preserving 2-switch). Cost = number of ordered vertex pairs at
# distance > D. The graph is kept bipartite by only ever joining vertices of
# opposite colour. If no zero-cost graph is found, it prints "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 3000
#define MAXDEG 64
#define MAXE 96000

static int N, DEGCAP, DIAM, M;
static int color[MAXN], deg[MAXN];
static int adj[MAXN][MAXDEG];
static unsigned char adjm[MAXN][MAXN];
static int Ea[MAXE], Eb[MAXE];
static int IU[MAXE], IV[MAXE];
static int L0[MAXN], L1[MAXN];
static int n0 = 0, n1 = 0;
static int qbuf[MAXN], stampv[MAXN], distv[MAXN];
static int curstamp = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static long cost_full(void) {
    long total = 0;
    for (int s = 0; s < N; s++) {
        curstamp++;
        int h = 0, t = 0;
        qbuf[t++] = s;
        stampv[s] = curstamp;
        distv[s] = 0;
        while (h < t) {
            int u = qbuf[h++];
            if (distv[u] >= DIAM) continue;
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (stampv[v] != curstamp) {
                    stampv[v] = curstamp;
                    distv[v] = distv[u] + 1;
                    qbuf[t++] = v;
                }
            }
        }
        total += N - t;
    }
    return total;
}

static int find_edge(int a, int b) {
    for (int k = 0; k < M; k++) {
        if ((Ea[k] == a && Eb[k] == b) || (Ea[k] == b && Eb[k] == a)) return k;
    }
    return -1;
}

static void link_adj(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
    adjm[u][v] = 1;
    adjm[v][u] = 1;
}

static void unlink_adj(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adj[u][k] == v) {
            adj[u][k] = adj[u][--deg[u]];
            break;
        }
    }
    for (int k = 0; k < deg[v]; k++) {
        if (adj[v][k] == u) {
            adj[v][k] = adj[v][--deg[v]];
            break;
        }
    }
    adjm[u][v] = 0;
    adjm[v][u] = 0;
}

static void add_e(int a, int b) {
    Ea[M] = a;
    Eb[M] = b;
    M++;
    link_adj(a, b);
}

static void del_e(int a, int b) {
    int k = find_edge(a, b);
    if (k < 0) return;
    M--;
    Ea[k] = Ea[M];
    Eb[k] = Eb[M];
    unlink_adj(a, b);
}

static int accept(long delta, double T) {
    if (delta <= 0) return 1;
    return rnd01() < exp(-(double)delta / T);
}

static void output_graph(void) {
    printf("%d %d\n", N, M);
    for (int k = 0; k < M; k++) printf("%d %d\n", Ea[k], Eb[k]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    int extra = (argc > 5) ? atoi(argv[5]) : 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        printf("0 0\n");
        return 0;
    }
    if (n <= 0 || m < 0 || m > MAXE || n + extra > MAXN || d < 1 ||
        d > MAXDEG - 4 || D < 1 || extra < 0) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &IU[i], &IV[i]) != 2) {
            printf("0 0\n");
            return 0;
        }
    }

    N = n + extra;
    DEGCAP = d;
    DIAM = D;
    M = 0;
    for (int i = 0; i < N; i++) {
        deg[i] = 0;
        color[i] = -1;
    }
    for (int i = 0; i < m; i++) {
        int a = IU[i], b = IV[i];
        if (a < 0 || b < 0 || a >= n || b >= n || a == b || adjm[a][b] ||
            deg[a] >= d || deg[b] >= d) {
            printf("0 0\n");
            return 0;
        }
        add_e(a, b);
    }

    /* 2-colour the base graph; reject if it is not bipartite. */
    int ok = 1;
    for (int s = 0; s < n && ok; s++) {
        if (color[s] >= 0) continue;
        color[s] = 0;
        int qh = 0, qt = 0;
        qbuf[qt++] = s;
        while (qh < qt && ok) {
            int u = qbuf[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (color[v] < 0) {
                    color[v] = 1 - color[u];
                    qbuf[qt++] = v;
                } else if (color[v] == color[u]) {
                    ok = 0;
                }
            }
        }
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    for (int i = n; i < N; i++) color[i] = (i - n) & 1;

    for (int k = 0; k < M; k++) {
        if (color[Ea[k]] != 0) {
            int t = Ea[k];
            Ea[k] = Eb[k];
            Eb[k] = t;
        }
    }
    for (int i = 0; i < N; i++) {
        if (color[i] == 0) L0[n0++] = i;
        else L1[n1++] = i;
    }
    if (n0 == 0) {
        printf("0 0\n");
        return 0;
    }

    long cur = cost_full();
    clock_t c0 = clock();
    double T = 1.0;
    double el = 0.0;
    for (long it = 0; cur > 0; it++) {
        if ((it & 15) == 0) {
            el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el > tl) break;
            T = 3.0 * (1.0 - el / tl) + 0.2;
        }
        int r = rndint(100);
        long nc = 0;
        if (r < 35) {
            /* endpoint shift: edge (a,b) becomes (x,b), a loses one degree, x gains one */
            if (M == 0) continue;
            int k = rndint(M);
            int a = Ea[k], b = Eb[k];
            int x = L0[rndint(n0)];
            if (x == a || deg[x] >= DEGCAP || adjm[x][b]) continue;
            del_e(a, b);
            add_e(x, b);
            nc = cost_full();
            if (accept(nc - cur, T)) cur = nc;
            else {
                del_e(x, b);
                add_e(a, b);
            }
        } else if (r < 70) {
            /* degree-preserving 2-switch */
            if (M < 2) continue;
            int k1 = rndint(M), k2 = rndint(M);
            if (k1 == k2) continue;
            int a1 = Ea[k1], b1 = Eb[k1], a2 = Ea[k2], b2 = Eb[k2];
            if (a1 == a2 || b1 == b2 || adjm[a1][b2] || adjm[a2][b1]) continue;
            del_e(a1, b1);
            del_e(a2, b2);
            add_e(a1, b2);
            add_e(a2, b1);
            nc = cost_full();
            if (accept(nc - cur, T)) cur = nc;
            else {
                del_e(a1, b2);
                del_e(a2, b1);
                add_e(a1, b1);
                add_e(a2, b2);
            }
        } else if (r < 85) {
            /* add an edge where both ends have spare degree */
            if (n1 == 0) continue;
            int x = L0[rndint(n0)], y = L1[rndint(n1)];
            if (deg[x] >= DEGCAP || deg[y] >= DEGCAP || adjm[x][y]) continue;
            add_e(x, y);
            nc = cost_full();
            if (accept(nc - cur, T)) cur = nc;
            else del_e(x, y);
        } else {
            /* remove an edge */
            if (M == 0) continue;
            int k = rndint(M);
            int a = Ea[k], b = Eb[k];
            del_e(a, b);
            nc = cost_full();
            if (accept(nc - cur, T)) cur = nc;
            else add_e(a, b);
        }
    }

    if (cur == 0) output_graph();
    else printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S
# such that every line holds at most s points of S and every point lies on at
# most s lines indexed by S. Add a new A-vertex joined to the q+1 lines through
# each P in S, and a new B-vertex joined to the q+1 points of each line j in S.
# Order is 2(q^2+q+1) + 2|S|. For d=16 a conic (|S| = q+1 = 14) gives 394.
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
# Growth phase: ask the C engine to insert extra vertices into a valid graph.
# ----------------------------------------------------------------------------

def _c_repair(n, edges, d, D, seed, budget, extra):
    """Run the C repair engine on (n, edges); returns (n2, edges2), or (0, []) on failure."""
    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), extra],
                     stdin_graph=(n, edges), timeout=budget + 8.0)
    return lib.parse_graph_text(text)


def _grow(best, d, D, seed, deadline):
    """Repeatedly try to add 1 or 2 vertices to the current valid graph until the deadline."""
    cur = best
    cap = lib.moore_bound(d, D)
    rnd = random.Random(seed + 101)
    while True:
        if cur[0] + 1 > cap:
            return cur
        progressed = False
        for extra in (1, 2):
            if cur[0] + extra > cap:
                continue
            remaining = deadline - time.monotonic()
            if remaining < 4.0:
                return cur
            budget = min(12.0, remaining - 2.0)
            try:
                n2, e2 = _c_repair(cur[0], cur[1], d, D, rnd.randrange(1 << 30), budget, extra)
            except Exception:
                return cur
            if n2 > cur[0] and lib.is_valid(n2, e2, d, D):
                cur = (n2, e2)
                progressed = True
                break
        if not progressed and deadline - time.monotonic() < 4.0:
            return cur


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total_end = start + 0.85 * time_limit
    c_end = start + 0.6 * time_limit
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

    cap = lib.moore_bound(d, D)

    # Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        cands = _arc_extensions(d, c_end, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < c_end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Calibration cases already at the Moore bound return immediately.
    if best_n >= cap:
        if lib.is_valid(best[0], best[1], d, D):
            return best
        return lib.haar_graph(d, range(d))

    # Bold phase: C repair search that grows the best graph by inserting vertices.
    if D >= 3 and d <= 60 and best_n <= 2800 and time.monotonic() < c_end:
        try:
            grown = _grow(best, d, D, seed, c_end)
            consider(grown[0], grown[1])
        except Exception:
            pass

    # Remaining time: annealed group voltage lifts.
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < total_end:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, total_end, iters=400)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
