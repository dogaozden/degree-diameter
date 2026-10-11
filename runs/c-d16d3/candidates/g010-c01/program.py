import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: grows a valid bipartite graph one vertex at a time.
#
# Starting from a valid input graph, each stage attaches a new vertex to random
# spare-capacity vertices on the opposite side, then runs simulated annealing
# on the number of vertex pairs at distance > D (computed with bitsets). Moves:
# degree-preserving double edge swaps, edge relocation to a spare pair, and
# pure addition of a spare pair. A stage that reaches cost 0 is kept; otherwise
# the state is rolled back, so the output is always valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXW (MAXN / 64)
#define MAXD 64

static int N, DEG_MAX, DIAM;
static int side[MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXD];
static uint64_t R[2][MAXN][MAXW];
static int bdeg[MAXN];
static int bnb[MAXN][MAXD];
static int L0[MAXN], L1[MAXN], cand[MAXN];
static uint64_t rs = 88172645463325252ULL;
static double t_budget = 1.0;
static clock_t t_start;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - t_start) / CLOCKS_PER_SEC; }

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (nb[a][k] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void del_one(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (nb[a][k] == b) {
            nb[a][k] = nb[a][--deg[a]];
            return;
        }
    }
}

static void remove_edge(int a, int b) {
    del_one(a, b);
    del_one(b, a);
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered vertex pairs at distance > DIAM. Zero means valid. */
static long cost(void) {
    int W = (N + 63) / 64;
    int cur = 0;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) R[0][v][w] = 0;
        R[0][v][v >> 6] |= (uint64_t)1 << (v & 63);
    }
    for (int r = 0; r < DIAM; r++) {
        int nx = 1 - cur;
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) R[nx][v][w] = R[cur][v][w];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = R[cur][nb[v][k]];
                for (int w = 0; w < W; w++) R[nx][v][w] |= src[w];
            }
        }
        cur = nx;
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(R[cur][v][w]);
        bad += N - c;
    }
    return bad / 2;
}

/* Random edge with endpoint a on side 0 and b on side 1. */
static int pick_edge0(int *a, int *b) {
    for (int t = 0; t < 200; t++) {
        int x = rndint(N);
        if (side[x] == 0 && deg[x] > 0) {
            *a = x;
            *b = nb[x][rndint(deg[x])];
            return 1;
        }
    }
    return 0;
}

static void sa_step(long *curp, double T) {
    long cur = *curp;
    int r = rndint(10);
    if (r < 4) {
        /* double edge swap, keeps all degrees */
        int a, b, c, e;
        if (!pick_edge0(&a, &b) || !pick_edge0(&c, &e)) return;
        if (a == c || b == e || has_edge(a, e) || has_edge(c, b)) return;
        remove_edge(a, b);
        remove_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long c2 = cost();
        long delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            *curp = c2;
        } else {
            remove_edge(a, e);
            remove_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
        return;
    }
    int moving = (r < 8);
    int u = -1, v = -1;
    if (moving) {
        if (!pick_edge0(&u, &v)) return;
        remove_edge(u, v);
    }
    int n0 = 0, n1 = 0;
    for (int w = 0; w < N; w++) {
        if (deg[w] < DEG_MAX) {
            if (side[w] == 0) L0[n0++] = w;
            else L1[n1++] = w;
        }
    }
    int x = -1, y = -1, found = 0;
    if (n0 > 0 && n1 > 0) {
        for (int t = 0; t < 30 && !found; t++) {
            x = L0[rndint(n0)];
            y = L1[rndint(n1)];
            if (!has_edge(x, y) && !(x == u && y == v)) found = 1;
        }
    }
    if (!found) {
        if (moving) add_edge(u, v);
        return;
    }
    add_edge(x, y);
    long c2 = cost();
    long delta = c2 - cur;
    if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
        *curp = c2;
    } else {
        remove_edge(x, y);
        if (moving) add_edge(u, v);
    }
}

/* Try to add one vertex. Returns 1 on success (state valid, N grows), else 0 with state restored. */
static int grow_stage(long maxit) {
    int N0 = N;
    memcpy(bdeg, deg, sizeof(int) * N0);
    memcpy(bnb, nb, sizeof(int) * MAXD * N0);
    int s = rndint(2);
    int c = 0;
    for (int v = 0; v < N0; v++)
        if (side[v] == 1 - s && deg[v] < DEG_MAX) cand[c++] = v;
    if (c == 0) return 0;
    int k = c < DEG_MAX ? c : DEG_MAX;
    for (int i = 0; i < k; i++) {
        int j = i + rndint(c - i);
        int t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    side[N0] = s;
    deg[N0] = 0;
    N = N0 + 1;
    for (int i = 0; i < k; i++) add_edge(N0, cand[i]);

    long cur = cost();
    for (long it = 0; it < maxit && cur > 0; it++) {
        if ((it & 63) == 0 && elapsed() > t_budget) break;
        double T = pow(0.05, (double)it / (double)maxit);
        sa_step(&cur, T);
    }
    if (cur == 0) return 1;
    N = N0;
    memcpy(deg, bdeg, sizeof(int) * N0);
    memcpy(nb, bnb, sizeof(int) * MAXD * N0);
    return 0;
}

static void output(void) {
    long m = 0;
    for (int v = 0; v < N; v++) m += deg[v];
    m /= 2;
    printf("%d %ld\n", N, m);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (v < nb[v][k]) printf("%d %d\n", v, nb[v][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG_MAX = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;
    t_budget = atof(argv[4]);
    t_start = clock();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        printf("0 0\n");
        return 0;
    }
    if (n0 < 1 || n0 >= MAXN - 64 || DEG_MAX < 1 || DEG_MAX >= MAXD || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    N = n0;
    for (int v = 0; v < N; v++) deg[v] = 0;
    int ok = 1;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v || has_edge(u, v)
            || deg[u] >= DEG_MAX || deg[v] >= DEG_MAX) {
            ok = 0;
            break;
        }
        add_edge(u, v);
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    /* bipartiteness check and sides */
    static int qq[MAXN];
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s0 = 0; s0 < N && ok; s0++) {
        if (side[s0] >= 0) continue;
        side[s0] = 0;
        int head = 0, tail = 0;
        qq[tail++] = s0;
        while (head < tail && ok) {
            int u = qq[head++];
            for (int k = 0; k < deg[u]; k++) {
                int w = nb[u][k];
                if (side[w] < 0) {
                    side[w] = 1 - side[u];
                    qq[tail++] = w;
                } else if (side[w] == side[u]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    if (cost() != 0) {
        printf("0 0\n");
        return 0;
    }
    while (N < MAXN - 2 && elapsed() < t_budget) {
        int grown = 0;
        for (int a = 0; a < 4 && !grown && elapsed() < t_budget; a++)
            grown = grow_stage(8000);
        if (!grown) break;
    }
    output();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Choose a point set S with every
# line holding <= s points of S and every point on <= s lines indexed by S,
# where s = d - q - 1. Add an A-vertex per point of S (joined to its lines) and
# a B-vertex per element of S (joined to the points of that line).
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
    """Old PG incidence plus a new A and a new B vertex per element of S."""
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
            cs = _conic_set(q, index, lib.GF(q))
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
# Simulated annealing over bi-Cayley voltage lifts (used only for D >= 5).
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
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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

    # Algebraic constructions (cheap).
    if D >= 3:
        cands = _arc_extensions(d, t0 + 0.25 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Voltage-lift annealing only for D >= 5, in a bounded share of the time.
    if D >= 5:
        ks = [1, 2, 2, 3, 4]
        anneal_deadline = t0 + 0.3 * time_limit
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

    # Main search: C engine grows the best construction by adding vertices.
    elapsed = time.monotonic() - t0
    left = 0.9 * time_limit - elapsed
    if left > 1.0:
        budget = 0.85 * left
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=left)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
