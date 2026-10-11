import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: cyclic and metacyclic Haar graphs from difference covers.
#
# For a finite group G of order N and a d-subset S of G, let H(G, S) be the
# bipartite graph with a_g ~ b_{gs} for s in S. It is d-regular on 2N vertices.
#   * A-A distance <= 2  <=>  S S^{-1} = G
#   * B-B distance <= 2  <=>  S^{-1} S = G   (differs from the first in nonabelian G)
#   * A-B distance <= 3  is implied by S S^{-1} = G.
# So any such S gives diameter 3. The Moore-type ceiling is N <= d(d-1)+1.
# The engine searches over G = Z_m x| Z_k (all orders N near the ceiling, k <= 8),
# using simulated annealing with O(d) incremental updates of the coverage counts.
# It climbs N upward from a feasible start and prints the largest graph found.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXPAR 400
#define MAXD 128

static uint64_t rng_state = 88172645463325252ULL;

static uint64_t rnd64(void) {
    uint64_t x = rng_state;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rng_state = x;
    return x * 2685821657736338717ULL;
}

static unsigned rnd_int(unsigned n) {
    return (unsigned)((rnd64() >> 11) % n);
}

static double rnd_unit(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_sec(void) {
    return (double)clock() / (double)CLOCKS_PER_SEC;
}

typedef struct {
    int N, m, k, r, two;
    int *mul;   /* N*N table, element (a,b) coded as a*k+b, identity 0 */
    int *inv;   /* N */
} Grp;

typedef struct { int m, k, r; } Par;

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod(int b, int e, int m) {
    long long res = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) res = res * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)res;
}

static void grp_free(Grp *G) {
    free(G->mul);
    free(G->inv);
    G->mul = NULL;
    G->inv = NULL;
}

/* Semidirect product Z_m x| Z_k: (a,b)(c,d) = (a + r^b c, b + d). */
static int grp_build(Grp *G, int m, int k, int r) {
    int N = m * k;
    G->N = N; G->m = m; G->k = k; G->r = r; G->two = 0;
    G->mul = malloc(sizeof(int) * (size_t)N * (size_t)N);
    G->inv = malloc(sizeof(int) * (size_t)N);
    if (!G->mul || !G->inv) return 0;
    int *pw = malloc(sizeof(int) * (size_t)k);
    if (!pw) return 0;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, dd = y % k;
            int a2 = (int)(((long long)a + (long long)pw[b] * c) % m);
            int b2 = (b + dd) % k;
            G->mul[x * N + y] = a2 * k + b2;
        }
    }
    free(pw);
    for (int x = 0; x < N; x++) {
        G->inv[x] = -1;
        for (int y = 0; y < N; y++) {
            if (G->mul[x * N + y] == 0) { G->inv[x] = y; break; }
        }
        if (G->inv[x] < 0) return 0;
    }
    for (int x = 0; x < N && !G->two; x++)
        for (int y = x + 1; y < N; y++)
            if (G->mul[x * N + y] != G->mul[y * N + x]) { G->two = 1; break; }
    return 1;
}

static void cadd(int *c, int idx, int delta, int *zeros) {
    if (idx == 0) { c[0] += delta; return; }
    if (delta > 0) {
        if (c[idx] == 0) (*zeros)--;
        c[idx] += delta;
    } else {
        c[idx] += delta;
        if (c[idx] == 0) (*zeros)++;
    }
}

/* Add delta * (pair contributions of element x with every S[j], j != skip). */
static void change(const Grp *G, const int *S, int d, int skip, int x, int delta,
                   int *c1, int *c2, int *zeros) {
    int N = G->N;
    const int *mul = G->mul, *inv = G->inv;
    int ix = inv[x];
    for (int j = 0; j < d; j++) {
        if (j == skip) continue;
        int t = S[j];
        int it = inv[t];
        cadd(c1, mul[x * N + it], delta, zeros);
        cadd(c1, mul[t * N + ix], delta, zeros);
        if (G->two) {
            cadd(c2, mul[ix * N + t], delta, zeros);
            cadd(c2, mul[it * N + x], delta, zeros);
        }
    }
}

/* Full recount; returns number of uncovered non-identity elements. */
static int recompute(const Grp *G, const int *S, int d, int *c1, int *c2) {
    int N = G->N;
    memset(c1, 0, sizeof(int) * (size_t)N);
    memset(c2, 0, sizeof(int) * (size_t)N);
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) {
            if (i == j) continue;
            c1[G->mul[S[i] * N + G->inv[S[j]]]]++;
            if (G->two) c2[G->mul[G->inv[S[i]] * N + S[j]]]++;
        }
    int z = 0;
    for (int idx = 1; idx < N; idx++) {
        if (c1[idx] == 0) z++;
        if (G->two && c2[idx] == 0) z++;
    }
    return z;
}

static int sa_run(const Grp *G, int d, long long M, int *out) {
    int N = G->N;
    int *S = malloc(sizeof(int) * (size_t)d);
    char *inS = calloc((size_t)N, 1);
    int *c1 = calloc((size_t)N, sizeof(int));
    int *c2 = calloc((size_t)N, sizeof(int));
    int found = 0;
    if (!S || !inS || !c1 || !c2) {
        free(S); free(inS); free(c1); free(c2);
        return 0;
    }
    for (int i = 0; i < d; i++) {
        int y;
        do { y = (int)rnd_int((unsigned)N); } while (inS[y]);
        S[i] = y;
        inS[y] = 1;
    }
    int zeros = recompute(G, S, d, c1, c2);
    double T = 1.0;
    double f = pow(0.15, 1.0 / (double)M);
    for (long long it = 0; it < M && zeros > 0; it++) {
        int i = (int)rnd_int((unsigned)d);
        int old = S[i];
        int y;
        do { y = (int)rnd_int((unsigned)N); } while (inS[y]);
        int z0 = zeros;
        change(G, S, d, i, old, -1, c1, c2, &zeros);
        S[i] = y;
        change(G, S, d, i, y, +1, c1, c2, &zeros);
        int delta = zeros - z0;
        if (delta <= 0 || rnd_unit() < exp(-(double)delta / T)) {
            inS[old] = 0;
            inS[y] = 1;
        } else {
            change(G, S, d, i, y, -1, c1, c2, &zeros);
            S[i] = old;
            change(G, S, d, i, old, +1, c1, c2, &zeros);
        }
        T *= f;
    }
    if (zeros == 0 && recompute(G, S, d, c1, c2) == 0) {
        memcpy(out, S, sizeof(int) * (size_t)d);
        found = 1;
    }
    free(S); free(inS); free(c1); free(c2);
    return found;
}

static int best_N = 0, best_m = 0, best_k = 0, best_r = 0;
static int best_S[MAXD];

static int try_order(int N, int d, double slice_end) {
    Par P[MAXPAR];
    int np = 0;
    for (int k = 1; k <= 8 && k <= N; k++) {
        if (N % k) continue;
        int m = N / k;
        if (m < 2) continue;
        if (k == 1) {
            if (np < MAXPAR) { P[np].m = m; P[np].k = 1; P[np].r = 1; np++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_int(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (np < MAXPAR) { P[np].m = m; P[np].k = k; P[np].r = r; np++; }
        }
    }
    if (np == 0) return 0;
    for (int i = np - 1; i > 0; i--) {
        int j = (int)rnd_int((unsigned)(i + 1));
        Par t = P[i]; P[i] = P[j]; P[j] = t;
    }
    int S[MAXD];
    int idx = 0;
    while (now_sec() < slice_end) {
        Par q = P[idx % np];
        idx++;
        Grp G;
        memset(&G, 0, sizeof G);
        if (!grp_build(&G, q.m, q.k, q.r)) { grp_free(&G); continue; }
        int ok = sa_run(&G, d, 2000000LL, S);
        grp_free(&G);
        if (ok) {
            best_N = N; best_m = q.m; best_k = q.k; best_r = q.r;
            memcpy(best_S, S, sizeof(int) * (size_t)d);
            return 1;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    char buf[4096];
    while (fread(buf, 1, sizeof buf, stdin) > 0) {}
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rng_state ^= (seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (rng_state == 0) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd64();
    if (D != 3 || d < 2 || d > MAXD) { printf("0 0\n"); return 0; }

    double deadline = now_sec() + budget;
    int cap = d * (d - 1) + 1;
    if (cap > 2000) cap = 2000;
    int N = (cap * 3) / 4;
    if (N < d + 1) N = d + 1;

    int best = 0;
    while (best == 0 && N > d && now_sec() < deadline) {
        double se = now_sec() + 3.0;
        if (se > deadline) se = deadline;
        if (try_order(N, d, se)) best = N;
        else N -= 4;
    }
    int fails = 0;
    N = best + 1;
    while (best > 0 && N <= cap && fails < 3 && now_sec() < deadline) {
        double se = now_sec() + 3.0;
        if (se > deadline) se = deadline;
        if (try_order(N, d, se)) { best = N; fails = 0; }
        else fails++;
        N++;
    }

    if (best == 0) { printf("0 0\n"); return 0; }
    Grp G;
    memset(&G, 0, sizeof G);
    if (!grp_build(&G, best_m, best_k, best_r) || G.N != best) { printf("0 0\n"); return 0; }
    int *c1 = calloc((size_t)best, sizeof(int));
    int *c2 = calloc((size_t)best, sizeof(int));
    if (!c1 || !c2 || recompute(&G, best_S, d, c1, c2) != 0) { printf("0 0\n"); return 0; }
    long E = (long)best * (long)d;
    printf("%d %ld\n", 2 * best, E);
    for (int g = 0; g < best; g++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", g, best + G.mul[g * best + best_S[j]]);
    grp_free(&G);
    free(c1); free(c2);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S
# such that every line contains at most s points of S and every point lies on
# at most s lines indexed by S. Add a new A-vertex per P in S and a new
# B-vertex per j in S. This is the safe fallback for D = 3.
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
# Greedy vertex insertion with ball-cover certificates (used for D >= 4).
# ----------------------------------------------------------------------------

def _side_colors(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _ball_masks(n, adj, R):
    """Bitmask of all vertices within distance R of each vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return reach


def _augment(n, edges, d, D, rng, deadline, max_fails=60):
    """Greedily insert vertices whose neighbourhoods cover the graph within D. Returns (n, edges)."""
    if n == 0 or D < 2:
        return n, list(edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _side_colors(n, adj)
    R = D - 1
    fails = 0
    while time.monotonic() < deadline and fails < max_fails:
        balls = _ball_masks(n, adj, R)
        full = (1 << n) - 1
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for side in sides:
            base_cand = [u for u in range(n) if color[u] == 1 - side and len(adj[u]) < d]
            if not base_cand:
                continue
            for _attempt in range(4):
                cand = base_cand[:]
                rng.shuffle(cand)
                covered = 0
                chosen = []
                pool = cand
                while covered != full and len(chosen) < d and pool:
                    best_gain, bu, bi = 0, None, -1
                    for i, u in enumerate(pool):
                        g = (balls[u] & ~covered).bit_count()
                        if g > best_gain:
                            best_gain, bu, bi = g, u, i
                    if bu is None:
                        break
                    chosen.append(bu)
                    covered |= balls[bu]
                    pool = pool[:bi] + pool[bi + 1:]
                if covered == full:
                    w = n
                    n += 1
                    adj.append(set())
                    color.append(side)
                    for u in chosen:
                        adj[u].add(w)
                        adj[w].add(u)
                    added = True
                    break
            if added:
                break
        if added:
            fails = 0
            continue
        fails += 1
        spare_a = [u for u in range(n) if len(adj[u]) < d and color[u] == 0]
        spare_b = [u for u in range(n) if len(adj[u]) < d and color[u] == 1]
        if spare_a and spare_b:
            for _ in range(20):
                u = rng.choice(spare_a)
                v = rng.choice(spare_b)
                if u != v and v not in adj[u]:
                    adj[u].add(v)
                    adj[v].add(u)
                    break
    out = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, out


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


# ----------------------------------------------------------------------------
# Entry point.
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

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        # Fallback first: arc-extended projective planes (valid, e.g. 394 for d = 16).
        arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)

        # New construction: largest Haar graph H(G, S) over a metacyclic group G
        # with |S| = d and S S^{-1} = S^{-1} S = G, found by C annealing.
        # The C clock starts after compilation, so keep a margin of 1 s.
        remaining = start + 0.85 * time_limit - time.monotonic() - 1.0
        if remaining > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                                 stdin_graph=None, timeout=remaining + 15.0)
                n_h, e_h = lib.parse_graph_text(text)
                consider(n_h, e_h)
            except (RuntimeError, ValueError):
                pass
    else:
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        if D >= 3:
            arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
            arcs.sort(key=lambda t: -t[0])
            for n_c, e_c in arcs[:3]:
                consider(n_c, e_c)
            if arcs:
                n_a, e_a = arcs[0]
                n2, e2 = _augment(n_a, e_a, d, D, rng, start + 0.30 * time_limit)
                consider(n2, e2)

        if D >= 4 and time.monotonic() < start + 0.30 * time_limit:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])

        search_end = start + 0.55 * time_limit
        while time.monotonic() < search_end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, search_end, iters=400)
            if res is not None:
                consider(res[0], res[1])

        if D >= 2 and time.monotonic() < start + 0.85 * time_limit:
            n_f, e_f = _augment(best[0], best[1], d, D, rng, start + 0.85 * time_limit)
            consider(n_f, e_f)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
