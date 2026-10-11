import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: greedy vertex insertion with ball-cover certificates.
#
# A valid graph of diameter <= D stays valid when we add a vertex w on one
# colour side, joined to a set N of vertices on the other side, provided every
# old vertex x lies within distance D-1 of some u in N. Adding edges between
# opposite colour classes never increases a distance, so it is also safe.
# The engine repeats: greedy set cover of the R-balls (R = D-1) using vertices
# with spare degree, insertion on success, a random cross edge on failure.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

typedef uint64_t u64;

static u64 rs = 0x9E3779B97F4A7C15ULL;
static u64 rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (u64)k); }

static int dmax, DIAM, n, cap;
static int *adj, *deg, *col;

#define ADJ(v, i) adj[(size_t)(v) * dmax + (i)]

static void add_edge(int u, int v) {
    ADJ(u, deg[u]++) = v;
    ADJ(v, deg[v]++) = u;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (ADJ(u, i) == v) return 1;
    return 0;
}

static int popc(u64 x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int count_bits(const u64 *b, int W) {
    int c = 0;
    for (int i = 0; i < W; i++) c += popc(b[i]);
    return c;
}

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC;
}

/* Radius-R balls as bitsets; row v occupies W words starting at v*W. */
static u64 *balls_compute(int R, int W) {
    u64 *cur = calloc((size_t)n * W, sizeof(u64));
    u64 *nxt = malloc((size_t)n * W * sizeof(u64));
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            u64 *dst = nxt + (size_t)v * W;
            const u64 *src = cur + (size_t)v * W;
            memcpy(dst, src, W * sizeof(u64));
            for (int i = 0; i < deg[v]; i++) {
                const u64 *s2 = cur + (size_t)ADJ(v, i) * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        u64 *t = cur; cur = nxt; nxt = t;
    }
    free(nxt);
    return cur;
}

/* Try to insert one vertex on colour `side` covering all current vertices. */
static int try_insert(int side, const u64 *balls, int W) {
    int *cand = malloc(sizeof(int) * (n + 1));
    int nc = 0;
    for (int v = 0; v < n; v++)
        if (col[v] == 1 - side && deg[v] < dmax) cand[nc++] = v;
    if (nc == 0) { free(cand); return 0; }
    for (int i = nc - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    char *used = calloc(nc, 1);
    u64 *cov = calloc(W, sizeof(u64));
    int *chosen = malloc(sizeof(int) * (dmax + 1));
    int nch = 0, covered = 0;
    while (covered < n && nch < dmax) {
        int best = -1, bestg = 0;
        for (int i = 0; i < nc; i++) {
            if (used[i]) continue;
            const u64 *b = balls + (size_t)cand[i] * W;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(b[w] & ~cov[w]);
            if (g > bestg) { bestg = g; best = i; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = cand[best];
        const u64 *b = balls + (size_t)cand[best] * W;
        for (int w = 0; w < W; w++) cov[w] |= b[w];
        covered = count_bits(cov, W);
    }
    int ok = (covered == n);
    if (ok) {
        int w = n;
        n++;
        col[w] = side;
        deg[w] = 0;
        for (int i = 0; i < nch; i++) add_edge(chosen[i], w);
    }
    free(cand); free(used); free(cov); free(chosen);
    return ok;
}

/* Add one random spare cross edge (keeps bipartite, never hurts distances). */
static int perturb(void) {
    int *A = malloc(sizeof(int) * (n + 1));
    int *B = malloc(sizeof(int) * (n + 1));
    int na = 0, nb = 0, ok = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] >= dmax) continue;
        if (col[v] == 0) A[na++] = v; else B[nb++] = v;
    }
    if (na && nb) {
        for (int t = 0; t < 400 && !ok; t++) {
            int u = A[rndint(na)], v = B[rndint(nb)];
            if (!has_edge(u, v)) { add_edge(u, v); ok = 1; }
        }
    }
    free(A); free(B);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: prog d D seed time\n"); return 1; }
    dmax = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= seed * 0x2545F4914F6CDD1DULL + 1;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (dmax < 1 || n0 < 0) { printf("0 0\n"); return 0; }
    cap = n0 + 20000;
    adj = calloc((size_t)cap * dmax, sizeof(int));
    deg = calloc(cap, sizeof(int));
    col = calloc(cap, sizeof(int));
    n = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= dmax || deg[v] >= dmax || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    /* 2-colour the input graph by BFS. */
    for (int v = 0; v < n; v++) col[v] = -1;
    int *stack = malloc(sizeof(int) * (cap + 1));
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stack[sp++] = s;
        while (sp) {
            int u = stack[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int v = ADJ(u, i);
                if (col[v] == -1) { col[v] = 1 - col[u]; stack[sp++] = v; }
            }
        }
    }
    free(stack);

    clock_t t0 = clock();
    if (DIAM >= 2 && n > 0) {
        int R = DIAM - 1;
        int fails = 0;
        while (elapsed(t0) < tl && fails < 300 && n < cap) {
            int W = (n + 63) / 64;
            u64 *balls = balls_compute(R, W);
            int ins = 0;
            int first = rndint(2);
            for (int k = 0; k < 2 && !ins; k++) {
                int side = (k == 0) ? first : 1 - first;
                if (try_insert(side, balls, W)) ins = 1;
            }
            free(balls);
            if (ins) { fails = 0; continue; }
            fails++;
            if (!perturb()) break;
        }
    }

    long m = 0;
    for (int v = 0; v < n; v++)
        for (int i = 0; i < deg[v]; i++) if (ADJ(v, i) > v) m++;
    printf("%d %ld\n", n, m);
    for (int v = 0; v < n; v++)
        for (int i = 0; i < deg[v]; i++) {
            int u = ADJ(v, i);
            if (u > v) printf("%d %d\n", v, u);
        }
    free(adj); free(deg); free(col);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so spare capacity is s = d - q - 1. Choose S (a point set that is also a
# line index set) with every line holding <= s points of S and every point on
# <= s lines indexed by S. Add an A-vertex per P in S (joined to the lines
# through P) and a B-vertex per j in S (joined to the points on line j).
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
    """Conic (plus nucleus for even q): an arc with no three collinear."""
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
    for t, j in enumerate(S):  # S doubles as a set of line indices
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
# Generalized quadrangle W(q) baseline (D = 4).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (for D >= 4).
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
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within D. Zero means valid."""
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

    def at(frac):
        return t0 + frac * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(cand):
        nonlocal best, best_n
        if cand is None:
            return
        n, e = cand
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    rng = random.Random(seed)

    # 1. Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        arcs = _arc_extensions(d, at(0.10), random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for c in arcs[:3]:
            consider(c)

    # 2. Generalized quadrangle (diameter 4).
    if D >= 4 and time.monotonic() < at(0.20):
        consider(_best_gq(d))

    # 3. Annealed group voltage lifts (only where they help, D >= 4).
    if D >= 4:
        search_end = at(0.40)
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < search_end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            consider(_anneal(d, D, k, order, mul, rng, search_end, iters=400))

    # 4. C greedy vertex insertion, starting from the best graph so far.
    budget = at(0.80) - time.monotonic()
    if budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best,
                             timeout=budget + min(3.0, 0.1 * time_limit))
            n_c, e_c = lib.parse_graph_text(text)
            consider((n_c, e_c))
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
