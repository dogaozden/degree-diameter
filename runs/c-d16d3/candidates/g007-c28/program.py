import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: greedy vertex insertion with ball-cover certificates.
#
# A new vertex w joined to a set N of opposite-colour vertices keeps diameter D
# exactly when every old vertex lies within distance D-1 of some u in N. Adding
# vertices or cross edges never increases old distances, so validity is kept.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd64() % (u64)k); }

static int popc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int n, dmax, Dd, Wc;
static int **adj;
static int *deg, *col;
static u64 *bufA, *bufB, *cur, *nxt;

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void compute_balls(int R) {
    int Wn = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < Wc; w++) cur[(size_t)v * Wc + w] = 0;
        cur[(size_t)v * Wc + (v >> 6)] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            u64 *dst = &nxt[(size_t)v * Wc];
            u64 *src = &cur[(size_t)v * Wc];
            for (int w = 0; w < Wn; w++) dst[w] = src[w];
            for (int i = 0; i < deg[v]; i++) {
                u64 *s2 = &cur[(size_t)adj[v][i] * Wc];
                for (int w = 0; w < Wn; w++) dst[w] |= s2[w];
            }
        }
        u64 *t = cur; cur = nxt; nxt = t;
    }
}

static int is_full(const u64 *c) {
    int Wn = (n + 63) / 64;
    for (int w = 0; w < Wn - 1; w++) if (c[w] != ~0ULL) return 0;
    int rem = n - 64 * (Wn - 1);
    u64 mask = (rem == 64) ? ~0ULL : ((1ULL << rem) - 1);
    return (c[Wn - 1] & mask) == mask;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dmax = atoi(argv[1]);
    Dd = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || m0 < 0) { printf("0 0\n"); return 0; }
    int *eu = malloc(sizeof(int) * (m0 + 1));
    int *ev = malloc(sizeof(int) * (m0 + 1));
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { printf("0 0\n"); return 0; }
    }

    /* Check the start graph: ranges, degrees. Otherwise echo it back unchanged. */
    int ok = 1;
    int *d0 = calloc(n0, sizeof(int));
    for (int i = 0; i < m0 && ok; i++) {
        if (eu[i] < 0 || eu[i] >= n0 || ev[i] < 0 || ev[i] >= n0 || eu[i] == ev[i]) ok = 0;
        else { d0[eu[i]]++; d0[ev[i]]++; }
    }
    for (int v = 0; v < n0 && ok; v++) if (d0[v] > dmax) ok = 0;
    if (!ok) {
        printf("%d %d\n", n0, m0);
        for (int i = 0; i < m0; i++) printf("%d %d\n", eu[i], ev[i]);
        return 0;
    }

    int cap = 4 * n0 + 200;
    if (cap > 8000) cap = 8000;
    if (cap < n0 + 1) cap = n0 + 1;
    Wc = (cap + 63) / 64;

    adj = malloc(sizeof(int *) * cap);
    for (int v = 0; v < cap; v++) adj[v] = malloc(sizeof(int) * dmax);
    deg = calloc(cap, sizeof(int));
    col = malloc(sizeof(int) * cap);
    bufA = calloc((size_t)cap * Wc, sizeof(u64));
    bufB = calloc((size_t)cap * Wc, sizeof(u64));
    cur = bufA; nxt = bufB;
    int *cand = malloc(sizeof(int) * cap);
    char *used = malloc(sizeof(char) * cap);
    int *chosen = malloc(sizeof(int) * (dmax + 1));
    u64 *covered = malloc(sizeof(u64) * Wc);
    int *q = malloc(sizeof(int) * cap);

    n = n0;
    for (int i = 0; i < m0; i++) add_edge(eu[i], ev[i]);

    /* Bipartition check. */
    for (int v = 0; v < n; v++) col[v] = -1;
    int bad = 0;
    for (int s = 0; s < n && !bad; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail && !bad) {
            int u = q[head++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) { col[v] = 1 - col[u]; q[tail++] = v; }
                else if (col[v] == col[u]) { bad = 1; break; }
            }
        }
    }
    if (bad) {
        printf("%d %d\n", n0, m0);
        for (int i = 0; i < m0; i++) printf("%d %d\n", eu[i], ev[i]);
        return 0;
    }

    int R = Dd - 1;
    int fails = 0;
    double t0 = (double)clock() / CLOCKS_PER_SEC;
    if (R >= 1) {
        while (fails < 20000) {
            double el = (double)clock() / CLOCKS_PER_SEC - t0;
            if (el > tl) break;
            if (n >= cap) break;
            compute_balls(R);
            int Wn = (n + 63) / 64;
            int inserted = 0;
            int first = rndint(2);
            for (int tries = 0; tries < 2 && !inserted; tries++) {
                int s = (tries == 0) ? first : 1 - first;
                int nc = 0;
                for (int u = 0; u < n; u++)
                    if (col[u] != s && deg[u] < dmax) cand[nc++] = u;
                if (nc == 0) continue;
                for (int i = nc - 1; i > 0; i--) {
                    int j = rndint(i + 1);
                    int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
                }
                memset(used, 0, nc);
                memset(covered, 0, sizeof(u64) * Wc);
                int k = 0;
                while (k < dmax && !is_full(covered)) {
                    int bi = -1, bg = 0;
                    for (int i = 0; i < nc; i++) {
                        if (used[i]) continue;
                        const u64 *bl = &cur[(size_t)cand[i] * Wc];
                        int g = 0;
                        for (int w = 0; w < Wn; w++) g += popc64(bl[w] & ~covered[w]);
                        if (g > bg) { bg = g; bi = i; }
                    }
                    if (bi < 0) break;
                    used[bi] = 1;
                    chosen[k++] = cand[bi];
                    const u64 *bl = &cur[(size_t)cand[bi] * Wc];
                    for (int w = 0; w < Wn; w++) covered[w] |= bl[w];
                }
                if (is_full(covered)) {
                    int w = n++;
                    col[w] = s;
                    deg[w] = 0;
                    for (int i = 0; i < k; i++) add_edge(chosen[i], w);
                    inserted = 1;
                }
            }
            if (inserted) { fails = 0; continue; }
            fails++;
            /* Perturbation: add a spare cross edge (keeps validity and bipartiteness). */
            for (int t = 0; t < 200; t++) {
                int u = rndint(n), v = rndint(n);
                if (u == v || col[u] == col[v] || deg[u] >= dmax || deg[v] >= dmax) continue;
                if (col[u] == 1) { int tmp = u; u = v; v = tmp; }
                if (has_edge(u, v)) continue;
                add_edge(u, v);
                break;
            }
        }
    }

    long m = 0;
    for (int u = 0; u < n; u++) m += deg[u];
    m /= 2;
    printf("%d %ld\n", n, m);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++) {
            int v = adj[u][i];
            if (u < v) printf("%d %d\n", u, v);
        }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each vertex has
# degree q+1, so with d >= q+1 there is spare capacity s = d-q-1. Choose a point
# set S with every line holding <= s points of S and every point on <= s lines
# indexed by S. Add an A-vertex per P in S (joined to the lines through P) and a
# B-vertex per j in S (joined to the points on j). Diameter stays 3.
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
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used only for D >= 4.
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
# Simulated annealing over bi-Cayley voltage lifts (from the parent programs).
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
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # 1. Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in arcs:
            consider(n_c, e_c)

    # 2. Generalized quadrangle for D >= 4.
    if D >= 4 and time.monotonic() < start + 0.20 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # 3. Annealed group voltage lifts, a short slice of the budget.
    search_end = start + 0.25 * time_limit
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
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

    # 4. C engine: greedy vertex insertion with ball-cover certificates,
    #    starting from the largest valid graph found so far.
    deadline = start + 0.85 * time_limit
    if D >= 2 and time.monotonic() < deadline - 1.0:
        budget = deadline - time.monotonic()
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=budget + 5.0)
            n_c, e_c = lib.parse_graph_text(out)
            consider(n_c, e_c)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
