import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: difference-cover search over small groups (D = 3).
#
# For a group G of order m and a k-subset S, let H(S) be the bipartite graph
# on A = G and B = G with a_x ~ b_{x s} for s in S. It is k-regular, and it has
# diameter <= 3 exactly when S S^{-1} = G and S^{-1} S = G (A-A and B-B pairs
# are then within 2, and A-B pairs within 3). The bound m <= k(k-1)+1 holds for
# every group. Non-abelian groups Z_m x|_r Z_k2 are searched as well as cyclic
# ones, which the Python parent did not try.
#
# Usage: prog d D seed time_limit [min_order]
# Prints the largest valid H(S) found with order >= min_order, or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define ITERS 100000
#define KMAX 64

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int K;             /* set size = degree d */
static int G;             /* group order */
static int *MUL = NULL;   /* G*G multiplication table */
static int *INV = NULL;   /* inverses */
static int *c1 = NULL, *c2 = NULL;
static int S[KMAX];
static int bestS[KMAX];

static long long pwmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static void free_group(void) {
    free(MUL); free(INV); free(c1); free(c2);
    MUL = NULL; INV = NULL; c1 = NULL; c2 = NULL;
}

/* Group Z_m x|_r Z_k2, element (a,b) coded a*k2+b:
   (a,b)(c,d) = (a + r^b c, b + d). Requires r^k2 = 1 mod m. */
static int build_group(int m, int k2, int r) {
    if (m < 1 || k2 < 1) return 0;
    if (pwmod(r, k2, m) != 1 % m) return 0;
    free_group();
    G = m * k2;
    long long *P = malloc(sizeof(long long) * (size_t)k2);
    P[0] = 1 % m;
    for (int b = 1; b < k2; b++) P[b] = P[b - 1] * r % m;
    MUL = malloc(sizeof(int) * (size_t)G * (size_t)G);
    INV = malloc(sizeof(int) * (size_t)G);
    c1 = malloc(sizeof(int) * (size_t)G);
    c2 = malloc(sizeof(int) * (size_t)G);
    if (!P || !MUL || !INV || !c1 || !c2) { free(P); free_group(); return 0; }
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, d = y % k2;
            long long aa = (a + P[b] * c) % m;
            MUL[(size_t)x * G + y] = (int)(aa * k2 + (b + d) % k2);
        }
    }
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        int nb = (k2 - b) % k2;
        long long ia = (m - (P[nb] * a) % m) % m;
        INV[x] = (int)(ia * k2 + nb);
    }
    free(P);
    for (int x = 0; x < G; x++) {
        if (MUL[(size_t)x * G + INV[x]] != 0) { free_group(); return 0; }
    }
    return 1;
}

/* Number of uncovered elements in S S^{-1} plus those in S^{-1} S. */
static int cost_of(void) {
    memset(c1, 0, sizeof(int) * (size_t)G);
    memset(c2, 0, sizeof(int) * (size_t)G);
    for (int i = 0; i < K; i++) {
        int si = S[i], ii = INV[si];
        for (int j = 0; j < K; j++) {
            int sj = S[j], ij = INV[sj];
            c1[MUL[(size_t)si * G + ij]]++;
            c2[MUL[(size_t)ii * G + sj]]++;
        }
    }
    int z = 0;
    for (int g = 0; g < G; g++) {
        if (!c1[g]) z++;
        if (!c2[g]) z++;
    }
    return z;
}

static int anneal(int iters) {
    char *in = calloc((size_t)G, 1);
    if (!in) return 0;
    for (int i = 0; i < K; i++) {
        int y;
        do { y = rndint(G); } while (in[y]);
        S[i] = y;
        in[y] = 1;
    }
    int cur = cost_of();
    for (int it = 0; it < iters && cur > 0; it++) {
        double T = 0.6 * (1.0 - (double)it / iters) + 0.03;
        int i = rndint(K), y = rndint(G);
        if (in[y]) continue;
        int old = S[i];
        S[i] = y;
        int c = cost_of();
        int delta = c - cur;
        if (delta <= 0 || rndu() < exp(-delta / T)) {
            cur = c;
            in[old] = 0;
            in[y] = 1;
        } else {
            S[i] = old;
        }
    }
    free(in);
    return cur == 0;
}

/* Random group of order Gt: cyclic, or Z_m x|_r Z_k2 with m >= 2. */
static void sample_group(int Gt, int *m, int *k2, int *r) {
    int cands[256], nc = 0;
    cands[nc++] = 1;
    for (int k = 2; k <= Gt / 2 && nc < 256; k++)
        if (Gt % k == 0 && Gt / k >= 2) cands[nc++] = k;
    int k = cands[rndint(nc)];
    if (k > 1) {
        int mm = Gt / k;
        for (int t = 0; t < 400; t++) {
            int rr = 1 + rndint(mm - 1);
            if (gcd_i(rr, mm) == 1 && pwmod(rr, k, mm) == 1 % mm) {
                *m = mm; *k2 = k; *r = rr;
                return;
            }
        }
    }
    *m = Gt; *k2 = 1; *r = 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int minG = argc > 5 ? atoi(argv[5]) : 2;
    if (minG < 2) minG = 2;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (D != 3 || d < 2 || d > KMAX) { printf("0 0\n"); return 0; }
    K = d;
    clock_t t0 = clock();
    int lo = minG;
    int hi = d * (d - 1) + 1;
    int bestG = 0, bestM = 0, bestK2 = 0, bestR = 0;

    while (lo <= hi && (double)(clock() - t0) / CLOCKS_PER_SEC < tl) {
        int Gt = lo + rndint(hi - lo + 1);
        if (Gt < K) continue;
        int m, k2, r;
        sample_group(Gt, &m, &k2, &r);
        if (!build_group(m, k2, r)) continue;
        if (anneal(ITERS)) {
            bestG = G; bestM = m; bestK2 = k2; bestR = r;
            memcpy(bestS, S, sizeof(int) * (size_t)K);
            lo = G + 1;
        }
        free_group();
    }

    if (bestG == 0 || !build_group(bestM, bestK2, bestR)) {
        printf("0 0\n");
        return 0;
    }
    int n = 2 * G, me = G * K;
    printf("%d %d\n", n, me);
    for (int x = 0; x < G; x++)
        for (int i = 0; i < K; i++)
            printf("%d %d\n", x, G + MUL[(size_t)x * G + bestS[i]]);
    free_group();
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
# C-backed difference-cover search (D = 3).
# ----------------------------------------------------------------------------

def _c_cover(d, budget, min_n_half, seed):
    """Run the C group difference-cover search; returns (n, edges) or None."""
    if budget < 0.5:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, 3, seed, round(budget, 2), min_n_half],
                        timeout=budget + 15.0)
        n, e = lib.parse_graph_text(out)
    except Exception:
        return None
    if n < 4:
        return None
    return n, e


# ----------------------------------------------------------------------------
# Ball-cover greedy vertex insertion ("_augment").
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
        # Arc-extended projective plane graphs (fast, deterministic baseline).
        arcs = _arc_extensions(d, start + 0.08 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)
        # New: non-abelian difference-cover Haar graphs, searched in C.
        # Only orders above the current best half-order are searched.
        if 3 <= d <= 64:
            budget = start + 0.88 * time_limit - time.monotonic() - 1.0
            cov = _c_cover(d, budget, best_n // 2 + 1, seed % 1000003 + 1)
            if cov is not None:
                consider(cov[0], cov[1])
    else:
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

        if D >= 2 and time.monotonic() < start + 0.85 * time_limit:
            n_f, e_f = _augment(best[0], best[1], d, D, rng, start + 0.85 * time_limit)
            consider(n_f, e_f)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
