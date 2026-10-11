import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine for D = 3: cyclic and non-abelian Haar graphs from difference covers.
#
# For a group G of order m and a k-subset S, the bipartite graph with a_g ~ b_{gs}
# (s in S) is k-regular on 2m vertices. A-A distances are <= 2 exactly when
# S S^{-1} covers G \ {1}; A-B distances are then <= 3 automatically. So the
# search needs a difference cover of size k = d in some group of order m, and
# m <= k(k-1)+1 gives the Moore-type ceiling 2(k(k-1)+1).
#
# Groups are semidirect products Z_A x| Z_B with element (a, b) coded as a*B+b
# and product (a1,b1)(a2,b2) = (a1 + r^{b1} a2, b1 + b2), with r^B = 1 mod A.
# Cyclic groups are (A=m, B=1); other choices are non-cyclic or dihedral-like.
# Simulated annealing minimises the number of uncovered non-identity elements.
# The order m increases round by round; each round doubles the move budget.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rng_state = 1;

static uint64_t rnd64(void) {
    uint64_t z = (rng_state += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rnd_unit(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int pow_mod(int base, int e, int mod) {
    long long res = 1 % mod;
    long long b = ((long long)base % mod + mod) % mod;
    while (e > 0) {
        if (e & 1) res = res * b % mod;
        b = b * b % mod;
        e >>= 1;
    }
    return (int)res;
}

static int semi_mul(int A, int B, const int *pw, int x, int y) {
    int a1 = x / B, b1 = x % B, a2 = y / B, b2 = y % B;
    int a = (int)(((long long)a1 + (long long)pw[b1] * a2) % A);
    int b = (b1 + b2) % B;
    return a * B + b;
}

typedef struct {
    int A, B, m;
    int *pw;
    int *mul;
    int *inv;
} Group;

static void group_free(Group *G) {
    free(G->pw);
    free(G->mul);
    free(G->inv);
    G->pw = NULL;
    G->mul = NULL;
    G->inv = NULL;
}

static int group_build(Group *G, int A, int B, int r) {
    int m = A * B;
    G->A = A;
    G->B = B;
    G->m = m;
    G->pw = malloc(sizeof(int) * (size_t)B);
    G->mul = malloc(sizeof(int) * (size_t)m * (size_t)m);
    G->inv = malloc(sizeof(int) * (size_t)m);
    for (int b = 0; b < B; b++) G->pw[b] = pow_mod(r, b, A);
    for (int x = 0; x < m; x++)
        for (int y = 0; y < m; y++)
            G->mul[x * m + y] = semi_mul(A, B, G->pw, x, y);
    for (int x = 0; x < m; x++) {
        int found = -1;
        for (int y = 0; y < m; y++)
            if (G->mul[x * m + y] == 0) { found = y; break; }
        if (found < 0) { group_free(G); return 0; }
        G->inv[x] = found;
    }
    return 1;
}

/* Replace S[i] by y, keeping cnt[x] = #ordered pairs (s,t), s != t, with s t^{-1} = x,
   and zeros = #{x != 0 : cnt[x] = 0}. */
static void replace_elem(const Group *G, int k, int *S, char *inS, int *cnt,
                         int *zeros, int i, int y) {
    const int m = G->m;
    const int *mul = G->mul, *inv = G->inv;
    int old = S[i];
    for (int j = 0; j < k; j++) {
        if (j == i) continue;
        int t = S[j];
        int x = mul[old * m + inv[t]];
        if (--cnt[x] == 0) (*zeros)++;
        x = mul[t * m + inv[old]];
        if (--cnt[x] == 0) (*zeros)++;
    }
    inS[old] = 0;
    S[i] = y;
    inS[y] = 1;
    for (int j = 0; j < k; j++) {
        if (j == i) continue;
        int t = S[j];
        int x = mul[y * m + inv[t]];
        if (cnt[x]++ == 0) (*zeros)--;
        x = mul[t * m + inv[y]];
        if (cnt[x]++ == 0) (*zeros)--;
    }
}

static int anneal(const Group *G, int k, long long iters, double deadline, int *outS) {
    const int m = G->m;
    int *S = malloc(sizeof(int) * (size_t)k);
    char *inS = calloc((size_t)m, 1);
    int *cnt = calloc((size_t)m, sizeof(int));
    int zeros = 0, found = 0;
    for (int i = 0; i < k; ) {
        int y = rnd_int(m);
        if (!inS[y]) { inS[y] = 1; S[i++] = y; }
    }
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            if (i != j) cnt[G->mul[S[i] * m + G->inv[S[j]]]]++;
    for (int x = 1; x < m; x++) if (cnt[x] == 0) zeros++;

    const double T0 = 0.8, T1 = 0.03;
    const double lr = log(T1 / T0);
    for (long long it = 0; it < iters && zeros > 0; it++) {
        if ((it & 1023) == 0 && now_s() > deadline) break;
        double T = T0 * exp(lr * (double)it / (double)iters);
        int i = rnd_int(k), y = rnd_int(m);
        if (inS[y]) continue;
        int old = S[i];
        int z0 = zeros;
        replace_elem(G, k, S, inS, cnt, &zeros, i, y);
        int delta = zeros - z0;
        if (delta > 0 && rnd_unit() >= exp(-(double)delta / T))
            replace_elem(G, k, S, inS, cnt, &zeros, i, old);
    }
    if (zeros == 0) {
        found = 1;
        memcpy(outS, S, sizeof(int) * (size_t)k);
    }
    free(S);
    free(inS);
    free(cnt);
    return found;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (D != 3 || d < 3 || d > 200) { printf("0 0\n"); return 0; }

    double deadline = now_s() + tl;
    rng_state = (uint64_t)seed * 0x2545F4914F6CDD1DULL + 0x51ED27ULL;
    int k = d;
    int cap = k * (k - 1) + 1;

    /* Fallback: cyclic Z_k with S = whole group, i.e. K_{k,k}. */
    int best_m = k, bA = k, bB = 1, br = 1;
    int *best_S = malloc(sizeof(int) * (size_t)k);
    for (int i = 0; i < k; i++) best_S[i] = i;
    int *S = malloc(sizeof(int) * (size_t)k);

    int lo = cap / 2;
    if (lo < k + 1) lo = k + 1;
    long long iters = 100000;
    const int NG = 6;
    Group G;

    while (best_m < cap && now_s() < deadline) {
        int mstart = (best_m + 1 > lo) ? best_m + 1 : lo;
        for (int m = mstart; m <= cap; m++) {
            if (now_s() >= deadline) break;
            int maxc = 6 * m + 16;
            int *cA = malloc(sizeof(int) * (size_t)maxc);
            int *cB = malloc(sizeof(int) * (size_t)maxc);
            int *cR = malloc(sizeof(int) * (size_t)maxc);
            int nc = 0;
            cA[nc] = m; cB[nc] = 1; cR[nc] = 1; nc++;
            for (int A = 2; A < m; A++) {
                if (m % A) continue;
                int B = m / A;
                if (B < 2) continue;
                for (int r = 1; r < A; r++) {
                    if (gcd_i(r, A) != 1) continue;
                    if (pow_mod(r, B, A) != 1 % A) continue;
                    if (nc < maxc) {
                        cA[nc] = A; cB[nc] = B; cR[nc] = r; nc++;
                    }
                }
            }
            for (int i = nc - 1; i > 0; i--) {
                int j = rnd_int(i + 1);
                int tA = cA[i], tB = cB[i], tR = cR[i];
                cA[i] = cA[j]; cB[i] = cB[j]; cR[i] = cR[j];
                cA[j] = tA; cB[j] = tB; cR[j] = tR;
            }
            int tries = nc < NG ? nc : NG;
            int ok = 0;
            for (int t = 0; t < tries && !ok && now_s() < deadline; t++) {
                if (!group_build(&G, cA[t], cB[t], cR[t])) continue;
                if (anneal(&G, k, iters, deadline, S)) {
                    ok = 1;
                    best_m = m;
                    bA = cA[t];
                    bB = cB[t];
                    br = cR[t];
                    memcpy(best_S, S, sizeof(int) * (size_t)k);
                }
                group_free(&G);
            }
            free(cA);
            free(cB);
            free(cR);
            if (best_m >= cap) break;
        }
        iters *= 2;
        if (iters > 4000000000LL) iters = 4000000000LL;
    }

    {
        int m = best_m;
        int *pw = malloc(sizeof(int) * (size_t)bB);
        for (int b = 0; b < bB; b++) pw[b] = pow_mod(br, b, bA);
        printf("%d %d\n", 2 * m, m * k);
        for (int g = 0; g < m; g++)
            for (int i = 0; i < k; i++) {
                int h = semi_mul(bA, bB, pw, g, best_S[i]);
                printf("%d %d\n", g, m + h);
            }
        free(pw);
    }
    free(best_S);
    free(S);
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
# P in S add a new A-vertex joined to the q+1 lines through P; for each j in S
# add a new B-vertex joined to the q+1 points on line j.
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
# Greedy vertex insertion with ball-cover certificates ("_augment").
#
# Let R = D-1 and let ball(u) be the set of vertices within distance R of u.
# A new vertex w joined to a set N of vertices on the opposite colour class
# reaches x within D exactly when x lies in ball(u) for some u in N.
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
        # Cheap projective-plane candidates first.
        arcs = _arc_extensions(d, start + 0.05 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)
        # Main construction: C search over groups of order m for difference covers of size d.
        remaining = time_limit - (time.monotonic() - start)
        c_budget = max(1.0, remaining * 0.75 - 3.0)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                             timeout=max(1.0, remaining * 0.9))
            n_h, e_h = lib.parse_graph_text(text)
            consider(n_h, e_h)
        except (RuntimeError, ValueError):
            pass
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
