import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: difference-cover search for Haar graphs (diameter 3).
#
# For an abelian group G of order m and a set S of size d in G, the Haar graph
# H(G, S) (A_x ~ B_{x+s}, s in S) has 2m vertices, degree d, and diameter <= 3
# exactly when S - S = G. The C code runs simulated annealing over S for each
# candidate group (cyclic or Z_a x Z_b), for orders m increasing from a lower
# bound, and prints the largest Haar graph it finds. If nothing is found it
# prints "0 0", and the Python side keeps its own fallback.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 512
#define MAXK 64
#define MAXGRP 32

static int M, GA, GB, K;
static int addt[MAXM][MAXM];
static int subt[MAXM][MAXM];
static int negt[MAXM];

static int S[MAXK];
static int inS[MAXM];
static int cnt[MAXM];
static int uncov;

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

static double now_s(void) {
    return (double)clock() / (double)CLOCKS_PER_SEC;
}

/* Group Z_a x Z_b, element x = i*b + j. */
static void setup_group(int a, int b) {
    GA = a;
    GB = b;
    M = a * b;
    for (int x = 0; x < M; x++) {
        int i1 = x / b, j1 = x % b;
        for (int y = 0; y < M; y++) {
            int i2 = y / b, j2 = y % b;
            addt[x][y] = ((i1 + i2) % a) * b + (j1 + j2) % b;
        }
    }
    for (int y = 0; y < M; y++) {
        for (int x = 0; x < M; x++) {
            if (addt[y][x] == 0) {
                negt[y] = x;
                break;
            }
        }
    }
    for (int x = 0; x < M; x++) {
        for (int y = 0; y < M; y++) {
            subt[x][y] = addt[x][negt[y]];
        }
    }
}

/* Add (sign=+1) or remove (sign=-1) the ordered differences between v and
   every element S[j] with j != excl. Keeps uncov = number of nonzero g with cnt[g]==0. */
static void upd_elem(int v, int sign, int excl) {
    for (int j = 0; j < K; j++) {
        if (j == excl) continue;
        int t = S[j];
        int d1 = subt[v][t];
        int d2 = subt[t][v];
        if (sign > 0) {
            if (cnt[d1]++ == 0) uncov--;
            if (cnt[d2]++ == 0) uncov--;
        } else {
            if (--cnt[d1] == 0) uncov++;
            if (--cnt[d2] == 0) uncov++;
        }
    }
}

static void init_state(void) {
    memset(inS, 0, sizeof(int) * (size_t)M);
    memset(cnt, 0, sizeof(int) * (size_t)M);
    for (int j = 0; j < K; j++) {
        int v;
        do {
            v = rndint(M);
        } while (inS[v]);
        S[j] = v;
        inS[v] = 1;
    }
    uncov = M - 1;
    for (int j = 0; j < K; j++) {
        for (int l = 0; l < K; l++) {
            if (l == j) continue;
            int d = subt[S[j]][S[l]];
            if (cnt[d]++ == 0) uncov--;
        }
    }
}

/* Simulated annealing with restarts on the current group. Returns 1 if S - S = G was reached. */
static int search_group(double until) {
    while (now_s() < until) {
        init_state();
        const long R = 300000;
        for (long step = 0; step < R; step++) {
            if (uncov == 0) return 1;
            if ((step & 1023) == 0 && now_s() >= until) return 0;
            double T = 0.9 * (1.0 - (double)step / (double)R) + 0.08;
            int i = rndint(K);
            int old = S[i];
            int v;
            do {
                v = rndint(M);
            } while (inS[v]);
            int before = uncov;
            upd_elem(old, -1, i);
            S[i] = v;
            upd_elem(v, +1, i);
            int delta = uncov - before;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                inS[old] = 0;
                inS[v] = 1;
            } else {
                upd_elem(v, -1, i);
                S[i] = old;
                upd_elem(old, +1, i);
            }
        }
        if (uncov == 0) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int lo = argc > 5 ? atoi(argv[5]) : 2;
    int hi = argc > 6 ? atoi(argv[6]) : MAXM - 1;

    rs ^= seed * 2654435761ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    K = d;
    if (D < 3 || K < 1 || K > MAXK) {
        printf("0 0\n");
        return 0;
    }

    long long cap = (long long)K * (K - 1) + 1;   /* Moore-type limit for a difference cover */
    long long mmax = hi;
    if (cap < mmax) mmax = cap;
    if (mmax > MAXM - 1) mmax = MAXM - 1;

    int found_m = 0, found_a = 0, found_b = 0;
    int foundS[MAXK];
    int start_m = lo < 2 ? 2 : lo;

    for (int m = start_m; m <= mmax; m++) {
        if (m <= K) continue;
        double t_now = now_s();
        double remaining = budget - t_now - 0.3;
        if (remaining <= 0) break;
        int share_n = (int)(mmax - m + 1);
        double slice = remaining / share_n;
        if (slice < 0.15) slice = 0.15;

        int ga[MAXGRP], gb[MAXGRP];
        int ng = 0;
        for (int a = 1; a * a <= m; a++) {
            if (m % a == 0) {
                int b = m / a;
                if (b % a == 0 && ng < MAXGRP) {
                    ga[ng] = a;
                    gb[ng] = b;
                    ng++;
                }
            }
        }
        if (ng == 0) continue;

        int ok = 0;
        for (int g = 0; g < ng && !ok; g++) {
            setup_group(ga[g], gb[g]);
            double per = slice / ng;
            double until = now_s() + per;
            if (search_group(until)) {
                ok = 1;
                found_m = m;
                found_a = ga[g];
                found_b = gb[g];
                memcpy(foundS, S, sizeof(int) * (size_t)K);
            }
        }
    }

    if (!found_m) {
        printf("0 0\n");
        return 0;
    }

    setup_group(found_a, found_b);
    int n = 2 * M;
    int E = M * K;
    printf("%d %d\n", n, E);
    for (int x = 0; x < M; x++) {
        for (int j = 0; j < K; j++) {
            printf("%d %d\n", x, M + addt[x][foundS[j]]);
        }
    }
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


def _arc_graph(m, edges, point_lines, S, line_points):
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
        n_c, e_c = _arc_graph(m, edges, point_lines, S, line_points)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Spare-capacity fill (diameter 3).
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """2-colouring of a bipartite graph given by adjacency lists."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _fill(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover the opposite side; return (n, edges)."""
    edges = list(edges)
    fails = 0
    while time.monotonic() < deadline and fails < 400:
        adj = [[] for _ in range(n)]
        for u, v in edges:
            adj[u].append(v)
            adj[v].append(u)
        deg = [len(a) for a in adj]
        col = _bipartition(n, adj)
        c = rng.randrange(2)
        uncovered = {v for v in range(n) if col[v] == 1 - c}
        cand = [v for v in range(n) if col[v] == c and deg[v] < d]
        chosen = []
        chosen_set = set()
        while uncovered and len(chosen) < d:
            best_v = None
            best_key = None
            for v in cand:
                if v in chosen_set:
                    continue
                g = 0
                for u in adj[v]:
                    if u in uncovered:
                        g += 1
                if g == 0:
                    continue
                key = (g, rng.random())
                if best_key is None or key > best_key:
                    best_key = key
                    best_v = v
            if best_v is None:
                break
            chosen.append(best_v)
            chosen_set.add(best_v)
            for u in adj[best_v]:
                uncovered.discard(u)
        if uncovered:
            fails += 1
            continue
        new_edges = edges + [(v, n) for v in chosen]
        if lib.is_valid(n + 1, new_edges, d, D):
            edges = new_edges
            n += 1
            fails = 0
        else:
            fails += 1
    return n, edges


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
# Difference-cover Haar search (D = 3): run the C engine.
# ----------------------------------------------------------------------------

def _haar_search(d, D, seed, budget, lo, timeout):
    """Run the C difference-cover search. Returns (n, edges), or (0, []) if nothing was found."""
    try:
        txt = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", lo, 100000],
                        stdin_graph=None, timeout=timeout)
        return lib.parse_graph_text(txt)
    except Exception:
        return 0, []


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
        # 1. Arc-extended projective plane graphs (fast).
        cands = _arc_extensions(d, start + 0.2 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

        # 2. Fill spare degree of the arc graph (bounded in time).
        if best_n > 2:
            n_f, e_f = _fill(best_n, best[1], d, D, start + 0.4 * time_limit,
                             random.Random(seed * 104729 + d))
            consider(n_f, e_f)

        # 3. Main bold search: difference covers of abelian groups give Haar graphs
        #    of diameter 3 on 2m vertices, degree d. Search m above the current best.
        elapsed = time.monotonic() - start
        budget = 0.78 * time_limit - elapsed - 1.0
        if budget > 1.0:
            lo = best_n // 2 + 1
            n_h, e_h = _haar_search(d, D, seed, budget, lo,
                                    timeout=max(1.0, 0.9 * time_limit - (time.monotonic() - start)))
            if n_h > best_n:
                consider(n_h, e_h)

        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    # D >= 4: parent-style constructions.
    deadline = start + 0.7 * time_limit

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
