import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: cyclic Haar graphs H(m, S) from difference covers (diameter 3).
#
# S is a k-subset of Z_m whose nonzero differences cover Z_m \ {0}. Then the
# bipartite graph a_i ~ b_{i+s} (s in S) has diameter 3 and is k-regular on
# 2m vertices. The search is simulated annealing on the number of uncovered
# residues, with focused moves that create a currently missing difference.
# The engine climbs m upward from a safe start and keeps retrying the first
# m it cannot cover, so it keeps going for m above the best found so far.
# Output: "n m" then edges, or "0 0" if nothing is found or D < 3.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rnd_unit(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double cpu_now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int M, K, zeros;
static int *S, *inS, *cnt;

static int md(int x) {
    x %= M;
    return x < 0 ? x + M : x;
}

/* Replace S[i] by y (y not in S), keeping cnt[] and zeros up to date. */
static void set_elem(int i, int y) {
    int old = S[i];
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        int t = S[j];
        if (--cnt[md(old - t)] == 0) zeros++;
        if (--cnt[md(t - old)] == 0) zeros++;
    }
    inS[old] = 0;
    S[i] = y;
    inS[y] = 1;
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        int t = S[j];
        if (cnt[md(y - t)]++ == 0) zeros--;
        if (cnt[md(t - y)]++ == 0) zeros--;
    }
}

static void init_state(void) {
    for (int x = 0; x < M; x++) {
        inS[x] = 0;
        cnt[x] = 0;
    }
    int c = 0;
    while (c < K) {
        int y = rnd_int(M);
        if (!inS[y]) {
            inS[y] = 1;
            S[c++] = y;
        }
    }
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            if (i != j) cnt[md(S[i] - S[j])]++;
    zeros = 0;
    for (int x = 1; x < M; x++)
        if (cnt[x] == 0) zeros++;
}

/* Returns 1 if a full difference cover was reached before slice_end (CPU seconds). */
static int search(double slice_end) {
    const double Thi = 0.8, Tlo = 0.05;
    const long cyc = 4000000L;
    long it = 0;
    double T = Thi;
    while (zeros > 0) {
        it++;
        if ((it & 4095) == 0) {
            if (cpu_now() > slice_end) return 0;
            long ph = it % cyc;
            T = Thi * pow(Tlo / Thi, (double)ph / (double)cyc);
        }
        int i = rnd_int(K);
        int old = S[i];
        int y;
        if (rnd_int(2) == 0) {
            /* focused move: create a missing difference x = y - t or t - y */
            int x = -1;
            for (int tr = 0; tr < 40; tr++) {
                int z = 1 + rnd_int(M - 1);
                if (cnt[z] == 0) {
                    x = z;
                    break;
                }
            }
            if (x < 0) continue;
            int t = S[rnd_int(K)];
            y = (rnd_int(2) == 0) ? md(t + x) : md(t - x);
        } else {
            y = rnd_int(M);
        }
        if (y == old || inS[y]) continue;
        int z0 = zeros;
        set_elem(i, y);
        int delta = zeros - z0;
        if (delta > 0 && rnd_unit() >= exp(-(double)delta / T)) set_elem(i, old);
    }
    return 1;
}

int main(int argc, char **argv) {
    int d = argc > 1 ? atoi(argv[1]) : 3;
    int D = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long seed = argc > 3 ? strtoul(argv[3], NULL, 10) : 1UL;
    double budget = argc > 4 ? atof(argv[4]) : 10.0;
    if (D < 3 || d < 3) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;

    K = d;
    int cap = K * (K - 1) + 1;
    S = malloc(sizeof(int) * (size_t)K);
    inS = malloc(sizeof(int) * (size_t)(cap + 2));
    cnt = malloc(sizeof(int) * (size_t)(cap + 2));
    int *bestS = malloc(sizeof(int) * (size_t)K);
    int best_m = 0;

    double deadline = cpu_now() + budget;
    int m = (int)(0.8 * cap);
    if (m < K + 1) m = K + 1;
    while (cpu_now() < deadline && m >= K + 1 && m <= cap) {
        M = m;
        double now = cpu_now();
        double remain = deadline - now;
        double slice = remain * 0.25;
        if (slice < 1.0) slice = remain;
        init_state();
        if (search(now + slice)) {
            best_m = m;
            memcpy(bestS, S, sizeof(int) * (size_t)K);
            m++;
        } else if (best_m == 0) {
            m--;
        }
    }

    if (best_m == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", 2 * best_m, K * best_m);
    for (int i = 0; i < best_m; i++)
        for (int j = 0; j < K; j++)
            printf("%d %d\n", i, best_m + (i + bestS[j]) % best_m);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Old vertices
# have degree q+1, so spare s = d - q - 1. Choose S (points) so that each line
# contains <= s points of S, and each point lies on <= s lines indexed by S.
# Add an A-vertex per point of S (joined to lines through it) and a B-vertex
# per line of S (joined to points on it). Diameter stays 3.
# ----------------------------------------------------------------------------

def _pg_data(q):
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
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
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
# Greedy vertex insertion with ball-cover certificates.
# A new vertex w joined to chosen vertices on the opposite side reaches x
# within D exactly when x lies within distance D-1 of some chosen neighbour.
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
# Generalized quadrangle W(q) incidence graph (diameter 4), for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 4).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
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

    if D == 2:
        return best

    # Stage 1: arc-extended projective planes (diameter 3, instant record-level).
    if D >= 3:
        arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)
        if arcs:
            n_a, e_a = arcs[0]
            n2, e2 = _augment(n_a, e_a, d, D, rng, start + 0.18 * time_limit)
            consider(n2, e2)

    # Stage 2: C search for difference-cover Haar graphs (diameter 3, valid for D >= 3).
    c_frac = 0.75 if D == 3 else 0.40
    c_end = start + c_frac * time_limit
    budget = c_end - time.monotonic() - 2.0
    if budget > 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)], stdin_graph=None,
                            timeout=max(1.0, time_limit * 0.9 - (time.monotonic() - start)))
            n_c, e_c = lib.parse_graph_text(out)
            consider(n_c, e_c)
        except Exception:
            pass

    # Stage 3: generalized quadrangle and annealed group lifts for D >= 4.
    if D >= 4:
        if time.monotonic() < start + 0.5 * time_limit:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        search_end = start + 0.8 * time_limit
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

    # Stage 4: final greedy augmentation of the best graph found.
    if time.monotonic() < start + 0.85 * time_limit:
        n_f, e_f = _augment(best[0], best[1], d, D, rng, start + 0.85 * time_limit)
        consider(n_f, e_f)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
