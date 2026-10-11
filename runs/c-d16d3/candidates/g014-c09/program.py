import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: difference-cover Haar graphs (D = 3).
#
# The Haar graph of Z_m with connection set S (|S| = d) is d-regular and bipartite:
# a_i ~ b_{i+s} for s in S. Its diameter is at most 3 whenever S - S = Z_m:
#   - two A-vertices a_i, a_{i'} share a neighbour iff i' - i = s - t for some s != t in S;
#   - an A-B pair is joined by a_i - b_{i+s} - a_{i+s-t} - b_{i+s-t+u}, covering every target.
# So the task is: find the largest m such that some d-subset of Z_m has all m-1 nonzero
# differences covered. The order is 2m, and the Moore bound gives m <= d(d-1)+1.
# The C search does hill-climbing on the number of covered differences.
# If the search fails or the output is bad, Python keeps its valid fallback.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXM 4096

static uint64_t rng_state = 88172645463325252ULL;

static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}

static double rnd01(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static int M, K;
static int S[MAXD];
static int inS[MAXM];
static int cnt[MAXM];
static int cov;

/* cnt[x] = number of ordered pairs (s, t), s != t in S, with s - t = x (mod M). cov = #{x != 0 : cnt[x] > 0}. */
static void bump(int x, int v) {
    if (v > 0) {
        if (cnt[x] == 0) cov++;
        cnt[x]++;
    } else {
        cnt[x]--;
        if (cnt[x] == 0) cov--;
    }
}

/* Add (v = +1) or remove (v = -1) element s against all members of S except index skip. */
static void touch(int s, int skip, int v) {
    for (int j = 0; j < K; j++) {
        if (j == skip) continue;
        int t = S[j];
        int x = ((s - t) % M + M) % M;
        bump(x, v);
        bump((M - x) % M, v);
    }
}

static void build_cnt(void) {
    memset(cnt, 0, sizeof(int) * (size_t)M);
    cov = 0;
    for (int i = 0; i < K; i++) {
        for (int j = 0; j < i; j++) {
            int x = ((S[i] - S[j]) % M + M) % M;
            bump(x, 1);
            bump((M - x) % M, 1);
        }
    }
}

/* Search for a K-subset of Z_m covering all nonzero differences. Returns 1 and fills out on success. */
static int try_m(int m, double slice_sec, int *out) {
    M = m;
    clock_t t0 = clock();
    while (1) {
        memset(inS, 0, sizeof(int) * (size_t)M);
        for (int i = 0; i < K; i++) {
            int r;
            do {
                r = (int)(rnd() % (uint64_t)M);
            } while (inS[r]);
            inS[r] = 1;
            S[i] = r;
        }
        build_cnt();
        long steps = 0;
        const double T = 0.6;
        while (steps < 3000000L) {
            if (cov == M - 1) {
                memcpy(out, S, sizeof(int) * (size_t)K);
                return 1;
            }
            steps++;
            if ((steps & 4095L) == 0) {
                double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
                if (el > slice_sec) return 0;
            }
            int i = (int)(rnd() % (uint64_t)K);
            int s = S[i];
            int r;
            do {
                r = (int)(rnd() % (uint64_t)M);
            } while (inS[r]);
            int old = cov;
            touch(s, i, -1);
            touch(r, i, +1);
            int nw = cov;
            if (nw >= old || rnd01() < exp((double)(nw - old) / T)) {
                inS[s] = 0;
                inS[r] = 1;
                S[i] = r;
            } else {
                touch(r, i, -1);
                touch(s, i, +1);
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rng_state = (uint64_t)seed * 2654435761ULL + 0x9E3779B97F4A7C15ULL;
    if (rng_state == 0) rng_state = 1;
    if (D != 3 || d < 2 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    K = d;
    int mmax = d * (d - 1) + 1;
    if (mmax > MAXM - 1) mmax = MAXM - 1;

    int best = 0;
    int bestS[MAXD];
    int tmpS[MAXD];
    int fails = 0;
    int m = d + 1;
    clock_t tstart = clock();
    while (m <= mmax && fails < 3) {
        double used = (double)(clock() - tstart) / CLOCKS_PER_SEC;
        double remain = tl - used;
        if (remain < 0.2) break;
        double slice = tl * 0.12;
        if (slice < 0.3) slice = 0.3;
        if (slice > remain) slice = remain;
        int ok = try_m(m, slice, tmpS);
        if (ok) {
            best = m;
            memcpy(bestS, tmpS, sizeof(int) * (size_t)d);
            fails = 0;
        } else {
            fails++;
        }
        m++;
    }

    if (best == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", 2 * best, best * d);
    for (int i = 0; i < best; i++) {
        for (int j = 0; j < d; j++) {
            printf("%d %d\n", i, best + (i + bestS[j]) % best);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), Python fallback.
#
# Start from PG(2, q). Each old vertex has degree q+1, so it has spare s = d-q-1.
# Add an A-vertex for each chosen point (joined to its q+1 lines) and a B-vertex for
# each chosen line (joined to its q+1 points), keeping loads at most s.
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


def _loads_ok(S, s, m, nbr):
    """True if every target t is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements x so that every target is hit by <= s chosen elements."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
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


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
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
    deadline = start + 0.7 * time_limit
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
        # Python fallback first: arc-extended projective plane graphs (cheap, diameter 3).
        try:
            cands = _arc_extensions(d, deadline, random.Random(seed * 7919 + d))
            for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
                consider(n_c, e_c)
        except Exception:
            pass

        # Bold change: difference-cover Haar graphs searched in C.
        # Z_m with a d-subset S covering all nonzero differences gives a d-regular bipartite
        # graph of order 2m and diameter 3.
        c_budget = max(1.0, 0.6 * time_limit)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}"],
                             stdin_graph=None, timeout=0.8 * time_limit)
            n_c, e_c = lib.parse_graph_text(text)
            consider(n_c, e_c)
        except Exception:
            pass
    else:
        # Parent pipeline for other diameters.
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
