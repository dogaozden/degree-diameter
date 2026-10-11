import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# A-side: a set SA of points. Each SA point P gets a new vertex joined to all
#         q+1 lines through P. Constraint: every line holds <= s points of SA.
# B-side: a set SB of lines. Each j in SB gets a new vertex joined to all q+1
#         points on j. Constraint: every point lies on <= s lines of SB.
#
# The two sides are independent, so SA and SB are maximized separately.
# Order is 2(q^2+q+1) + |SA| + |SB|. Diameter stays 3 for any SA, SB.
#
# Change in this version: the side sets are found by a C engine (SIDE_C), an
# iterated plateau search with swaps, kicks and restarts from the best set.
# It runs ~100x more moves per second than the Python local search. Every
# candidate still goes through the load check and lib.is_valid.
# ----------------------------------------------------------------------------

SIDE_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static unsigned long long rs = 88172645463325252ULL;
static unsigned long long nextr(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs;
}
static int rndint(int n) { return (int)(nextr() % (unsigned long long)n); }
static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int N, M, LIM;
static int *off, *adjv, *roff, *radjv;
static int *inS, *load, *cur, *pos, *best;
static int curk, bestk;

static void add_el(int x) {
    inS[x] = 1; pos[x] = curk; cur[curk++] = x;
    for (int i = off[x]; i < off[x + 1]; i++) load[adjv[i]]++;
}
static void rem_el(int x) {
    inS[x] = 0;
    int p = pos[x];
    int last = cur[--curk];
    cur[p] = last; pos[last] = p; pos[x] = -1;
    for (int i = off[x]; i < off[x + 1]; i++) load[adjv[i]]--;
}
static int can_add(int x) {
    for (int i = off[x]; i < off[x + 1]; i++) if (load[adjv[i]] >= LIM) return 0;
    return 1;
}
static void save_best(void) {
    bestk = curk;
    memcpy(best, cur, sizeof(int) * (size_t)curk);
}
static void load_best(void) {
    while (curk > 0) rem_el(cur[curk - 1]);
    for (int i = 0; i < bestk; i++) add_el(best[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    double tl = atof(argv[1]);
    LIM = atoi(argv[2]);
    rs ^= (unsigned long long)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int w = 0; w < 10; w++) nextr();

    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 1;
    N = atoi(argv[4]);
    M = n - N;
    if (N <= 0 || M <= 0) { printf("0\n\n"); return 0; }

    int *eu = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    int *ev = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) return 1;
        if (eu[i] > ev[i]) { int t = eu[i]; eu[i] = ev[i]; ev[i] = t; }
    }

    off = calloc(N + 1, sizeof(int));
    roff = calloc(M + 1, sizeof(int));
    for (int i = 0; i < m; i++) { off[eu[i] + 1]++; roff[ev[i] - N + 1]++; }
    for (int x = 0; x < N; x++) off[x + 1] += off[x];
    for (int t = 0; t < M; t++) roff[t + 1] += roff[t];
    adjv = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    radjv = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    int *fo = malloc(sizeof(int) * (size_t)(N + 1));
    int *fr = malloc(sizeof(int) * (size_t)(M + 1));
    memcpy(fo, off, sizeof(int) * (size_t)(N + 1));
    memcpy(fr, roff, sizeof(int) * (size_t)(M + 1));
    for (int i = 0; i < m; i++) {
        adjv[fo[eu[i]]++] = ev[i] - N;
        radjv[fr[ev[i] - N]++] = eu[i];
    }

    inS = calloc(N, sizeof(int));
    load = calloc(M, sizeof(int));
    cur = malloc(sizeof(int) * (size_t)N);
    best = malloc(sizeof(int) * (size_t)N);
    pos = malloc(sizeof(int) * (size_t)N);
    int *cand = malloc(sizeof(int) * (size_t)N);
    int *perm = malloc(sizeof(int) * (size_t)N);
    for (int x = 0; x < N; x++) pos[x] = -1;
    curk = 0; bestk = 0;

    for (int i = 0; i < N; i++) perm[i] = i;
    for (int i = N - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
    }
    for (int i = 0; i < N; i++) if (can_add(perm[i])) add_el(perm[i]);
    save_best();

    double t0 = now();
    long long it = 0, since = 0;
    const long long STALL = 60000;
    while (1) {
        if ((it & 1023) == 0 && now() - t0 > tl) break;
        it++; since++;
        if (since > STALL) {
            load_best();
            for (int r = 0; r < 2 && curk > 0; r++) rem_el(cur[rndint(curk)]);
            since = 0;
        }
        int x = rndint(N);
        if (inS[x]) continue;
        if (can_add(x)) {
            add_el(x);
            if (curk > bestk) { save_best(); since = 0; }
            continue;
        }
        int deg = off[x + 1] - off[x];
        if (deg == 0) continue;
        int st = rndint(deg), t = -1;
        for (int j = 0; j < deg; j++) {
            int tt = adjv[off[x] + (st + j) % deg];
            if (load[tt] >= LIM) { t = tt; break; }
        }
        if (t < 0) continue;
        int nc = 0;
        for (int i = roff[t]; i < roff[t + 1]; i++)
            if (inS[radjv[i]]) cand[nc++] = radjv[i];
        if (nc == 0) continue;
        int y = cand[rndint(nc)];
        rem_el(y);
        if (can_add(x)) add_el(x);
        else if (rndint(40) != 0) add_el(y);
    }

    printf("%d\n", bestk);
    for (int i = 0; i < bestk; i++) printf("%d ", best[i]);
    printf("\n");
    return 0;
}
"""


def _pg_data(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _loads_ok(S, s, m, nbr):
    """True if every target t is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy fallback: choose elements so that every target is hit by <= s chosen elements."""
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


def _side_search(m, s, nbr, budget, seed):
    """Run the C plateau search on one side. Returns the chosen element list (may raise RuntimeError)."""
    edges = [(x, m + t) for x in range(m) for t in nbr[x]]
    out = lib.run_c(SIDE_C, [round(budget, 3), s, seed, m],
                    stdin_graph=(2 * m, edges), timeout=budget + 15)
    tok = out.split()
    k = int(tok[0])
    return [int(v) for v in tok[1:1 + k]]


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


def _arc_extensions(d, deadline, seed):
    """Return (n, edges) candidates over prime powers q with q + 1 <= d."""
    out = []
    qs = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        m = q * q + q + 1
        s = d - q - 1
        if s == 0:
            # Plain PG(2, q) incidence graph (e.g. the Heawood graph for d = 3).
            m_, edges, pl, lp = _pg_data(q)
            out.append(_arc_graph(m_, edges, pl, lp, [], []))
            continue
        qs.append((q, s, m, 2 * m + 2 * (s * m // (q + 1))))  # pot = optimistic order
    if not qs:
        return out

    # Spend time only on q whose optimistic order is near the best one.
    top = max(t[3] for t in qs)
    active = [t for t in qs if t[3] >= 0.8 * top]
    remaining = float(sum(t[3] for t in active))
    for q, s, _m, pot in sorted(active, key=lambda t: -t[3]):
        left = deadline - time.monotonic()
        if left <= 0.5:
            break
        budget = left * pot / remaining
        remaining -= pot
        if budget < 0.3:
            continue
        m, edges, pl, lp = _pg_data(q)
        try:
            SA = _side_search(m, s, pl, budget / 2, seed * 131 + q)
            SB = _side_search(m, s, lp, budget / 2, seed * 137 + q)
        except RuntimeError:
            rng = random.Random(seed * 131 + q)
            SA = _greedy_side(m, s, pl, rng, 40, deadline)
            SB = _greedy_side(m, s, lp, rng, 40, deadline)
        if not (_loads_ok(SA, s, m, pl) and _loads_ok(SB, s, m, lp)):
            continue
        out.append(_arc_graph(m, edges, pl, lp, SA, SB))
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
# Simulated annealing over bi-Cayley voltage lifts (unchanged from parent).
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
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
    deadline = start + 0.8 * time_limit
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

    # Arc-extended projective plane graphs, side sets found by the C engine.
    # Diameter 3, so valid for all D >= 3.
    if D >= 3:
        cands = _arc_extensions(d, deadline, seed)
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed group voltage lifts. Skipped for D = 3 with d >= 4, where the
    # arc search is the strong route and lifts are unlikely to beat it.
    if not (D == 3 and d >= 4):
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
