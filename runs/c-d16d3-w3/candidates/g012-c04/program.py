import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with degree bound d each old vertex has spare s = d - q - 1.
#
# A-side: a set SA of points, each giving a new vertex joined to its q+1 lines.
#         Feasible iff every line holds <= s points of SA.
# B-side: a set SB of lines, each giving a new vertex joined to its q+1 points.
#         Feasible iff every point lies on <= s lines of SB.
# The sides are independent, and diameter 3 holds for any feasible SA, SB.
#
# New in this version: the side sets are chosen by a C engine
# (capacitated set packing by simulated annealing with ejection chains).
# A move forces an outside element x in and ejects, for each over-full target
# of x, one random current owner of that target. The move is accepted by a
# Metropolis rule on the size change, with a reheating temperature schedule.
# The output is checked in Python and then by lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 1;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int h, nt, cap, nS;
static int *adjStart, *adj, *load, *owners, *inS;

static void add_el(int x) {
    inS[x] = 1;
    nS++;
    for (int k = adjStart[x]; k < adjStart[x + 1]; k++) {
        int t = adj[k];
        owners[(size_t)t * cap + load[t]] = x;
        load[t]++;
    }
}

static void rem_el(int y) {
    inS[y] = 0;
    nS--;
    for (int k = adjStart[y]; k < adjStart[y + 1]; k++) {
        int t = adj[k];
        int *o = owners + (size_t)t * cap;
        for (int j = 0; j < load[t]; j++) {
            if (o[j] == y) {
                o[j] = o[load[t] - 1];
                break;
            }
        }
        load[t]--;
    }
}

int main(int argc, char **argv) {
    if (argc < 4) {
        fprintf(stderr, "usage: prog cap seed seconds\n");
        return 1;
    }
    cap = atoi(argv[1]);
    unsigned long long seed = strtoull(argv[2], NULL, 10);
    double secs = atof(argv[3]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 0) n = 0;
    h = n / 2;
    nt = n - h;
    if (cap < 1 || h < 1) {
        printf("0\n\n");
        return 0;
    }

    int *eu = malloc(sizeof(int) * (size_t)(m + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m + 1));
    int cnt = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        int a = u < v ? u : v;
        int b = u < v ? v : u;
        if (a < 0 || a >= h || b < h || b >= n) continue;
        eu[cnt] = a;
        ev[cnt] = b - h;
        cnt++;
    }

    int *deg = calloc((size_t)h + 1, sizeof(int));
    for (int e = 0; e < cnt; e++) deg[eu[e]]++;
    adjStart = malloc(sizeof(int) * ((size_t)h + 2));
    adjStart[0] = 0;
    for (int x = 0; x < h; x++) adjStart[x + 1] = adjStart[x] + deg[x];
    adj = malloc(sizeof(int) * ((size_t)cnt + 1));
    int *fillp = malloc(sizeof(int) * ((size_t)h + 1));
    for (int x = 0; x < h; x++) fillp[x] = adjStart[x];
    for (int e = 0; e < cnt; e++) adj[fillp[eu[e]]++] = ev[e];

    load = calloc((size_t)nt + 1, sizeof(int));
    owners = calloc((size_t)nt * (size_t)cap + 1, sizeof(int));
    inS = calloc((size_t)h + 1, sizeof(int));
    nS = 0;

    int *removed = malloc(sizeof(int) * ((size_t)h + 1));
    int *best = calloc((size_t)h + 1, sizeof(int));
    int bestn = 0;

    clock_t c0 = clock();
    long long it = 0;
    const long long CYC = 200000;
    while (1) {
        if ((it & 1023) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= secs) break;
        }
        it++;
        int x = rndint(h);
        if (inS[x]) continue;

        double ph = (double)(it % CYC) / (double)CYC;
        double T = 0.5 * pow(0.1, ph);

        int nrem = 0;
        for (int k = adjStart[x]; k < adjStart[x + 1]; k++) {
            int t = adj[k];
            while (load[t] >= cap) {
                int y = owners[(size_t)t * cap + rndint(load[t])];
                rem_el(y);
                removed[nrem++] = y;
            }
        }
        add_el(x);
        int delta = 1 - nrem;
        if (delta >= 0 || rnd01() < exp((double)delta / T)) {
            if (nS > bestn) {
                bestn = nS;
                memcpy(best, inS, sizeof(int) * (size_t)h);
            }
        } else {
            rem_el(x);
            for (int i = 0; i < nrem; i++) add_el(removed[i]);
        }
    }

    printf("%d\n", bestn);
    int first = 1;
    for (int x = 0; x < h; x++) {
        if (best[x]) {
            printf(first ? "%d" : " %d", x);
            first = 0;
        }
    }
    printf("\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Projective-plane helpers.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q); points 0..m-1, lines m..2m-1 in edges."""
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


def _valid_set(S, m, s, nbr):
    """True if S has distinct in-range elements and respects the load bound s."""
    return (len(set(S)) == len(S) and all(0 <= x < m for x in S)
            and _loads_ok(S, s, m, nbr))


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


def _c_select(h, pairs, cap, seed, secs):
    """Run the C engine on the element/target incidence `pairs` (element in 0..h-1, target in 0..h-1).

    Returns the list of chosen element indices."""
    edges = [(e, h + t) for e, t in pairs]
    out = lib.run_c(C_SOURCE, [cap, seed, f"{secs:.3f}"],
                    stdin_graph=(2 * h, edges), timeout=secs + 30.0)
    tok = out.split()
    k = int(tok[0])
    return [int(x) for x in tok[1:1 + k]]


def _arc_candidates(d):
    """(bound, q) for prime powers q with q + 1 <= d, sorted by the order bound of the arc extension."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        m = q * q + q + 1
        s = d - q - 1
        bound = 2 * m + (2 * (m * s // (q + 1)) if s >= 1 else 0)
        out.append((bound, q))
    out.sort(reverse=True)
    return out


def _arc_phase(d, budget, seed, consider):
    """Build arc-extended PG graphs for the top candidates, with C-selected A and B sets."""
    cands = _arc_candidates(d)[:2]
    work = [q for _, q in cands if d - q - 1 >= 1]
    if len(work) == 2:
        weight = {work[0]: 0.7, work[1]: 0.3}
    else:
        weight = {q: 1.0 for q in work}

    for _, q in cands:
        s = d - q - 1
        m, edges, point_lines, line_points = _pg_data(q)
        SA, SB = [], []
        if q in weight:
            per = budget * weight[q] / 2.0
            if per >= 0.2:
                pa = [(u, v - m) for u, v in edges]
                pb = [(v - m, u) for u, v in edges]
                try:
                    SA = _c_select(m, pa, s, seed * 131 + q, per)
                except Exception:
                    SA = []
                try:
                    SB = _c_select(m, pb, s, seed * 151 + q + 1, per)
                except Exception:
                    SB = []
                if not _valid_set(SA, m, s, point_lines):
                    SA = []
                if not _valid_set(SB, m, s, line_points):
                    SB = []
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        consider(n_c, e_c)


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
    deadline = start + 0.7 * time_limit

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

    # Arc-extended projective plane graphs, diameter 3, so valid for all D >= 3.
    if D >= 3:
        if D == 3:
            arc_budget = 0.7 * time_limit - 2.0
        else:
            arc_budget = 0.3 * time_limit - 1.0
        if arc_budget > 0.5:
            try:
                _arc_phase(d, arc_budget, seed, consider)
            except Exception:
                pass

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed group voltage lifts for D >= 4.
    if D >= 4:
        rng = random.Random(seed * 7919 + d)
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
