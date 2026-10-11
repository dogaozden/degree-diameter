import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: penalised simulated annealing over integer multisets.
#
# Input (standard graph format from lib.run_c): n m, then m edges "u v".
# Items are vertices 0..ni-1; targets are vertices ni..n-1. Each item may be
# chosen with multiplicity 0..S. A target's load is the sum of multiplicities
# of its neighbouring items. Maximise the total multiplicity with every load <= S.
# Args: S seed time_limit_seconds ni.
# Output: total count, then the item indices (repeated by multiplicity).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs;
}
static double urand(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static int ni, nt, S;
static int *off, *adj, *x, *load, *bestx;
static int X, O;

static void inc_item(int i) {
    for (int k = off[i]; k < off[i + 1]; k++) {
        int t = adj[k];
        if (load[t] >= S) O++;
        load[t]++;
    }
    x[i]++;
    X++;
}

static void dec_item(int i) {
    for (int k = off[i]; k < off[i + 1]; k++) {
        int t = adj[k];
        load[t]--;
        if (load[t] >= S) O--;
    }
    x[i]--;
    X--;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    S = atoi(argv[1]);
    unsigned long long seed = strtoull(argv[2], NULL, 10);
    double tl = atof(argv[3]);
    ni = atoi(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (!rs) rs = 1;
    for (int w = 0; w < 10; w++) rnd();

    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 1;
    nt = n - ni;
    if (ni < 1 || nt < 1 || S < 1) {
        printf("0\n\n");
        return 0;
    }

    int *ea = malloc(sizeof(int) * (m + 1));
    int *eb = malloc(sizeof(int) * (m + 1));
    off = calloc(ni + 2, sizeof(int));
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 1;
        if (u > v) { int tmp = u; u = v; v = tmp; }
        if (u < 0 || u >= ni || v - ni < 0 || v - ni >= nt) return 1;
        ea[e] = u;
        eb[e] = v - ni;
        off[u + 1]++;
    }
    for (int i = 0; i < ni; i++) off[i + 1] += off[i];
    adj = malloc(sizeof(int) * (m + 1));
    int *pos = malloc(sizeof(int) * (ni + 1));
    for (int i = 0; i < ni; i++) pos[i] = off[i];
    for (int e = 0; e < m; e++) adj[pos[ea[e]]++] = eb[e];

    x = calloc(ni, sizeof(int));
    bestx = calloc(ni, sizeof(int));
    load = calloc(nt, sizeof(int));
    X = 0;
    O = 0;

    int bestX = 0;
    const double T0 = 1.0, T1 = 0.04;
    const long long CYC = 3000000LL;
    long long cyc = 0;
    long long it = 0;
    clock_t c0 = clock();

    while (1) {
        it++;
        if ((it & 1023) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= tl) break;
        }
        cyc++;
        if (cyc >= CYC) cyc = 0;
        double ph = (double)cyc / (double)CYC;
        double T = T0 * pow(T1 / T0, ph);

        int eold = O - X;
        int mv = 0, ai = -1, aj = -1;
        double r = urand();
        if (r < 0.45) {
            int i = (int)(rnd() % (unsigned long long)ni);
            if (x[i] < S) { inc_item(i); mv = 1; ai = i; }
        } else if (r < 0.55) {
            int i = (int)(rnd() % (unsigned long long)ni);
            if (x[i] > 0) { dec_item(i); mv = 2; ai = i; }
        } else {
            int i = (int)(rnd() % (unsigned long long)ni);
            int j = (int)(rnd() % (unsigned long long)ni);
            if (i != j && x[i] > 0 && x[j] < S) {
                dec_item(i);
                inc_item(j);
                mv = 3; ai = i; aj = j;
            }
        }
        if (!mv) continue;

        int de = (O - X) - eold;
        if (de <= 0 || urand() < exp(-(double)de / T)) {
            if (O == 0 && X > bestX) {
                bestX = X;
                memcpy(bestx, x, sizeof(int) * (size_t)ni);
            }
        } else {
            if (mv == 1) dec_item(ai);
            else if (mv == 2) inc_item(ai);
            else { inc_item(ai); dec_item(aj); }
        }
    }

    long long total = 0;
    for (int i = 0; i < ni; i++) total += bestx[i];
    printf("%lld\n", total);
    int first = 1;
    for (int i = 0; i < ni; i++) {
        for (int c = 0; c < bestx[i]; c++) {
            if (first) printf("%d", i);
            else printf(" %d", i);
            first = 0;
        }
    }
    printf("\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# A-side: a multiset SA of points (repeats allowed). Each entry P gets a new
#         vertex joined to all q+1 lines through P. Every line holds <= s entries.
# B-side: a multiset SB of lines. Each entry j gets a new vertex joined to all
#         q+1 points on j. Every point lies on <= s entries.
#
# Diameter stays 3 for any multisets SA, SB (see the derivation in the notes).
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
    """True if every target t is hit by <= s entries of S (repeats counted), where entry x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _c_multiset(nbr, nt, s, seed, budget):
    """Run the C annealer on the item->target incidence nbr (targets 0..nt-1). Returns item list."""
    ni = len(nbr)
    edges = [(i, ni + t) for i, lst in enumerate(nbr) for t in lst]
    out = lib.run_c(C_SOURCE, [s, seed, f"{budget:.3f}", ni],
                    stdin_graph=(ni + nt, edges), timeout=budget + 15.0)
    nums = out.split()
    k = int(nums[0])
    items = [int(v) for v in nums[1:1 + k]]
    if len(items) != k:
        raise ValueError("C multiset output truncated")
    return items


def _multi_side(m, s, nbr, rng, deadline):
    """Python fallback: iterated greedy over multisets with every target hit <= s times."""
    order = list(range(m))

    def fill(S, load):
        rng.shuffle(order)
        for x in order:
            nb = nbr[x]
            while all(load[t] < s for t in nb):
                S.append(x)
                for t in nb:
                    load[t] += 1
        return S

    cur = fill([], [0] * m)
    best = list(cur)
    while time.monotonic() < deadline:
        S = list(cur)
        load = [0] * m
        for x in S:
            for t in nbr[x]:
                load[t] += 1
        for _ in range(min(rng.randint(1, 3), len(S))):
            i = rng.randrange(len(S))
            x = S.pop(i)
            for t in nbr[x]:
                load[t] -= 1
        S = fill(S, load)
        if len(S) >= len(cur):
            cur = S
            if len(cur) > len(best):
                best = list(cur)
    return best


def _side(nbr, m, s, secs, rng, seed):
    """Best multiset for one side: C annealer first, Python greedy as fallback."""
    if secs < 0.2:
        return []
    try:
        S = _c_multiset(nbr, m, s, seed, secs * 0.85)
        if _loads_ok(S, s, m, nbr):
            return S
    except Exception:
        pass
    return _multi_side(m, s, nbr, rng, time.monotonic() + secs)


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA entry and one new B-vertex per SB entry."""
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
    """Return (n, edges) candidates from the best few prime powers q with q + 1 <= d."""
    out = []
    rng = random.Random(seed * 7919 + d)
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def est(q):
        m = q * q + q + 1
        s = d - q - 1
        return 2 * m + 2 * min(s * m // (q + 1), m)

    qs.sort(key=lambda q: -est(q))
    qs = qs[:3]
    weights = [2.0 if i == 0 else 1.0 for i in range(len(qs))]
    total_w = sum(weights) or 1.0
    total_t = max(0.0, deadline - time.monotonic())

    for idx, q in enumerate(qs):
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        SA, SB = [], []
        if s >= 1:
            secs = total_t * weights[idx] / total_w / 2.0
            SA = _side(point_lines, m, s, secs, rng, seed * 31 + q)
            SB = _side(line_points, m, s, secs, rng, seed * 37 + q + 1)
        F = lib.GF(q)
        cs = _conic_set(q, index, F)
        if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
            SA = cs
        if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
            SB = cs
        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
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
# Simulated annealing over bi-Cayley voltage lifts (from parent).
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
# Driver.
# ----------------------------------------------------------------------------

def _solve(d, D, seed, time_limit, start):
    """Build the best graph this program can find. May raise; build() guards it."""
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    deadline_all = start + 0.8 * time_limit

    # Diameter-3 family: the weight search gets most of the time for D = 3.
    if D >= 3:
        arc_frac = 0.72 if D == 3 else 0.4
        arc_deadline = start + arc_frac * time_limit
        cands = _arc_extensions(d, arc_deadline, seed)
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < deadline_all:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    rng = random.Random(seed)
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < deadline_all:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline_all, iters=400)
        if res is not None:
            consider(res[0], res[1])

    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if D == 1:
        fallback = (2, [(0, 1)]) if d >= 1 else (1, [])
    else:
        fallback = lib.haar_graph(max(d, 1), range(max(d, 1)))
    try:
        best = _solve(d, D, seed, time_limit, start)
    except Exception:
        best = None
    if best is None or not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
