import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: packing search for arc-extended projective plane graphs.
#
# Input (stdin): the incidence graph of PG(2, q) as "n m" plus m edges, with
# points 0..M-1 and lines M..2M-1 (n = 2M). Argument: s (per-set capacity),
# seed, time in seconds.
#
# Choose S (a set of point indices) so that every constraint set holds at most
# s elements of S. The constraint sets are the points on each line and the
# lines through each point, both indexed by the element ids. Maximising |S|
# gives the number of added A/B vertex pairs. The engine runs an iterated local
# search: insert a random outside element, repair violated sets by removing
# random conflicting members, and accept with a Metropolis rule on the size
# change (cyclic temperature). It prints "k i1 ... ik".
# ----------------------------------------------------------------------------

C_ARC = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXE 1024
#define MAXSET 2048
#define MAXSZ 64
#define MAXMEM 128

static int ne, cap;
static int setsz[MAXSET];
static int setel[MAXSET][MAXSZ];
static int nmem[MAXE];
static int memb[MAXE][MAXMEM];
static int cnt[MAXSET];
static int inS[MAXE];
static int Sl[MAXE], Sp[MAXE], Ssz = 0;
static int bestS[MAXE], bestSz = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int ri(int k) { return (int)(rnd() % (uint64_t)k); }
static double rd(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static void addS(int y) {
    inS[y] = 1; Sp[y] = Ssz; Sl[Ssz++] = y;
    for (int t = 0; t < nmem[y]; t++) cnt[memb[y][t]]++;
}
static void remS(int y) {
    inS[y] = 0;
    int p = Sp[y];
    int last = Sl[--Ssz];
    Sl[p] = last; Sp[last] = p;
    for (int t = 0; t < nmem[y]; t++) cnt[memb[y][t]]--;
}
static int can_add(int y) {
    for (int t = 0; t < nmem[y]; t++) if (cnt[memb[y][t]] >= cap) return 0;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 4) { printf("0\n"); return 0; }
    cap = atoi(argv[1]);
    uint64_t seed = (uint64_t)strtoull(argv[2], NULL, 10);
    double tl = atof(argv[3]);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 977ULL);
    if (!rs) rs = 1;
    clock_t t0 = clock();

    int n = 0, me = 0;
    if (scanf("%d %d", &n, &me) != 2 || n < 2 || (n & 1) || n / 2 > MAXE || me < 0 || cap < 1) {
        printf("0\n"); return 0;
    }
    int m = n / 2;
    ne = m;
    int bad = 0;
    for (int j = 0; j < n; j++) setsz[j] = 0;
    for (int i = 0; i < me && !bad; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { bad = 1; break; }
        int p = u < v ? u : v, l = u < v ? v : u;
        if (p < 0 || l >= n || p >= m || l < m) { bad = 1; break; }
        int L = l - m;
        if (setsz[L] >= MAXSZ || setsz[m + p] >= MAXSZ) { bad = 1; break; }
        setel[L][setsz[L]++] = p;          /* set L: points on line L */
        setel[m + p][setsz[m + p]++] = L;  /* set m+p: lines through point p */
    }
    if (bad) { printf("0\n"); return 0; }

    for (int j = 0; j < n && !bad; j++)
        for (int t = 0; t < setsz[j]; t++) {
            int e = setel[j][t];
            if (nmem[e] >= MAXMEM) { bad = 1; break; }
            memb[e][nmem[e]++] = j;
        }
    if (bad) { printf("0\n"); return 0; }

    static int perm[MAXE];
    for (int i = 0; i < m; i++) perm[i] = i;
    for (int i = m - 1; i > 0; i--) {
        int j = ri(i + 1);
        int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
    }
    for (int i = 0; i < m; i++) {
        int y = perm[i];
        if (!inS[y] && can_add(y)) addS(y);
    }
    bestSz = Ssz;
    memcpy(bestS, Sl, sizeof(int) * (size_t)Ssz);

    static int logR[MAXE];
    long it = 0;
    for (;;) {
        if ((it & 255) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > tl) break;
        it++;
        if (Ssz >= ne) break;

        double phase = (double)(it % 300000) / 300000.0;
        double T = 0.04 + 0.5 * (1.0 - phase) * (1.0 - phase);

        int y;
        do { y = ri(ne); } while (inS[y]);
        addS(y);

        int nlog = 0, fail = 0;
        for (int t = 0; t < nmem[y] && !fail; t++) {
            int j = memb[y][t];
            while (cnt[j] > cap) {
                int L = setsz[j];
                int off = ri(L);
                int z = -1;
                for (int u = 0; u < L; u++) {
                    int e = setel[j][(off + u) % L];
                    if (inS[e] && e != y) { z = e; break; }
                }
                if (z < 0) { fail = 1; break; }
                remS(z);
                logR[nlog++] = z;
            }
        }

        int delta = 1 - nlog;
        int accept = !fail && (delta >= 0 || rd() < exp((double)delta / T));
        if (accept) {
            if (Ssz > bestSz) {
                bestSz = Ssz;
                memcpy(bestS, Sl, sizeof(int) * (size_t)Ssz);
            }
        } else {
            remS(y);
            for (int u = nlog - 1; u >= 0; u--) addS(logR[u]);
        }
    }

    printf("%d", bestSz);
    for (int i = 0; i < bestSz; i++) printf(" %d", bestS[i]);
    printf("\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3, valid for any S
# whose loads are <= s). Start from the incidence graph of PG(2, q). With
# d >= q+1 each vertex has spare capacity s = d - q - 1. Choose S such that
# every constraint set holds <= s points of S. Add an A-vertex joined to the
# q+1 lines through each P in S, and a B-vertex joined to the q+1 points on
# each line j in S. Every pair is then within distance 3 whatever S is.
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


def _arc_result(q, s, seconds, seed):
    """Run the packing search for PG(2, q) with capacity s; return (n, edges) or None."""
    m, edges, point_lines, line_points, _, _ = _pg_data(q)
    if s == 0:
        return _arc_graph(m, edges, point_lines, line_points, [])
    out = lib.run_c(C_ARC, [s, seed, round(seconds, 2)],
                    stdin_graph=(2 * m, edges), timeout=seconds + 20)
    toks = out.split()
    k = int(toks[0])
    S = sorted({int(x) for x in toks[1:1 + k]})
    if not _loads_ok(S, s, m, point_lines, line_points):
        return None
    return _arc_graph(m, edges, point_lines, line_points, S)


def _arc_search(d, seed, deadline, consider, current):
    """Try the most promising prime powers q (largest upper bound first) with the packing engine."""
    cands = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 0:
            continue
        m = q * q + q + 1
        # Each element lies in q+1 sets, and each set holds <= s, so |S|(q+1) <= s*m.
        ub = min(m, s * m // (q + 1))
        cands.append((2 * m + 2 * ub, q, s))
    cands.sort(reverse=True)
    for idx, (val, q, s) in enumerate(cands[:4]):
        if val <= current():
            break
        rem = deadline - time.monotonic()
        if rem < 1.0:
            break
        sec = max(0.5, 0.85 * rem - 0.5)
        try:
            g = _arc_result(q, s, sec, seed + 101 * idx)
        except Exception:
            g = None
        if g is not None:
            consider(g)


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used for D >= 4.
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
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    end = t_start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = (g[0], list(g[1]))

    # Packing search over arc-extended PG(2, q) graphs (valid for D >= 3).
    if D >= 3 and time.monotonic() < end:
        share = 1.0 if D == 3 else 0.4
        arc_deadline = time.monotonic() + share * (end - time.monotonic())
        _arc_search(d, seed, arc_deadline, consider, lambda: best[0])

    # Generalized quadrangle (valid for D >= 4).
    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # Voltage-lift annealing for D >= 4.
    if D >= 4:
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < end:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, end, iters=400)
            if res is not None:
                consider(res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
