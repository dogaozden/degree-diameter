import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: maximum-cardinality multiset packing with capacity CAP per target.
#
# Input (graph text on stdin): n m, then m edges "u v". Vertices 0..E-1 are
# elements (may be chosen with repeats), vertices E..n-1 are targets. Element x
# consumes one unit of capacity at each target it touches. Argv: E CAP seed
# budget_seconds. Output: K, then K lines "x c" (element x chosen c times).
# Local search: greedy insert, swap-in with a blocking element, and iterated
# local search that restarts from the best state after long stagnation.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static int NE, NT, CAP;
static int *eoff, *eadj, *toff, *tadj, *cnt, *load, *bestcnt;
static int total = 0;

static int fits(int x) {
    for (int k = eoff[x]; k < eoff[x + 1]; k++)
        if (load[eadj[k]] >= CAP) return 0;
    return 1;
}
static void addu(int x) {
    cnt[x]++;
    total++;
    for (int k = eoff[x]; k < eoff[x + 1]; k++) load[eadj[k]]++;
}
static void remu(int x) {
    cnt[x]--;
    total--;
    for (int k = eoff[x]; k < eoff[x + 1]; k++) load[eadj[k]]--;
}
static void setstate(const int *c) {
    memset(load, 0, sizeof(int) * (size_t)NT);
    total = 0;
    for (int x = 0; x < NE; x++) {
        cnt[x] = c[x];
        total += c[x];
        for (int k = eoff[x]; k < eoff[x + 1]; k++) load[eadj[k]] += c[x];
    }
}
static void greedy_fill(int *ord) {
    for (int i = 0; i < NE; i++) ord[i] = i;
    for (int i = NE - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = ord[i]; ord[i] = ord[j]; ord[j] = t;
    }
    for (int i = 0; i < NE; i++) {
        int x = ord[i];
        if (eoff[x + 1] == eoff[x]) continue;
        while (fits(x)) addu(x);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    NE = atoi(argv[1]);
    CAP = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;

    int n = 0, mm = 0;
    if (scanf("%d %d", &n, &mm) != 2) return 1;
    NT = n - NE;
    if (NE <= 0 || NT <= 0 || CAP <= 0) { printf("0\n"); return 0; }

    int *eu = malloc(sizeof(int) * (size_t)(mm + 1));
    int *ev = malloc(sizeof(int) * (size_t)(mm + 1));
    eoff = calloc((size_t)NE + 1, sizeof(int));
    int kept = 0;
    for (int i = 0; i < mm; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 1;
        if (u > v) { int tmp = u; u = v; v = tmp; }
        if (u < NE && v >= NE && v - NE < NT) {
            eu[kept] = u;
            ev[kept] = v - NE;
            kept++;
            eoff[u + 1]++;
        }
    }
    for (int x = 0; x < NE; x++) eoff[x + 1] += eoff[x];
    eadj = malloc(sizeof(int) * (size_t)(kept + 1));
    int *fp = malloc(sizeof(int) * (size_t)(NE + 1));
    memcpy(fp, eoff, sizeof(int) * (size_t)(NE + 1));
    for (int i = 0; i < kept; i++) eadj[fp[eu[i]]++] = ev[i];

    toff = calloc((size_t)NT + 1, sizeof(int));
    for (int k = 0; k < kept; k++) toff[eadj[k] + 1]++;
    for (int t = 0; t < NT; t++) toff[t + 1] += toff[t];
    tadj = malloc(sizeof(int) * (size_t)(kept + 1));
    int *fq = malloc(sizeof(int) * (size_t)(NT + 1));
    memcpy(fq, toff, sizeof(int) * (size_t)(NT + 1));
    for (int x = 0; x < NE; x++)
        for (int k = eoff[x]; k < eoff[x + 1]; k++)
            tadj[fq[eadj[k]]++] = x;

    cnt = calloc((size_t)NE, sizeof(int));
    bestcnt = calloc((size_t)NE, sizeof(int));
    load = calloc((size_t)NT, sizeof(int));
    int *ord = malloc(sizeof(int) * (size_t)NE);

    greedy_fill(ord);
    int best_total = total;
    memcpy(bestcnt, cnt, sizeof(int) * (size_t)NE);

    clock_t c0 = clock();
    long long it = 0, stuck = 0;
    const long long STUCK = 300000;
    while (1) {
        if ((it & 4095) == 0 && (double)(clock() - c0) / CLOCKS_PER_SEC > budget) break;
        it++;
        int x = rndint(NE);
        int deg = eoff[x + 1] - eoff[x];
        if (deg == 0) continue;
        if (fits(x)) {
            addu(x);
        } else {
            int t = -1;
            int st = rndint(deg);
            for (int j = 0; j < deg; j++) {
                int tt = eadj[eoff[x] + (st + j) % deg];
                if (load[tt] >= CAP) { t = tt; break; }
            }
            if (t >= 0) {
                int tdeg = toff[t + 1] - toff[t];
                int y = -1;
                for (int tr = 0; tr < 8 && tdeg > 0; tr++) {
                    int c = tadj[toff[t] + rndint(tdeg)];
                    if (c != x && cnt[c] > 0) { y = c; break; }
                }
                if (y >= 0) {
                    remu(y);
                    if (fits(x)) addu(x);
                    else addu(y);
                }
            }
        }
        if (total > best_total) {
            best_total = total;
            memcpy(bestcnt, cnt, sizeof(int) * (size_t)NE);
            stuck = 0;
        } else {
            stuck++;
        }
        if (stuck > STUCK) {
            setstate(bestcnt);
            int drops = 1 + rndint(3);
            for (int r = 0; r < drops; r++) {
                for (int tr = 0; tr < 100000; tr++) {
                    int z = rndint(NE);
                    if (cnt[z] > 0) { remu(z); break; }
                }
            }
            greedy_fill(ord);
            stuck = 0;
        }
    }

    int K = 0;
    for (int x = 0; x < NE; x++) if (bestcnt[x] > 0) K++;
    printf("%d\n", K);
    for (int x = 0; x < NE; x++)
        if (bestcnt[x] > 0) printf("%d %d\n", x, bestcnt[x]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# A-side: a multiset SA of points (repeats allowed). Each entry gets a new
#         vertex joined to the q+1 lines through that point. Every line may
#         be hit by at most s entries.
# B-side: a multiset SB of lines, symmetric.
#
# Distances: A-vertices are pairwise at distance <= 2; an A-vertex reaches
# every old point within 2 and every old line within 3; an A-vertex and a
# B-vertex are joined by A_P - L - Q - B_j with Q = L cap j, so distance 3.
# Diameter stays 3 for any multisets, and bipartiteness holds by side.
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
    """True if every target is hit by <= s entries of S (repeats counted)."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


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


def _pack(nbr, m, s, seed, budget):
    """Run the C packing engine: choose a multiset of elements (rows of nbr) so each target
    (0..m-1) is hit at most s times. Returns the list of chosen element indices with repeats."""
    E = len(nbr)
    edges = [(x, E + t) for x, ts in enumerate(nbr) for t in ts]
    txt = lib.run_c(C_SOURCE, [E, s, seed, f"{budget:.2f}"],
                    stdin_graph=(E + m, edges), timeout=budget + 30.0)
    tok = txt.split()
    if not tok:
        return []
    K = int(tok[0])
    out = []
    for i in range(K):
        x, c = int(tok[1 + 2 * i]), int(tok[2 + 2 * i])
        out.extend([x] * c)
    return out


def _arc_best(d, deadline, seed):
    """Best arc-extended PG graph over the top prime powers q (with q+1 <= d)."""
    cands = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        m = q * q + q + 1
        s = d - q - 1
        ub = 2 * m + (2 * (s * m // (q + 1)) if s > 0 else 0)
        cands.append((ub, q, s))
    cands.sort(reverse=True)
    cands = cands[:2]
    if not cands:
        return None
    fr = [0.7, 0.3][:len(cands)]
    fr_sum = sum(fr)
    best = None
    for idx, (ub, q, s) in enumerate(cands):
        avail = deadline - time.monotonic()
        if avail <= 1.0:
            break
        share = avail * fr[idx] / fr_sum
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        SA, SB = [], []
        if s > 0:
            per = max(0.3, share / 2.0)
            SA = _pack(point_lines, m, s, seed * 131 + q, per)
            SB = _pack(line_points, m, s, seed * 151 + q + 7, per)
            if s >= 2:
                cs = _conic_set(q, index, lib.GF(q))
                if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                    SA = cs
                if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                    SB = cs
        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        if best is None or n_c > best[0]:
            best = (n_c, e_c)
    return best


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
    deadline = start + 0.75 * time_limit
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

    # Arc-extended PG graphs with multiset sides packed by the C engine (diameter 3).
    if D >= 3 and d >= 3:
        res = _arc_best(d, deadline, seed)
        if res is not None:
            consider(res[0], res[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search for D >= 4: annealed group voltage lifts.
    if D >= 4:
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
