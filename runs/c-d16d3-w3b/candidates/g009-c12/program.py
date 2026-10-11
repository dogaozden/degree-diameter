import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: covering search for bi-Cayley (Haar-type) graphs of diameter 3.
#
# Let G be a group of order N and S a k-subset of G (k = d). The Haar graph
# with left vertices x and right vertices y, and edges x -- x*s (s in S), is
# bipartite and k-regular. It has diameter <= 3 exactly when
#     S S^{-1} = G   and   S^{-1} S = G.
# The engine searches for such S by simulated annealing, where cost = number
# of uncovered group elements in the two difference sets. It tries groups
# Z_m x| Z_g (r^g = 1 mod m) with growing order N, and prints the largest
# order it covers. Output: "m g r k" then the k element codes of S
# (element (a,b) is coded a*g+b, multiplication as in lib.semidirect_group).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 400
#define MAXK 64

static int K;
static int gm, gg, gr, G;
static int pw[MAXG];
static int invT[MAXG];
static int TA[MAXG * MAXG];
static int TB[MAXG * MAXG];
static int c1[MAXG], c2[MAXG];
static int cost;
static int S[MAXK], inS[MAXG];
static int bestS[MAXK];
static int bestm = 0, bestg = 0, bestr = 0, bestK = 0;
static uint64_t rs = 1;
static clock_t T0;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - T0) / CLOCKS_PER_SEC; }

static long long modpow(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}
static int gcd_(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* semidirect product Z_m x| Z_g, element (a,b) coded a*g+b, (a,b)(c,e)=(a+r^b c, b+e) */
static int gmul(int x, int y) {
    int a = x / gg, b = x % gg, c = y / gg, dd = y % gg;
    int t = (int)(((long long)pw[b] * c + a) % gm);
    return t * gg + (b + dd) % gg;
}
static int ginv(int x) {
    int a = x / gg, b = x % gg;
    int nb = (gg - b) % gg;
    long long t = ((long long)pw[nb] * a) % gm;
    t = (gm - t) % gm;
    return (int)t * gg + nb;
}

static void set_group(int m, int g, int r) {
    gm = m; gg = g; gr = r; G = m * g;
    pw[0] = 1 % m;
    for (int b = 1; b < g; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    for (int x = 0; x < G; x++) invT[x] = ginv(x);
    for (int x = 0; x < G; x++) {
        for (int y = 0; y < G; y++) {
            TA[x * G + y] = gmul(x, invT[y]);   /* x * y^{-1} */
            TB[x * G + y] = gmul(invT[x], y);   /* x^{-1} * y */
        }
    }
}

static void choose_group(int Gord) {
    int divs[MAXG];
    int nd = 0;
    for (int g = 2; g <= Gord; g++) {
        if (Gord % g == 0 && Gord / g >= 2) divs[nd++] = g;
    }
    if (nd > 0 && rint_(100) < 60) {
        int g = divs[rint_(nd)];
        int m = Gord / g;
        for (int t = 0; t < 300; t++) {
            int r = 1 + rint_(m - 1);
            if (gcd_(r, m) != 1) continue;
            if (modpow(r, g, m) != (1 % m)) continue;
            set_group(m, g, r);
            return;
        }
    }
    set_group(Gord, 1, 1);
}

static void init_S(void) {
    for (int x = 0; x < G; x++) inS[x] = 0;
    for (int i = 0; i < K; i++) {
        int x;
        do { x = rint_(G); } while (inS[x]);
        S[i] = x;
        inS[x] = 1;
    }
}

static void full_init(void) {
    for (int x = 0; x < G; x++) { c1[x] = 0; c2[x] = 0; }
    for (int i = 0; i < K; i++) {
        for (int j = 0; j < K; j++) {
            c1[TA[S[i] * G + S[j]]]++;
            c2[TB[S[i] * G + S[j]]]++;
        }
    }
    cost = 0;
    for (int x = 0; x < G; x++) {
        if (!c1[x]) cost++;
        if (!c2[x]) cost++;
    }
}

static inline void dec1(int x) { if (--c1[x] == 0) cost++; }
static inline void inc1(int x) { if (c1[x]++ == 0) cost--; }
static inline void dec2(int x) { if (--c2[x] == 0) cost++; }
static inline void inc2(int x) { if (c2[x]++ == 0) cost--; }

/* Add (sg>0) or remove (sg<0) the ordered-pair contributions of element x at slot i. */
static void change(int i, int x, int sg) {
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        int y = S[j];
        int a1 = TA[x * G + y], a2 = TA[y * G + x];
        int b1 = TB[x * G + y], b2 = TB[y * G + x];
        if (sg < 0) {
            dec1(a1); dec1(a2); dec2(b1); dec2(b2);
        } else {
            inc1(a1); inc1(a2); inc2(b1); inc2(b2);
        }
    }
    int s0 = TA[x * G + x], t0 = TB[x * G + x];
    if (sg < 0) { dec1(s0); dec2(t0); }
    else { inc1(s0); inc2(t0); }
}

static int anneal(long long moves, double lim) {
    if (cost == 0) return 1;
    for (long long it = 0; it < moves; it++) {
        if ((it & 4095) == 0 && elapsed() > lim) return 0;
        double f = (double)it / (double)moves;
        double T = 0.9 * (1.0 - f) + 0.15;
        int i = rint_(K);
        int nv = rint_(G);
        if (inS[nv]) continue;
        int old = S[i];
        int c0 = cost;
        change(i, old, -1);
        change(i, nv, +1);
        S[i] = nv;
        int delta = cost - c0;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            inS[old] = 0;
            inS[nv] = 1;
            if (cost == 0) return 1;
        } else {
            change(i, nv, -1);
            change(i, old, +1);
            S[i] = old;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 777ULL);
    if (rs == 0) rs = 1;
    T0 = clock();

    if (D != 3 || d < 2 || d > MAXK) {
        printf("0 0 0 0\n");
        return 0;
    }
    K = d;
    int Gmax = d * d - d + 1;
    if (Gmax > MAXG - 1) Gmax = MAXG - 1;
    int Gl = d + 1;
    if (Gmax / 2 > Gl) Gl = Gmax / 2;

    int bestG = 0;
    for (int Gord = Gl; Gord <= Gmax; Gord++) {
        double el = elapsed();
        double rem = tl - el;
        if (rem < 0.3) break;
        double cap = 0.15 * rem;
        if (cap < 2.0) cap = 2.0;
        if (cap > rem) cap = rem;
        double lim = el + cap;
        int found = 0;
        while (!found && elapsed() < lim) {
            choose_group(Gord);
            init_S();
            full_init();
            found = anneal(800000LL, lim);
        }
        if (found) {
            bestG = Gord;
            bestm = gm; bestg = gg; bestr = gr; bestK = K;
            memcpy(bestS, S, sizeof(int) * (size_t)K);
        }
    }

    if (bestG == 0) {
        printf("0 0 0 0\n");
        return 0;
    }
    printf("%d %d %d %d\n", bestm, bestg, bestr, bestK);
    for (int i = 0; i < bestK; i++) printf("%d ", bestS[i]);
    printf("\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Group-covering Haar graphs (diameter 3, bipartite, k-regular with k = d).
# ----------------------------------------------------------------------------

def _group_haar(text, d, D):
    """Rebuild the Haar graph from the C output "m g r k" + S, or return None if invalid."""
    try:
        nums = [int(x) for x in text.split()]
        if len(nums) < 4:
            return None
        m, g, r, k = nums[:4]
        S = nums[4:4 + k]
        if k < 1 or len(S) != k or m < 1 or g < 1 or m * g < 2:
            return None
        order, mul, _ = lib.semidirect_group(m, g, r)
        edges = [(x, order + mul(x, s)) for x in range(order) for s in S]
        n = 2 * order
        if lib.is_valid(n, edges, d, D):
            return (n, edges)
    except Exception:
        return None
    return None


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


def _swap_improve(S, s, m, point_lines, line_points, rng, deadline, iters):
    """Local search that grows the arc set S by ejection moves; returns the best set seen."""
    cur = list(S)
    inS = set(cur)
    best = list(cur)
    pl_set = [set(point_lines[X]) for X in range(m)]
    lp_set = [set(line_points[X]) for X in range(m)]
    for _ in range(iters):
        if time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if P in inS:
            continue
        cl = [0] * m
        cp = [0] * m
        for X in cur:
            for L in point_lines[X]:
                cl[L] += 1
            for Q in line_points[X]:
                cp[Q] += 1
        Lset = set(point_lines[P])
        Qset = set(line_points[P])
        Lfull = {L for L in Lset if cl[L] >= s}
        Qfull = {Q for Q in Qset if cp[Q] >= s}
        block = [X for X in cur if (pl_set[X] & Lfull) or (lp_set[X] & Qfull)]
        if len(block) > 2:
            continue
        if not block and rng.random() > 0.5:
            continue
        bset = set(block)
        new = [X for X in cur if X not in bset] + [P]
        if not _loads_ok(new, s, m, point_lines, line_points):
            continue
        if len(new) >= len(cur) or rng.random() < 0.1:
            cur = new
            inS = set(cur)
            if len(cur) > len(best):
                best = list(cur)
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
    """Return (n, edges) candidates for each prime power q with q + 1 <= d, largest q first."""
    out = []
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]
    for q in sorted(qs, reverse=True):
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            g = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
            g = _swap_improve(g, s, m, point_lines, line_points, rng,
                              min(deadline, time.monotonic() + 2.0), iters=6000)
            cands.append(g)
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cs = _swap_improve(cs, s, m, point_lines, line_points, rng,
                                   min(deadline, time.monotonic() + 1.0), iters=3000)
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


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
    end = t_start + 0.8 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g is not None and g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = (g[0], list(g[1]))

    if D == 3:
        # Arc-extended projective plane graphs, with a short budget.
        if time.monotonic() < end:
            arc_deadline = min(end, t_start + 0.2 * time_limit)
            cands = _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d))
            for g in sorted(cands, key=lambda t: -t[0])[:2]:
                consider(g)

        # Main bold change: group-covering Haar graphs found by C annealing.
        cbudget = end - time.monotonic() - 1.5
        if cbudget > 3.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(cbudget, 2)],
                                stdin_graph=None, timeout=cbudget + 6)
                consider(_group_haar(out, d, D))
            except Exception:
                pass

    # Voltage-lift annealing for D >= 4.
    if D >= 4:
        if D >= 4 and time.monotonic() < end:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq)
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
