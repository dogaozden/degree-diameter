import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing for a difference cover in a finite group G
# (cyclic Z_M when K = 1, otherwise the semidirect product Z_M x|_R Z_K, element
# (a, b) coded as a*K + b). We look for S of size D with S * S^{-1} = G, which
# makes the Haar-type bipartite graph A_x ~ B_{x s} (s in S) of diameter 3.
# Cost = number of group elements not of the form s t^{-1}. Output "OK s_0 ..."
# or "FAIL". The identity is fixed as S[0] (right translation keeps S S^{-1}).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 512
#define MAXD 64

static int G, K, M, R, D;
static int mulT[MAXG][MAXG];
static int invT[MAXG];
static int pw[MAXG];
static int S[MAXD];
static int cnt[MAXG], cntb[MAXG], ulist[MAXG];
static uint64_t rs = 1;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int in_prefix(int x, int upto) {
    for (int i = 0; i < upto; i++) if (S[i] == x) return 1;
    return 0;
}

static int cost_full(void) {
    memset(cnt, 0, sizeof(int) * (size_t)G);
    for (int i = 0; i < D; i++)
        for (int j = 0; j < D; j++)
            cnt[mulT[S[i]][invT[S[j]]]]++;
    int unc = 0;
    for (int g = 0; g < G; g++) if (cnt[g] == 0) unc++;
    return unc;
}

int main(int argc, char **argv) {
    if (argc < 7) return 1;
    M = atoi(argv[1]); K = atoi(argv[2]); R = atoi(argv[3]); D = atoi(argv[4]);
    uint64_t seed = (uint64_t)strtoull(argv[5], NULL, 10);
    double tl = atof(argv[6]);
    if (M < 1 || K < 1) { printf("FAIL\n"); return 0; }
    G = M * K;
    if (G > MAXG || D < 2 || D > MAXD || D > G) { printf("FAIL\n"); return 0; }

    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 991ULL);
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    pw[0] = 1 % M;
    for (int b = 1; b < K; b++) pw[b] = (int)(((long long)pw[b - 1] * R) % M);
    for (int x = 0; x < G; x++) {
        int a = x / K, b = x % K;
        for (int y = 0; y < G; y++) {
            int c = y / K, e = y % K;
            long long aa = ((long long)a + (long long)pw[b] * c) % M;
            mulT[x][y] = (int)(aa * K + (b + e) % K);
        }
    }
    for (int x = 0; x < G; x++) {
        invT[x] = -1;
        for (int y = 0; y < G; y++) if (mulT[x][y] == 0) { invT[x] = y; break; }
        if (invT[x] < 0) { printf("FAIL\n"); return 0; }
    }

    S[0] = 0;
    for (int i = 1; i < D; i++) {
        int x;
        do { x = rint_(G); } while (in_prefix(x, i));
        S[i] = x;
    }

    clock_t t0 = clock();
    int cur = cost_full();
    const long long EP = 300000;
    const double T0 = 1.2, T1 = 0.03;
    long long it = 0;
    while (cur > 0) {
        if ((it & 1023) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > tl) break;
        }
        it++;
        double T = T0 * pow(T1 / T0, (double)(it % EP) / (double)EP);

        int nu = 0;
        for (int g = 0; g < G; g++) if (cnt[g] == 0) ulist[nu++] = g;

        int i, x;
        if (nu > 0 && rdbl() < 0.5) {
            int g = ulist[rint_(nu)];
            int j = rint_(D);
            i = 1 + rint_(D - 1);
            x = mulT[g][S[j]];
        } else {
            i = 1 + rint_(D - 1);
            x = rint_(G);
        }
        if (in_prefix(x, D)) continue;

        int old = S[i];
        memcpy(cntb, cnt, sizeof(int) * (size_t)G);
        S[i] = x;
        int nc = cost_full();
        int delta = nc - cur;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            S[i] = old;
            memcpy(cnt, cntb, sizeof(int) * (size_t)G);
        }
    }

    if (cur == 0) {
        printf("OK");
        for (int i = 0; i < D; i++) printf(" %d", S[i]);
        printf("\n");
    } else {
        printf("FAIL\n");
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
# Difference-cover Haar graphs (diameter 3): the new main construction for D = 3.
# If S has size d and S S^{-1} = G, then A_x ~ B_{x s} gives a d-regular
# bipartite graph on 2|G| vertices with diameter 3, and |G| <= d^2 - d + 1.
# ----------------------------------------------------------------------------

def _try_cover(m, k, r, d, seed, budget):
    """Run the C difference-cover search; return the list of d group codes or None."""
    if budget < 0.3:
        return None
    try:
        out = lib.run_c(C_SOURCE, [m, k, r, d, seed, round(budget, 2)],
                        stdin_graph=None, timeout=budget + 15)
    except RuntimeError:
        return None
    tok = out.split()
    if len(tok) != d + 1 or tok[0] != "OK":
        return None
    try:
        return [int(x) for x in tok[1:]]
    except ValueError:
        return None


def _haar_from_cover(order, mul, S):
    """Bipartite graph on A = 0..order-1, B = order..2*order-1 with A_x ~ B_{mul(x, s)}."""
    edges = [(x, order + mul(x, s)) for x in range(order) for s in S]
    return 2 * order, edges


def _cover_search(d, seed, end, rng, consider, start_order):
    """Cyclic groups in ascending order, then random semidirect products above the best order."""
    hi = d * d - d + 1
    best_order = start_order
    m = max(d, start_order + 1, int(0.7 * hi))
    fails = 0
    while m <= hi and fails < 3:
        budget = min(6.0, end - time.monotonic())
        if budget < 0.3:
            return
        S = _try_cover(m, 1, 1, d, seed + 101 * m, budget)
        if S is None:
            fails += 1
        else:
            fails = 0
            _, mul, _ = lib.semidirect_group(m, 1, 1)
            consider(_haar_from_cover(m, mul, S))
            best_order = max(best_order, m)
        m += 1

    tries = 0
    while best_order < hi and tries < 200:
        budget = min(4.0, end - time.monotonic())
        if budget < 0.3:
            return
        tries += 1
        G = rng.randint(best_order + 1, hi)
        ks = [k for k in range(2, 9) if G % k == 0 and G // k >= 2]
        if not ks:
            continue
        K = rng.choice(ks)
        M = G // K
        rlist = [r for r in range(2, M) if math.gcd(r, M) == 1 and pow(r, K, M) == 1 % M]
        if not rlist:
            continue
        R = rng.choice(rlist)
        S = _try_cover(M, K, R, d, seed + 7 * tries + 13, budget)
        if S is None:
            continue
        try:
            _, mul, _ = lib.semidirect_group(M, K, R)
        except ValueError:
            continue
        consider(_haar_from_cover(G, mul, S))
        best_order = max(best_order, G)


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used for D >= 4.
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
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    end = t_start + 0.82 * time_limit - 2.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        try:
            if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
                best = (g[0], list(g[1]))
        except Exception:
            pass

    # Arc-extended projective plane graphs (valid for D >= 3).
    if D >= 3 and time.monotonic() < end:
        cands = _arc_extensions(d, end, random.Random(seed * 7919 + d))
        for g in sorted(cands, key=lambda t: -t[0]):
            consider(g)

    # New main construction for D = 3: difference-cover Haar graphs.
    # Only Haar graphs with order above the current best are searched.
    if D == 3 and d >= 2 and time.monotonic() < end:
        try:
            _cover_search(d, seed, end, rng, consider, best[0] // 2)
        except Exception:
            pass

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
