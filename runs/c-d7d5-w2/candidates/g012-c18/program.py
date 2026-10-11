import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: simulated annealing over the voltages of a bi-Cayley lift
# over an arbitrary finite group given by its multiplication table.
#
# Input (stdin): the table is passed as a "graph" with n = G*G and m = G*G
# pairs (i, T[i]), where T[x*G+y] = x*y. Identity is not needed.
#
# Base graph: K vertices per side, DEG layers, each layer a permutation of
# 0..K-1. Dart e = l*K + i joins A_i to B_{dJ[e]} with voltage dS[e]:
# A_{i,x} ~ B_{j, x*s} for all x. Left multiplication is an automorphism, so
# BFS from the 2K representatives A_{i,0}, B_{j,0} decides the diameter exactly.
#
# Excess-distance cost: a vertex at distance t > DIAM costs (t - DIAM); a vertex
# not reached within LMAX levels costs (LMAX - DIAM + 2). Duplicate darts are
# penalised. Total zero iff the lift has diameter <= DIAM.
#
# Moves: change a voltage, or swap two targets within one layer.
#
# Usage: prog d D K seed slice_seconds
# Prints a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define BIGCOST (1 << 30)
#define STAG 8000

static int DEG, DIAM, K, G, N, NE;
static int *MT;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx;
static int *bestS, *bestJ;
static uint32_t *vis;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static void set_perm(int e) {
    int s = dS[e];
    int *pm = perm + (size_t)e * G;
    for (int g = 0; g < G; g++) pm[g] = MT[(size_t)g * G + s];
}

static int cost_fn(void) {
    int dup = 0;
    for (int e1 = 0; e1 < NE; e1++)
        for (int e2 = e1 + 1; e2 < NE; e2++)
            if (dI[e1] == dI[e2] && dJ[e1] == dJ[e2] && dS[e1] == dS[e2]) dup++;

    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < NE; e++) {
        int ba = dI[e] * G, bb = (K + dJ[e]) * G;
        const int *pm = perm + (size_t)e * G;
        for (int g = 0; g < G; g++) {
            int a = ba + g, b = bb + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }

    const int LMAX = DIAM + 3;
    const int UNREACH_W = LMAX - DIAM + 2;
    int total = 0;
    for (int ri = 0; ri < 2 * K; ri++) {
        int src = ri * G;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)N);
            stamp = 0;
        }
        stamp++;
        vis[src] = stamp;
        int *cur = fr, *nxt = nx;
        int fn = 1, reached = 1;
        cur[0] = src;
        for (int lv = 0; lv < LMAX && fn > 0; lv++) {
            int nn = 0;
            for (int q = 0; q < fn; q++) {
                int u = cur[q];
                const int *au = adj + (size_t)u * DEG;
                for (int t = 0; t < DEG; t++) {
                    int v = au[t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        nxt[nn++] = v;
                    }
                }
            }
            reached += nn;
            if (lv + 1 > DIAM) total += (lv + 1 - DIAM) * nn;
            int *tmp = cur; cur = nxt; nxt = tmp;
            fn = nn;
        }
        total += (N - reached) * UNREACH_W;
    }
    return total + PEN * dup;
}

static void save_best(void) {
    memcpy(bestS, dS, sizeof(int) * (size_t)NE);
    memcpy(bestJ, dJ, sizeof(int) * (size_t)NE);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D K seed slice\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double slice = atof(argv[5]);

    if (DEG < 1 || DIAM < 1 || K < 1) { printf("0 0\n"); return 0; }

    long long nn = 0, mm = 0;
    if (scanf("%lld %lld", &nn, &mm) != 2) { printf("0 0\n"); return 0; }
    long long gg = (long long)floor(sqrt((double)nn) + 0.5);
    if (gg < 1 || gg * gg != nn || mm != nn || gg > 2000) { printf("0 0\n"); return 0; }
    G = (int)gg;
    MT = malloc(sizeof(int) * (size_t)nn);
    if (!MT) { printf("0 0\n"); return 0; }
    for (long long i = 0; i < mm; i++) {
        long long u, v;
        if (scanf("%lld %lld", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || u >= nn || v < 0 || v >= gg) { printf("0 0\n"); return 0; }
        MT[u] = (int)v;
    }

    N = 2 * K * G;
    NE = DEG * K;

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    dI = malloc(sizeof(int) * NE);
    dJ = malloc(sizeof(int) * NE);
    dS = malloc(sizeof(int) * NE);
    bestS = malloc(sizeof(int) * NE);
    bestJ = malloc(sizeof(int) * NE);
    perm = malloc(sizeof(int) * (size_t)NE * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * N);
    fr = malloc(sizeof(int) * N);
    nx = malloc(sizeof(int) * N);
    vis = calloc(N, sizeof(uint32_t));
    int *p = malloc(sizeof(int) * K);
    if (!dI || !dJ || !dS || !bestS || !bestJ || !perm || !adj || !cnt || !fr || !nx || !vis || !p) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    int found = 0;
    int bestCost = BIGCOST;
    const int RL = 60000;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestCost >= BIGCOST || rnd01() < 0.25) {
            for (int l = 0; l < DEG; l++) {
                for (int i = 0; i < K; i++) p[i] = i;
                for (int i = K - 1; i > 0; i--) {
                    int j = rndint(i + 1);
                    int t = p[i]; p[i] = p[j]; p[j] = t;
                }
                for (int i = 0; i < K; i++) {
                    dI[l * K + i] = i;
                    dJ[l * K + i] = p[i];
                }
            }
            for (int e = 0; e < NE; e++) {
                dS[e] = rndint(G);
                set_perm(e);
            }
            T0 = 2.0;
        } else {
            memcpy(dJ, bestJ, sizeof(int) * (size_t)NE);
            memcpy(dS, bestS, sizeof(int) * (size_t)NE);
            int kick = NE / 8 + 1;
            for (int q = 0; q < kick; q++) dS[rndint(NE)] = rndint(G);
            for (int e = 0; e < NE; e++) set_perm(e);
            T0 = 0.8;
        }
        int cur = cost_fn();
        if (cur < bestCost) { bestCost = cur; save_best(); }
        if (cur == 0) { found = 1; break; }

        int runBest = cur;
        int since = 0;
        for (int it = 0; it < RL; it++) {
            if ((it & 255) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.05;
            if (K > 1 && rnd01() < 0.3) {
                int l = rndint(DEG);
                int i1 = rndint(K);
                int i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                int e1 = l * K + i1, e2 = l * K + i2;
                int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                }
            } else {
                int e = rndint(NE);
                int old = dS[e];
                int ns = rndint(G);
                if (ns == old) continue;
                dS[e] = ns;
                set_perm(e);
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    dS[e] = old;
                    set_perm(e);
                }
            }
            if (cur < bestCost) { bestCost = cur; save_best(); }
            if (cur < runBest) { runBest = cur; since = 0; }
            else if (++since > STAG) break;
            if (cur == 0) { found = 1; break; }
        }
    }

    if (found) {
        printf("%d %d\n", N, NE * G);
        for (int e = 0; e < NE; e++) {
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", dI[e] * G + g, (K + dJ[e]) * G + perm[(size_t)e * G + g]);
            }
        }
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Groups as multiplication tables: (order, flat table with T[x*n+y] = x*y).
# Families: metacyclic Z_m x|_r Z_k, symmetric and alternating groups,
# GL(2,q) and SL(2,q), Heisenberg groups, and direct products. Non-metacyclic
# groups are the main change from the earlier version.
# ----------------------------------------------------------------------------

def _from_mul(n, mulfn):
    return n, [mulfn(x, y) for x in range(n) for y in range(n)]


def _is_even_perm(p):
    inv = 0
    for i in range(len(p)):
        for j in range(i + 1, len(p)):
            if p[i] > p[j]:
                inv += 1
    return inv % 2 == 0


def _grp_perm(n, alt):
    elems = [p for p in itertools.permutations(range(n)) if not alt or _is_even_perm(p)]
    idx = {p: i for i, p in enumerate(elems)}
    m = len(elems)
    tab = []
    for x in elems:
        for y in elems:
            tab.append(idx[tuple(x[y[i]] for i in range(n))])
    return m, tab


def _grp_heis(p):
    def mul(x, y):
        a1, r1 = divmod(x, p * p)
        b1, c1 = divmod(r1, p)
        a2, r2 = divmod(y, p * p)
        b2, c2 = divmod(r2, p)
        return ((a1 + a2) % p) * p * p + ((b1 + b2) % p) * p + (c1 + c2 + a1 * b2) % p
    return _from_mul(p ** 3, mul)


def _grp_meta(m, k2, r):
    order, mul, _ = lib.semidirect_group(m, k2, r)
    return _from_mul(order, mul)


def _grp_matrix(q, special):
    F = lib.GF(q)
    mats = []
    for a, b, c, d in itertools.product(range(q), repeat=4):
        det = F.sub(F.mul(a, d), F.mul(b, c))
        if det != 0 and (not special or det == 1):
            mats.append((a, b, c, d))
    idx = {mt: i for i, mt in enumerate(mats)}

    def mm(x, y):
        a, b, c, d = x
        e, f, g, h = y
        return (F.add(F.mul(a, e), F.mul(b, g)), F.add(F.mul(a, f), F.mul(b, h)),
                F.add(F.mul(c, e), F.mul(d, g)), F.add(F.mul(c, f), F.mul(d, h)))

    n = len(mats)
    tab = [idx[mm(x, y)] for x in mats for y in mats]
    return n, tab


def _grp_prod(A, B):
    na, ta = A
    nb, tb = B
    n = na * nb
    tab = [0] * (n * n)
    for x in range(n):
        a1, b1 = divmod(x, nb)
        for y in range(n):
            a2, b2 = divmod(y, nb)
            tab[x * n + y] = ta[a1 * na + a2] * nb + tb[b1 * nb + b2]
    return n, tab


_GROUP_CACHE = {}


def _spec_order(s):
    t = s[0]
    if t == 'meta':
        return s[1] * s[2]
    if t == 'sym':
        return math.factorial(s[1])
    if t == 'alt':
        return math.factorial(s[1]) // 2
    if t == 'gl2':
        q = s[1]
        return (q * q - 1) * (q * q - q)
    if t == 'sl2':
        q = s[1]
        return q * (q * q - 1)
    if t == 'heis':
        return s[1] ** 3
    if t == 'prod':
        return _spec_order(s[1]) * _spec_order(s[2])
    raise ValueError(s)


def _make_group(spec):
    if spec in _GROUP_CACHE:
        return _GROUP_CACHE[spec]
    t = spec[0]
    if t == 'meta':
        g = _grp_meta(spec[1], spec[2], spec[3])
    elif t == 'sym':
        g = _grp_perm(spec[1], False)
    elif t == 'alt':
        g = _grp_perm(spec[1], True)
    elif t == 'gl2':
        g = _grp_matrix(spec[1], False)
    elif t == 'sl2':
        g = _grp_matrix(spec[1], True)
    elif t == 'heis':
        g = _grp_heis(spec[1])
    elif t == 'prod':
        g = _grp_prod(_make_group(spec[1]), _make_group(spec[2]))
    else:
        raise ValueError(spec)
    if len(_GROUP_CACHE) >= 6:
        _GROUP_CACHE.pop(next(iter(_GROUP_CACHE)))
    _GROUP_CACHE[spec] = g
    return g


K2_CHOICES = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21, 24,
              27, 28, 30, 36, 40, 42, 49, 54, 56, 63, 72, 81]

NONAB = [('sym', 3), ('sym', 4), ('alt', 4), ('sl2', 3), ('gl2', 3), ('heis', 3),
         ('meta', 7, 3, 2), ('meta', 9, 2, 8), ('sl2', 4), ('sym', 5), ('heis', 5),
         ('sl2', 5), ('sl2', 7)]


def _sample_spec(T, rng, cap):
    """Return a group spec with order >= T (and <= cap) and small overshoot, or None."""
    best, best_over = None, None
    for _ in range(80):
        if rng.random() < 0.4:
            k2 = rng.choice(K2_CHOICES)
            m = max(2, -(-T // k2))
            r = 1
            if k2 > 1 and m > 2:
                cands = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
                if cands:
                    r = rng.choice(cands)
            spec = ('meta', m, k2, r)
        else:
            c = rng.choice(NONAB)
            oc = _spec_order(c)
            m = -(-T // oc)
            spec = ('prod', c, ('meta', m, 1, 1)) if m > 1 else c
        o = _spec_order(spec)
        if o < T or o > cap:
            continue
        over = o - T
        if best is None or over < best_over:
            best, best_over = spec, over
        if over <= 0.08 * T + 2:
            break
    return best


# ----------------------------------------------------------------------------
# Exact / safe constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
# Greedy spare-degree extension (no-op for regular lifts).
# ----------------------------------------------------------------------------

def _two_colour(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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
                elif col[v] == col[u]:
                    return None
    return col


def _extend_spare(n, edges, d, D, deadline):
    """Greedily add fresh vertex pairs while the graph stays valid. Returns (n, edges)."""
    if d < 2:
        return n, edges
    col = _two_colour(n, edges)
    if col is None:
        return n, edges
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    edges = list(edges)
    while time.monotonic() < deadline:
        A_sp = [v for v in range(n) if col[v] == 0 and deg[v] < d]
        B_sp = [v for v in range(n) if col[v] == 1 and deg[v] < d]
        if not A_sp or not B_sp:
            break
        grown = False
        for k in range(d - 1, 0, -1):
            if k > len(A_sp) or k > len(B_sp):
                continue
            a, b = n, n + 1
            cand_new = [(a, b)] + [(a, x) for x in B_sp[:k]] + [(b, y) for y in A_sp[:k]]
            cand = edges + cand_new
            if lib.is_valid(n + 2, cand, d, D):
                edges = cand
                n += 2
                col += [0, 1]
                deg += [0, 0]
                deg[a] = k + 1
                deg[b] = k + 1
                for x in B_sp[:k]:
                    deg[x] += 1
                for y in A_sp[:k]:
                    deg[y] += 1
                grown = True
                break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = start + budget
    search_deadline = start + 0.92 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is larger and valid. Returns True when the best improved."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: lifts over general groups with adaptive target size.
    step = 0.08
    fails = 0
    while True:
        remaining = search_deadline - time.monotonic()
        if remaining < 1.0 or fails > 40:
            break
        slice_s = min(remaining, 10.0)
        K = rng.choice([1, 1, 2, 2, 3, 3, 4, 6])
        want = best[0] * (1.0 + step)
        T = max(2, math.ceil(want / (2 * K)))
        spec = _sample_spec(T, rng, cap=900)
        if spec is None:
            fails += 1
            step = max(0.005, step * 0.7)
            continue
        try:
            n_g, tab = _make_group(spec)
            out = lib.run_c(
                C_SOURCE,
                [d, D, K, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                stdin_graph=(n_g * n_g, [(i, t) for i, t in enumerate(tab)]),
                timeout=slice_s + 15.0,
            )
        except (RuntimeError, ValueError, MemoryError):
            fails += 1
            continue
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            step = max(0.005, step * 0.7)
            continue
        if consider(n, e):
            step = min(0.4, step * 1.25)
        else:
            step = max(0.005, step * 0.7)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Spare-degree extension with the remaining time.
    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, deadline)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
