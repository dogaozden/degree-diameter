import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C search engine: simulated annealing over the voltages of a bi-Cayley lift
# over an arbitrary finite group G given by its multiplication table.
#
# Base graph: K vertices per side, DEG layers, each layer a permutation of
# 0..K-1 (every vertex has degree DEG). Dart e = l*K + i joins A_i to B_{dJ[e]}
# with voltage dS[e]: A_{i,g} ~ B_{j,g*s} for all g in G.
# Left multiplication by x is an automorphism, so BFS from the 2K fibre
# representatives (vertex (u, 0)) decides the diameter exactly.
#
# Input (stdin): "n m" with n = m = |G|^2, then m pairs "u v" where
# u = x*|G| + y and v = x*y (multiplication table, row-major).
# Usage: prog DEG DIAM K seed slice_seconds
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

static int DEG, DIAM, K, G, N, NE;
static int *MUL;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx, *bestS, *bestJ;
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
    for (int g = 0; g < G; g++) pm[g] = MUL[(size_t)g * G + s];
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
        for (int lv = 0; lv < DIAM && fn > 0; lv++) {
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
            int *tmp = cur; cur = nxt; nxt = tmp;
            fn = nn;
        }
        total += N - reached;
    }
    return total + PEN * dup;
}

static void save_best(void) {
    memcpy(bestS, dS, sizeof(int) * (size_t)NE);
    memcpy(bestJ, dJ, sizeof(int) * (size_t)NE);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double slice = atof(argv[5]);

    int tn = 0, tm = 0;
    if (scanf("%d %d", &tn, &tm) != 2 || tn < 1 || tm != tn) {
        printf("0 0\n");
        return 0;
    }
    int gg = (int)(sqrt((double)tn) + 0.5);
    if (gg < 1 || gg * gg != tn) {
        printf("0 0\n");
        return 0;
    }
    G = gg;
    if (DEG < 1 || DIAM < 1 || K < 1) {
        printf("0 0\n");
        return 0;
    }
    MUL = malloc(sizeof(int) * (size_t)tn);
    if (!MUL) { printf("0 0\n"); return 0; }
    for (int i = 0; i < tm; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || u >= tn || v < 0 || v >= G) { printf("0 0\n"); return 0; }
        MUL[u] = v;
    }

    NE = DEG * K;
    N = 2 * K * G;
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
# Group families. A group descriptor is a tuple:
#   ('sd', m, k2, r)      Z_m x|_r Z_k2, element (a, b) coded as a*k2 + b
#   ('aff', q, h)         {x -> a x + b : a in H}, H the order-h subgroup of GF(q)*
#   ('prod', desc, j)     desc x Z_j
# Each group is turned into a multiplication table with numpy, vectorised.
# ----------------------------------------------------------------------------

_GF = {}
_AFF_QS = [q for q in range(3, 130) if lib.is_prime_power(q)]


def _gf(q):
    if q not in _GF:
        _GF[q] = lib.GF(q)
    return _GF[q]


def _sd_vec(m, k2, r):
    n = m * k2
    powers = np.array([pow(r, b, m) for b in range(k2)], dtype=np.int64)

    def mul(X, Y):
        a, b = X // k2, X % k2
        c, dd = Y // k2, Y % k2
        return ((a + powers[b] * c) % m) * k2 + (b + dd) % k2

    return n, mul


def _prod_vec(f1, f2):
    n1, m1 = f1
    n2, m2 = f2

    def mul(X, Y):
        a, b = X // n2, X % n2
        c, dd = Y // n2, Y % n2
        return m1(a, c) * n2 + m2(b, dd)

    return n1 * n2, mul


def _aff_vec(q, h):
    F = _gf(q)
    g = F.primitive_element()
    step = (q - 1) // h
    H = np.array([F.pow(g, step * i) for i in range(h)], dtype=np.int64)
    add_t = np.asarray(F.add_table, dtype=np.int64)
    mul_t = np.asarray(F.mul_table, dtype=np.int64)

    def mul(X, Y):
        i1, b1 = X // q, X % q
        i2, b2 = Y // q, Y % q
        ai = (i1 + i2) % h
        b = add_t[mul_t[H[i1], b2], b1]
        return ai * q + b

    return q * h, mul


def _vec(desc):
    if desc[0] == 'sd':
        return _sd_vec(desc[1], desc[2], desc[3])
    if desc[0] == 'aff':
        return _aff_vec(desc[1], desc[2])
    return _prod_vec(_vec(desc[1]), _sd_vec(desc[2], 1, 1))


def _group_edges(desc):
    """Return (|G|, pairs) encoding the multiplication table for the C engine."""
    n, mul = _vec(desc)
    X = np.arange(n, dtype=np.int64)[:, None]
    Y = np.arange(n, dtype=np.int64)[None, :]
    T = np.broadcast_to(np.asarray(mul(X, Y), dtype=np.int64), (n, n))
    flat = T.ravel().tolist()
    return n, list(zip(range(n * n), flat))


def _sd_list(lo, hi):
    out = []
    for k2 in range(1, 41):
        m_lo = max(2, -(-lo // k2))
        m_hi = hi // k2
        for m in range(m_lo, m_hi + 1):
            if k2 == 1:
                out.append(('sd', m, 1, 1))
                continue
            out.append(('sd', m, k2, 1))
            for r in range(2, m):
                if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                    out.append(('sd', m, k2, r))
    return out


def _aff_list(lo, hi):
    out = []
    for q in _AFF_QS:
        for h in range(1, q):
            if (q - 1) % h:
                continue
            if lo <= q * h <= hi:
                out.append(('aff', q, h))
    return out


def _catalog(lo, hi, rng):
    out = _sd_list(lo, hi) + _aff_list(lo, hi)
    for j in (2, 3, 4):
        sub = _sd_list(-(-lo // j), hi // j)
        if len(sub) > 60:
            sub = rng.sample(sub, 60)
        out += [('prod', s, j) for s in sub]
    return out


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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Greedy spare-degree extension (no-op for regular graphs).
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
            if time.monotonic() >= deadline:
                break
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
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

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

    # Main search: anneal voltages of bi-group lifts over a varied catalogue of
    # groups (metacyclic, affine over GF(q), and products with cyclic factors).
    # Each success is a strict improvement; targets are biased toward small
    # orders for reliability, with a ceiling near a fraction of the Moore bound.
    moore = lib.moore_bound(d, D)
    exc_count = 0
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 3.0 or exc_count >= 3:
            break
        slice_s = min(remaining - 1.5, 7.0 + 3.0 * rng.random())
        k = rng.choice([1, 1, 2, 2, 3, 4])
        base_lo = best[0] // (2 * k) + 1
        top = min(int(0.37 * moore / (2 * k)), 720)
        span = max(0, top - base_lo)
        lo = base_lo + int((rng.random() ** 2) * span)
        lo = min(lo, 800)
        if 2 * k * lo <= best[0]:
            continue
        hi = lo + max(4, lo // 12)
        cat = _catalog(lo, hi, rng)
        if not cat:
            continue
        desc = rng.choice(cat)
        try:
            n_g, edges = _group_edges(desc)
        except Exception:
            continue
        if 2 * k * n_g <= best[0]:
            continue
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, k, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                stdin_graph=(n_g * n_g, edges),
                timeout=slice_s + 20.0,
            )
        except RuntimeError:
            exc_count += 1
            continue
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Spare-degree extension with whatever time is left.
    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, deadline)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
