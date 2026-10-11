import functools
import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C search engine: simulated annealing over the voltages of a bi-Cayley lift
# over an ARBITRARY finite group. The group is passed as a full multiplication
# table (identity = element 0). Base graph: K vertices per side, DEG layers,
# each layer a permutation of 0..K-1, so every vertex has degree DEG.
# Dart e = l*K + i joins A_i to B_{dJ[e]} with voltage dS[e]:
#     A_{i,g} ~ B_{j, g*s}   for all g.
# Left multiplication is an automorphism, so BFS from the 2K representatives
# (A_i, e) and (B_j, e) decides the diameter exactly.
#
# Moves: change a voltage, or swap the targets of two darts in one layer.
# Cost = unreached (rep, vertex) pairs + duplicate penalty. Reheating from the
# best state inside the same run, with random kicks.
#
# Input (stdin, graph text format): header "G G*G", then G*G lines "idx val",
# meaning MT[idx] = val, where MT[x*G+y] = x*y.
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

static int DEG, DIAM, K, G, N, NE;
static int *MT;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx, *bestS, *bestJ, *p;
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
    if (argc < 6) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double slice = atof(argv[5]);

    int hn = 0, hm = 0;
    if (scanf("%d %d", &hn, &hm) != 2) { printf("0 0\n"); return 0; }
    G = hn;
    if (DEG < 1 || DIAM < 1 || K < 1 || G < 1 || hm != G * G) { printf("0 0\n"); return 0; }
    MT = malloc(sizeof(int) * (size_t)G * G);
    if (!MT) { printf("0 0\n"); return 0; }
    for (int i = 0; i < hm; i++) {
        int idx = 0, val = 0;
        if (scanf("%d %d", &idx, &val) != 2) { printf("0 0\n"); return 0; }
        if (idx < 0 || idx >= G * G || val < 0 || val >= G) { printf("0 0\n"); return 0; }
        MT[idx] = val;
    }
    for (int y = 0; y < G; y++) {
        if (MT[y] != y || MT[(size_t)y * G] != y) { printf("0 0\n"); return 0; }
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
    p = malloc(sizeof(int) * K);
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


MAXO = 800  # largest base group order used (keeps the stdin table moderate)
TABLE_CAP = 900


# ----------------------------------------------------------------------------
# Exact / safe constructions (carried over from the parent).
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
# Finite groups as multiplication tables (identity = index 0).
# Specs are hashable tuples:
#   ('semi', m, k2, r)  Z_m x|_r Z_k2 (r = 1 gives the direct product)
#   ('psl', p) / ('pgl', p)  projective special/general linear group over Z_p
#   ('agl', q)          affine group x -> ax + b over GF(q)
#   ('ut', q)           upper unitriangular 3x3 matrices over GF(q), order q^3
#   ('prod', spec, k)   direct product with cyclic group Z_k
# ----------------------------------------------------------------------------

def _order(spec):
    kind = spec[0]
    if kind == 'semi':
        return spec[1] * spec[2]
    if kind == 'psl':
        p = spec[1]
        return p * (p * p - 1) // 2
    if kind == 'pgl':
        p = spec[1]
        return p * (p * p - 1)
    if kind == 'agl':
        q = spec[1]
        return q * (q - 1)
    if kind == 'ut':
        return spec[1] ** 3
    if kind == 'prod':
        return _order(spec[1]) * spec[2]
    raise ValueError(kind)


def _semi_table(m, k2, r):
    n = m * k2
    x = np.arange(n, dtype=np.int64)
    A, B = x // k2, x % k2
    powers = np.array([pow(r, b, m) for b in range(k2)], dtype=np.int64)
    Ax, Bx = A[:, None], B[:, None]
    Ay, By = A[None, :], B[None, :]
    return ((Ax + powers[Bx] * Ay) % m) * k2 + (Bx + By) % k2


def _proj_table(p, square_only):
    """PGL(2,p) or PSL(2,p) (det a square) as normalized 2x2 matrices, identity first."""
    els = []
    seen = set()
    for v in itertools.product(range(p), repeat=4):
        a, b, c, d = v
        det = (a * d - b * c) % p
        if det == 0:
            continue
        if square_only and pow(det, (p - 1) // 2, p) != 1:
            continue
        first = next(x for x in v if x)
        inv = pow(first, p - 2, p)
        nv = tuple(x * inv % p for x in v)
        if nv not in seen:
            seen.add(nv)
            els.append(nv)
    els.remove((1, 0, 0, 1))
    els.insert(0, (1, 0, 0, 1))
    index = {e: i for i, e in enumerate(els)}
    n = len(els)
    tab = np.empty((n, n), dtype=np.int64)
    for i, (a, b, c, d) in enumerate(els):
        for j, (e, f, g, h) in enumerate(els):
            x = (a * e + b * g) % p
            y = (a * f + b * h) % p
            z = (c * e + d * g) % p
            w = (c * f + d * h) % p
            first = next(t for t in (x, y, z, w) if t)
            inv = pow(first, p - 2, p)
            tab[i, j] = index[(x * inv % p, y * inv % p, z * inv % p, w * inv % p)]
    return tab


def _agl_table(q):
    """Affine maps x -> a x + b over GF(q); (a,b)(c,d) = (ac, ad + b), identity (1,0) first."""
    F = lib.GF(q)
    els = [(1, 0)] + [(a, b) for a in range(1, q) for b in range(q) if (a, b) != (1, 0)]
    A = np.array([e[0] for e in els], dtype=np.int64)
    B = np.array([e[1] for e in els], dtype=np.int64)
    n = len(els)
    idx = np.full((q, q), -1, dtype=np.int64)
    idx[A, B] = np.arange(n)
    mul, add = F.mul_table, F.add_table
    pa = mul[A[:, None], A[None, :]]
    pb = add[mul[A[:, None], B[None, :]], B[:, None]]
    return idx[pa, pb]


def _ut_table(q):
    """Upper unitriangular matrices over GF(q): (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a b')."""
    F = lib.GF(q)
    n = q ** 3
    x = np.arange(n, dtype=np.int64)
    A = x // (q * q)
    B = (x // q) % q
    C = x % q
    mul, add = F.mul_table, F.add_table
    pa = add[A[:, None], A[None, :]]
    pb = add[B[:, None], B[None, :]]
    pc = add[add[C[:, None], C[None, :]], mul[A[:, None], B[None, :]]]
    return pa * (q * q) + pb * q + pc


@functools.lru_cache(maxsize=12)
def _table(spec):
    kind = spec[0]
    if kind == 'semi':
        return _semi_table(spec[1], spec[2], spec[3])
    if kind == 'psl':
        return _proj_table(spec[1], True)
    if kind == 'pgl':
        return _proj_table(spec[1], False)
    if kind == 'agl':
        return _agl_table(spec[1])
    if kind == 'ut':
        return _ut_table(spec[1])
    if kind == 'prod':
        T1 = _table(spec[1])
        T2 = _semi_table(spec[2], 1, 1)
        n1, n2 = T1.shape[0], T2.shape[0]
        return (T1[:, None, :, None] * n2 + T2[None, :, None, :]).reshape(n1 * n2, n1 * n2)
    raise ValueError(kind)


def _make_pool(maxo=MAXO):
    """Named nonabelian groups (and products with cyclic groups) with order <= maxo."""
    pool = []
    for p in (5, 7, 11):
        pool.append(('psl', p))
    for p in (5, 7):
        pool.append(('pgl', p))
    for q in range(3, 33):
        if lib.is_prime_power(q) and q * (q - 1) <= maxo:
            pool.append(('agl', q))
    for q in (2, 3, 4, 5, 7, 8, 9):
        if q ** 3 <= maxo:
            pool.append(('ut', q))
    base = [s for s in pool if _order(s) <= maxo // 2]
    for b in base:
        ob = _order(b)
        for k in range(2, maxo // ob + 1):
            pool.append(('prod', b, k))
    return pool


def _pick_spec(lo, hi, rng, pool):
    """Pick a group spec whose order lies in [lo, hi], or None."""
    if rng.random() < 0.5:
        cands = [s for s in pool if lo <= _order(s) <= hi]
        if cands:
            return rng.choice(cands)
    for _ in range(40):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        mlo = max(2, -(-lo // k2))
        mhi = hi // k2
        if mlo > mhi:
            continue
        m = rng.randint(mlo, mhi)
        if k2 == 1:
            return ('semi', m, 1, 1)
        units = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        return ('semi', m, k2, rng.choice(units))  # r = 1 is always in units
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
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
        try:
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

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

    # Search: anneal voltages of bi-Cayley lifts over a variety of groups,
    # including nonabelian ones (PSL/PGL, affine, unitriangular, products).
    pool = _make_pool()
    misses = 0
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            break
        K = rng.choice([1, 1, 2, 2, 3, 4])
        lo = best[0] // (2 * K) + 1           # group order giving N = 2*K*G > best
        hi = lo + max(3, lo // 12) + 6 * misses
        spec = _pick_spec(lo, hi, rng, pool)
        if spec is None or _order(spec) > TABLE_CAP:
            misses += 1
            continue
        misses = 0
        slice_s = min(remaining - 1.0, 10.0)
        try:
            tab = _table(spec)
            G = int(tab.shape[0])
            flat = tab.ravel().tolist()
            out = lib.run_c(
                C_SOURCE,
                [d, D, K, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                stdin_graph=(G, list(zip(range(G * G), flat))),
                timeout=slice_s + 20.0,
            )
        except RuntimeError:
            break
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
