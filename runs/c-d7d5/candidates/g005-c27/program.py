import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C search engine: simulated annealing over voltages of a bi-Cayley lift over an
# arbitrary finite group given by its multiplication table.
#
# Base graph: K vertices per side, DEG layers, each layer a permutation of
# 0..K-1, so every vertex has degree DEG. Dart e = l*K + i joins A_i to B_{dJ[e]}
# with voltage dS[e]: A_{i,g} ~ B_{j, g*s} for all g. Left multiplication is an
# automorphism, so BFS from the 2K representatives (A_i, B_j at the identity)
# decides the diameter exactly.
#
# Group input (stdin): the table T[x*G+y] = x*y, identity 0, G*G entries.
# Moves: change a voltage, or swap two targets within one layer (keeps degrees).
# Cost = unreached (rep, vertex) pairs + duplicate-dart penalty.
#
# Usage: prog d D K G seed slice_seconds
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
static int *T;
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
    for (int g = 0; g < G; g++) pm[g] = T[g * G + s];
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
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    G = atoi(argv[4]);
    uint64_t seed = strtoull(argv[5], NULL, 10);
    double slice = atof(argv[6]);

    if (DEG < 1 || DIAM < 1 || K < 1 || G < 1 || G > 1100) {
        printf("0 0\n");
        return 0;
    }

    long long L = 0, M = 0;
    if (scanf("%lld %lld", &L, &M) != 2) { printf("0 0\n"); return 0; }
    if (L != (long long)G * G || M < 0 || 2 * M < L) { printf("0 0\n"); return 0; }
    int *raw = malloc(sizeof(int) * (size_t)(2 * M + 2));
    if (!raw) { printf("0 0\n"); return 0; }
    for (long long i = 0; i < 2 * M; i++) {
        int x;
        if (scanf("%d", &x) != 1) { printf("0 0\n"); return 0; }
        raw[i] = x;
    }
    for (long long i = 0; i < L; i++) {
        if (raw[i] < 0 || raw[i] >= G) { printf("0 0\n"); return 0; }
    }
    for (int y = 0; y < G; y++) {
        if (raw[y] != y || raw[(size_t)y * G] != y) { printf("0 0\n"); return 0; }
    }
    T = raw;

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
    const int RL = 30000;

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
            double Tt = T0 * (1.0 - (double)it / RL) + 0.05;
            if (K > 1 && rnd01() < 0.3) {
                int l = rndint(DEG);
                int i1 = rndint(K);
                int i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                int e1 = l * K + i1, e2 = l * K + i2;
                int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / Tt)) {
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
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / Tt)) {
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
# Group sources. Any finite group works: the C engine only needs a table.
# New families versus the parent: AGL(1,q), PGL(2,q), PSL(2,q) over GF(q) for
# prime powers q (non-metacyclic in general), plus metacyclic semidirect products.
# ----------------------------------------------------------------------------

MAX_TABLE = 1000  # largest group order handed to C (table has order^2 entries)


def _closure_table(gens, npts, cap):
    """Multiplication table (T[g, s] = index of g o s) of the permutation group generated by gens.

    Identity has index 0. Returns None if the group order reaches cap.
    """
    ident = tuple(range(npts))
    elems = [ident]
    seen = {ident: 0}
    i = 0
    while i < len(elems):
        g = elems[i]
        i += 1
        for s in gens:
            h = tuple(g[x] for x in s)  # (g o s)(x) = g(s(x))
            if h not in seen:
                if len(elems) >= cap:
                    return None
                seen[h] = len(elems)
                elems.append(h)
    P = np.array(elems, dtype=np.int64)
    G = len(elems)
    keys = {P[i].tobytes(): i for i in range(G)}
    T = np.empty((G, G), dtype=np.int64)
    for s in range(G):
        R = P[:, P[s]]  # R[g, x] = g[s[x]]
        T[:, s] = [keys[R[g].tobytes()] for g in range(G)]
    return T


def _field_table(kind, q):
    """Table of AGL(1,q), PGL(2,q) or PSL(2,q) (q odd) acting on the projective/affine line over GF(q)."""
    F = lib.GF(q)
    prim = F.primitive_element()
    if kind == "agl":
        npts = q
        gens = [tuple(F.add(x, b) for x in range(q)) for b in range(q)]
        gens.append(tuple(F.mul(prim, x) for x in range(q)))
    else:
        npts = q + 1
        inf = q
        gens = [tuple([F.add(x, b) for x in range(q)] + [inf]) for b in range(q)]
        a = prim if kind == "pgl" else F.mul(prim, prim)
        gens.append(tuple([F.mul(a, x) for x in range(q)] + [inf]))
        gens.append(tuple([inf] + [F.neg(F.inv(x)) for x in range(1, q)] + [0]))  # x -> -1/x
    return _closure_table(gens, npts, MAX_TABLE + 1)


def _field_specs():
    specs = []
    for q in range(5, 40):
        if not lib.is_prime_power(q):
            continue
        cands = [("agl", q * (q - 1)), ("pgl", q * (q * q - 1))]
        if q % 2:
            cands.append(("psl", q * (q * q - 1) // 2))
        for kind, order in cands:
            if order <= MAX_TABLE:
                specs.append((order, kind, q))
    return specs


_FIELD_SPECS = _field_specs()


def _semi_table(m, k, r):
    order, mul, _ = lib.semidirect_group(m, k, r)
    return np.array([[mul(x, y) for y in range(order)] for x in range(order)], dtype=np.int64)


def _semi_sample(lo, hi, rng):
    """Random metacyclic Z_m x|_r Z_k with lo <= m*k <= hi, as (order, table) or None."""
    for _ in range(300):
        k = rng.choice([2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24])
        m_lo = max(2, -(-lo // k))
        m_hi = hi // k
        if m_hi < m_lo:
            continue
        m = rng.randint(m_lo, m_hi)
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        r = rng.choice(rs) if (rs and rng.random() < 0.8) else 1
        order = m * k
        if not (lo <= order <= hi):
            continue
        return order, _semi_table(m, k, r)
    return None


def _pick_group(lo, hi, rng):
    """Return (order, table) for a group with lo <= order <= hi, or None."""
    field = [s for s in _FIELD_SPECS if lo <= s[0] <= hi]
    options = []
    if field:
        options.append("field")
    options.append("semi")
    for choice in rng.sample(options, len(options)):
        if choice == "field":
            order, kind, q = rng.choice(field)
            T = _field_table(kind, q)
            if T is not None:
                return order, T
        else:
            res = _semi_sample(lo, hi, rng)
            if res is not None:
                return res
    return None


def _table_graph(T):
    """Encode the table as the (n, edges) pair that lib.run_c writes to stdin.

    n is the number of table entries G*G; the C side reads the flat entries back.
    """
    flat = T.reshape(-1).tolist()
    if len(flat) % 2:
        flat.append(0)
    return (T.shape[0] ** 2, list(zip(flat[0::2], flat[1::2])))


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
# Greedy spare-degree extension for valid graphs that are not regular.
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
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    search_deadline = start + 0.9 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
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

    # Main search: anneal voltages of bi-Cayley lifts over a range of groups.
    # A lift with K base vertices per side over a group of order G has 2KG
    # vertices, so we only pick groups with 2KG > current best.
    failures = 0
    while failures < 6:
        remaining = search_deadline - time.monotonic()
        if remaining < 2.0:
            break
        slice_s = min(remaining, 10.0)
        k = rng.choice([1, 1, 2, 2, 3])
        lo = best[0] // (2 * k) + 1
        if lo > MAX_TABLE:
            failures += 1
            continue
        picked = (_pick_group(lo, min(MAX_TABLE, lo + max(60, lo // 3)), rng)
                  or _pick_group(lo, MAX_TABLE, rng))
        if picked is None:
            failures += 1
            continue
        order, T = picked
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, k, order, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                stdin_graph=_table_graph(T),
                timeout=slice_s + 20.0,
            )
        except RuntimeError:
            failures += 1
            continue
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Spare-degree extension on the best graph, with the remaining time.
    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, deadline)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
