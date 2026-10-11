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
# Input (stdin): the table as an "n m" graph text with n = |G| and m = |G|^2
# lines "idx value", where idx = x*|G| + y and value = x*y. Identity is 0.
#
# Base graph: K vertices per side, DEG layers, each layer a permutation of
# 0..K-1 (every vertex has degree DEG). Dart e = l*K + i joins A_i to
# B_{dJ[e]} with voltage dS[e]: A_{i,g} ~ B_{j, g*s} for all g.
# Left multiplication is an automorphism, so BFS from the 2K representatives
# decides the diameter exactly.
#
# Excess-distance cost: a vertex at distance t > DIAM costs (t - DIAM); a
# vertex not reached within LMAX levels costs (LMAX - DIAM + 2). The total is
# zero iff the lift has diameter <= DIAM. Duplicate darts are penalised.
#
# Usage: prog d D K seed slice_seconds      (table on stdin)
# Prints a graph ("n m" + edges) or "0 0".
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
#define RL 60000
#define GMAX 2000

static int DEG, DIAM, K, G, N, NE;
static int *MT;
static int *dI, *dJ, *dS, *bestS, *bestJ, *perm, *adj, *cnt, *fr, *nx, *pp;
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
        fprintf(stderr, "usage: prog d D K seed slice (table on stdin)\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double slice = atof(argv[5]);
    if (DEG < 1 || DIAM < 1 || K < 1) { printf("0 0\n"); return 0; }

    int gn, gm;
    if (scanf("%d %d", &gn, &gm) != 2) { printf("0 0\n"); return 0; }
    if (gn < 1 || gn > GMAX || (long long)gn * gn != (long long)gm) { printf("0 0\n"); return 0; }
    G = gn;
    MT = malloc(sizeof(int) * (size_t)G * G);
    if (!MT) { printf("0 0\n"); return 0; }
    for (int i = 0; i < gm; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || u >= gm || v < 0 || v >= G) { printf("0 0\n"); return 0; }
        MT[u] = v;
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
    pp = malloc(sizeof(int) * K);
    if (!dI || !dJ || !dS || !bestS || !bestJ || !perm || !adj || !cnt || !fr || !nx || !vis || !pp) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    int found = 0;
    int bestCost = BIGCOST;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestCost >= BIGCOST || rnd01() < 0.25) {
            for (int l = 0; l < DEG; l++) {
                for (int i = 0; i < K; i++) pp[i] = i;
                for (int i = K - 1; i > 0; i--) {
                    int j = rndint(i + 1);
                    int t = pp[i]; pp[i] = pp[j]; pp[j] = t;
                }
                for (int i = 0; i < K; i++) {
                    dI[l * K + i] = i;
                    dJ[l * K + i] = pp[i];
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
# Group tables (identity = element 0). Each returns (order, table) where
# table[x, y] is the index of x*y as a numpy int64 array.
# ----------------------------------------------------------------------------

GMAX_PY = 800      # keeps the stdin table (G*G pairs) a manageable size
K2_CHOICES = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21, 24,
              27, 28, 30, 36, 40, 42, 49, 54, 56, 63, 72, 81, 84, 96, 108, 121,
              128, 162, 243]
VEC_CHOICES = [(2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3),
               (3, 4), (3, 5), (5, 2), (5, 3), (7, 2), (11, 2), (13, 2)]


def _tab_abelian(ns):
    """Direct product of cyclic groups Z_n for n in ns (mixed-radix coding)."""
    G = 1
    weights = []
    for n in ns:
        weights.append(G)
        G *= n
    idx = np.arange(G, dtype=np.int64)
    digs = [(idx // w) % n for w, n in zip(weights, ns)]
    T = np.zeros((G, G), dtype=np.int64)
    for w, n, dg in zip(weights, ns, digs):
        T += ((dg[:, None] + dg[None, :]) % n) * w
    return G, T


def _tab_semi_cyclic(m, k, r):
    """Z_m x|_r Z_k with (a,b)(c,d) = (a + r^b c, b + d); element a*k + b."""
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    G = m * k
    X = np.arange(G, dtype=np.int64)
    A = X // k
    B = X % k
    Aa = (A[:, None] + pw[B][:, None] * A[None, :]) % m
    Bb = (B[:, None] + B[None, :]) % k
    return G, Aa * k + Bb


def _tab_vec_semi(p, n, M, k):
    """F_p^n x|_M Z_k with (v,b)(w,c) = (v + M^b w, b + c); needs M^k = I. Element v*k + b."""
    q = p ** n
    V = np.array([[(v // p ** j) % p for j in range(n)] for v in range(q)], dtype=np.int64)
    wts = np.array([p ** j for j in range(n)], dtype=np.int64)
    W = np.zeros((k, q), dtype=np.int64)
    P = np.eye(n, dtype=np.int64)
    for b in range(k):
        img = (V @ P.T) % p
        W[b] = img @ wts
        P = (P @ M) % p
    S = (V[:, None, :] + V[None, :, :]) % p
    add = S @ wts
    G = q * k
    X = np.arange(G, dtype=np.int64)
    A = X // k
    B = X % k
    Vres = add[A[:, None], W[B[:, None], A[None, :]]]
    Bres = (B[:, None] + B[None, :]) % k
    return G, Vres * k + Bres


def _mat_order(M, p, cap):
    """Order of invertible matrix M over F_p if it is <= cap, else None."""
    n = M.shape[0]
    I = np.eye(n, dtype=np.int64)
    P = M % p
    for k in range(1, cap + 1):
        if np.array_equal(P, I):
            return k
        P = (P @ M) % p
    return None


def _prime_powers(N):
    out = []
    x = N
    f = 2
    while f * f <= x:
        if x % f == 0:
            pe = 1
            while x % f == 0:
                x //= f
                pe *= f
            out.append(pe)
        f += 1
    if x > 1:
        out.append(x)
    return out


def _random_split(N, rng):
    """Random abelian invariant split of N: distribute prime powers into 1..4 cyclic factors."""
    pp = _prime_powers(N)
    nb = rng.choice([1, 2, 2, 3, 3, 4])
    bins = [1] * nb
    for x in pp:
        bins[rng.randrange(nb)] *= x
    ns = [b for b in bins if b > 1]
    return ns or [1]


def _sample_group(T, rng):
    """Return (order, table) for a group of order in [T, ~1.12T] from a random family."""
    hi = int(T * 1.12) + 2
    roll = rng.random()
    if roll < 0.4:
        N = rng.randint(T, hi)
        return _tab_abelian(_random_split(N, rng))
    if roll < 0.75:
        for _ in range(60):
            p, n = rng.choice(VEC_CHOICES)
            q = p ** n
            if 2 * q > hi:
                continue
            cap = hi // q
            M = np.array([[rng.randrange(p) for _ in range(n)] for _ in range(n)], dtype=np.int64)
            k = _mat_order(M, p, cap)
            if k is None or k < 2 or q * k < T:
                continue
            return _tab_vec_semi(p, n, M, k)
    for _ in range(40):
        k2 = rng.choice(K2_CHOICES)
        m = max(2, -(-T // k2))
        cands = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        r = rng.choice(cands) if cands else 1
        return _tab_semi_cyclic(m, k2, r)
    return _tab_abelian([rng.randint(T, hi)])


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

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    step = 0.08
    while True:
        remaining = search_deadline - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(remaining, 10.0)
        Kc = rng.choice([1, 1, 2, 2, 3])
        want = best[0] * (1.0 + step)
        T = max(2, math.ceil(want / (2 * Kc)))
        while T > GMAX_PY and Kc < 60:
            Kc += 1
            T = max(2, math.ceil(want / (2 * Kc)))
        grp = _sample_group(T, rng)
        G, tab = grp
        if G > GMAX_PY:
            step = max(0.005, step * 0.7)
            continue
        table_edges = list(zip(range(G * G), tab.ravel().tolist()))
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, Kc, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                stdin_graph=(G, table_edges),
                timeout=slice_s + 10.0,
            )
        except RuntimeError:
            break
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

    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, deadline)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
