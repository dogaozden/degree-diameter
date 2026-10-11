import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C search engine: simulated annealing over the voltages of a bi-regular lift
# of a base graph (K vertices per side, DEG layers of permutations) with voltage
# group G given by a multiplication table read from stdin.
#
# Stdin format (carried by lib.run_c as a graph with n = G and m = G*G edges):
#   "G G*G" then G*G lines "k T[k]", where k = x*G + y and T[k] = x*y.
#   Element 0 must be the identity.
#
# Dart e = l*K + i joins A_i to B_{dJ[e]} with voltage dS[e]: A_{i,g} ~ B_{j,g*s}.
# Left multiplication is an automorphism, so BFS from the 2K representatives
# decides the diameter exactly. Cost = unreached (rep, vertex) pairs + duplicate
# penalty. Moves: change a voltage, or swap two darts' targets within a layer.
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

static int DEG, DIAM, K, G, N, NE;
static int *mt;
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
    for (int g = 0; g < G; g++) pm[g] = mt[(size_t)g * G + s];
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
        fprintf(stderr, "usage: prog d D K seed slice\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double slice = atof(argv[5]);

    if (DEG < 1 || DIAM < 1 || K < 1) {
        printf("0 0\n");
        return 0;
    }

    int hg = 0, hm = 0;
    if (scanf("%d %d", &hg, &hm) != 2 || hg < 1 || hm != hg * hg) {
        printf("0 0\n");
        return 0;
    }
    G = hg;
    mt = malloc(sizeof(int) * (size_t)hm);
    if (!mt) { printf("0 0\n"); return 0; }
    for (int k = 0; k < hm; k++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || u >= hm || v < 0 || v >= G) {
            printf("0 0\n");
            return 0;
        }
        mt[u] = v;
    }
    for (int y = 0; y < G; y++) {
        if (mt[y] != y) { printf("0 0\n"); return 0; }
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
    const int RL = 40000;

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
            if ((it & 127) == 0 && elapsed(t0) >= slice) break;
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
# Groups given as multiplication tables (identity = element 0).
# ----------------------------------------------------------------------------

def _proj_group(p, kind):
    """Return (G, T) for PSL(2,p) ('psl') or PGL(2,p) ('pgl'); T[x, y] = index of x*y."""
    allm = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    a, b, c, d_ = allm[:, 0], allm[:, 1], allm[:, 2], allm[:, 3]
    det = (a * d_ - b * c) % p
    sel = allm[det == 1] if kind == "psl" else allm[det != 0]
    invt = np.zeros(p, dtype=np.int64)
    for x in range(1, p):
        invt[x] = pow(x, p - 2, p)

    def enc(X):
        return ((X[:, 0] * p + X[:, 1]) * p + X[:, 2]) * p + X[:, 3]

    def canon(X):
        if kind == "psl":
            return np.minimum(enc(X), enc((-X) % p))
        first = np.argmax(X != 0, axis=1)
        lead = X[np.arange(len(X)), first]
        return enc((X * invt[lead][:, None]) % p)

    def dec(k):
        x3 = k % p
        k = k // p
        x2 = k % p
        k = k // p
        x1 = k % p
        x0 = k // p
        return np.stack([x0, x1, x2, x3], axis=1)

    keys = np.unique(canon(sel))
    E = dec(keys)
    ident = canon(np.array([[1, 0, 0, 1]], dtype=np.int64))[0]
    pos = int(np.nonzero(keys == ident)[0][0])
    order = np.concatenate(([pos], np.delete(np.arange(len(keys)), pos)))
    keys = keys[order]
    E = E[order]
    G = len(keys)
    lookup = np.full(p ** 4, -1, dtype=np.int64)
    lookup[keys] = np.arange(G)
    T = np.zeros((G, G), dtype=np.int64)
    for g in range(G):
        a1, b1, c1, d1 = E[g]
        X = np.stack([
            (a1 * E[:, 0] + b1 * E[:, 2]) % p,
            (a1 * E[:, 1] + b1 * E[:, 3]) % p,
            (c1 * E[:, 0] + d1 * E[:, 2]) % p,
            (c1 * E[:, 1] + d1 * E[:, 3]) % p,
        ], axis=1)
        T[g] = lookup[canon(X)]
    return G, T


def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x|_r Z_k2 with order m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        r = 1  # r = 1 is the direct product, always valid
        if k2 > 1 and m > 2:
            cands = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if cands:
                r = rng.choice(cands)
        return m, k2, r
    return None


def _make_setup(rng, need):
    """Pick a group and base size K so that the lift has at least `need` vertices."""
    if rng.random() < 0.3:
        kind, q = rng.choice([("psl", 11), ("pgl", 7), ("psl", 7)])
        G, T = _proj_group(q, kind)
        K = max(1, -(-need // (2 * G)))
        if 2 * K * G > 2600:
            return None
        return G, K, T
    K = rng.choice([1, 1, 2, 2, 3])
    target = -(-need // (2 * K))
    grp = _sample_group(target + rng.randrange(0, max(2, target // 25 + 1)), rng)
    if grp is None:
        return None
    m, k2, r = grp
    G = m * k2
    if G > 800:
        return None
    K = max(1, -(-need // (2 * G)))
    if 2 * K * G > 2600:
        return None
    _, mul, _ = lib.semidirect_group(m, k2, r)
    T = np.array([[mul(x, y) for y in range(G)] for x in range(G)], dtype=np.int64)
    return G, K, T


# ----------------------------------------------------------------------------
# Greedy spare-degree extension (no-op for regular lifts).
# ----------------------------------------------------------------------------

def _two_colour(n, edges):
    """Return a 0/1 side label per vertex (bipartition), or None if not bipartite."""
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

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bold search: C anneals voltages of lifts over explicit group tables
    # (projective groups PSL/PGL(2,p) and semidirect products). Each attempt
    # targets at least best+2 vertices, so every success is a strict gain.
    if d >= 3 and D >= 3:
        failures = 0
        attempts = 0
        while attempts < 12 and failures < 4:
            remaining = search_deadline - time.monotonic()
            if remaining < 2.0:
                break
            attempts += 1
            need = best[0] + 2
            slice_s = min(remaining - 1.0, 11.0)
            setup = _make_setup(rng, need)
            if setup is None:
                continue
            G, K, T = setup
            edges = list(zip(range(G * G), T.ravel().tolist()))
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, K, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                    stdin_graph=(G, edges),
                    timeout=slice_s + 15.0,
                )
            except RuntimeError:
                failures += 1
                continue
            try:
                n, e = lib.parse_graph_text(out)
            except ValueError:
                continue
            consider(n, e)

    # Spare-degree extension, then a final validity guard.
    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, deadline)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
