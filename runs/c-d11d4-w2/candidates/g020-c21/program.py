import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over Z_M x| Z_K2 voltage lifts of a bipartite
# base with 2K vertices and DEG darts per base vertex. Cost = number of vertex
# pairs at distance > DIAM, computed with bitset ball propagation. Moves change
# one voltage, or swap two side-1 endpoints inside one permutation layer (both
# keep every lift vertex at degree DEG). Output is the first zero-cost lift.
# ----------------------------------------------------------------------------

LIFT_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXV 4096
#define WMAX 64
#define MAXDEG 32
#define MAXDART 1024
#define MAXK 64

static int DEG, DIAM, K, M, K2, R, ORD, NV, NDART;
static int dU[MAXDART], dV[MAXDART], dG[MAXDART];
static int pw[MAXK];
static int adj[MAXV][MAXDEG];
static int cnt[MAXV];
static uint64_t BA[MAXV * WMAX], BB[MAXV * WMAX];
static int outA[MAXV * MAXDEG], outB[MAXV * MAXDEG];
static uint64_t rs = 1;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nextr() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* (a,b)*(c,d) = (a + r^b c, b + d), element coded as a*K2 + b. */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, d = y % K2;
    long long A = ((long long)a + (long long)pw[b] * c) % M;
    return (int)(A * K2 + (b + d) % K2);
}

static void init_darts(void) {
    NDART = DEG * K;
    int perm[MAXK];
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            int idx = l * K + i;
            dU[idx] = i;
            dV[idx] = K + perm[i];
            dG[idx] = rnd(ORD);
        }
    }
}

static void build_lift(void) {
    for (int v = 0; v < NV; v++) cnt[v] = 0;
    for (int j = 0; j < NDART; j++) {
        int u = dU[j], w = dV[j], g = dG[j];
        for (int x = 0; x < ORD; x++) {
            int a = u * ORD + x;
            int b = w * ORD + gmul(x, g);
            adj[a][cnt[a]++] = b;
            adj[b][cnt[b]++] = a;
        }
    }
}

static long long eval_cost(void) {
    int W = (NV + 63) >> 6;
    uint64_t *cur = BA, *nxt = BB, *tmp;
    for (int v = 0; v < NV; v++) {
        uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) s[w] = 0;
        s[v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < NV; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            uint64_t *s = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) o[w] = s[w];
            for (int i = 0; i < cnt[v]; i++) {
                uint64_t *t = cur + (size_t)adj[v][i] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < NV; v++) {
        uint64_t *s = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(s[w]);
        bad += NV - c;
    }
    return bad / 2;
}

static void output_graph(void) {
    build_lift();
    for (int v = 0; v < NV; v++) {
        for (int i = 1; i < cnt[v]; i++) {
            int x = adj[v][i];
            int k = i - 1;
            while (k >= 0 && adj[v][k] > x) {
                adj[v][k + 1] = adj[v][k];
                k--;
            }
            adj[v][k + 1] = x;
        }
    }
    int ne = 0;
    for (int v = 0; v < NV; v++) {
        for (int i = 0; i < cnt[v]; i++) {
            int w = adj[v][i];
            if (w > v && (i == 0 || adj[v][i - 1] != w)) {
                outA[ne] = v;
                outB[ne] = w;
                ne++;
            }
        }
    }
    printf("%d %d\n", NV, ne);
    for (int e = 0; e < ne; e++) printf("%d %d\n", outA[e], outB[e]);
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    K = atoi(argv[5]);
    M = atoi(argv[6]);
    K2 = atoi(argv[7]);
    R = atoi(argv[8]);
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1 || tl <= 0 || K < 1 || K > MAXK ||
        M < 2 || K2 < 1 || K2 > MAXK) {
        printf("0 0\n");
        return 0;
    }
    ORD = M * K2;
    NV = 2 * K * ORD;
    if (NV > MAXV || DEG * K > MAXDART) {
        printf("0 0\n");
        return 0;
    }
    R = ((R % M) + M) % M;
    pw[0] = 1 % M;
    for (int i = 1; i < K2; i++) pw[i] = (int)((long long)pw[i - 1] * R % M);

    rs = seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    init_darts();
    build_lift();
    long long cost = eval_cost();
    double t0 = (double)clock() / CLOCKS_PER_SEC;

    while (cost > 0) {
        double frac = ((double)clock() / CLOCKS_PER_SEC - t0) / tl;
        if (frac >= 1.0) break;
        double T = 0.25 + 1.2 * (1.0 - frac);
        int type = (K >= 2 && rnd01() < 0.5) ? 1 : 0;
        int j = 0, oldg = 0, idx1 = 0, idx2 = 0;
        if (type == 0) {
            j = rnd(NDART);
            oldg = dG[j];
            int ng;
            do {
                ng = rnd(ORD);
            } while (ng == oldg);
            dG[j] = ng;
        } else {
            int l = rnd(DEG);
            int i1 = rnd(K);
            int i2 = rnd(K - 1);
            if (i2 >= i1) i2++;
            idx1 = l * K + i1;
            idx2 = l * K + i2;
            int t = dV[idx1];
            dV[idx1] = dV[idx2];
            dV[idx2] = t;
        }
        build_lift();
        long long c2 = eval_cost();
        double dl = (double)(c2 - cost);
        if (dl <= 0 || rnd01() < exp(-dl / T)) {
            cost = c2;
        } else {
            if (type == 0) {
                dG[j] = oldg;
            } else {
                int t = dV[idx1];
                dV[idx1] = dV[idx2];
                dV[idx2] = t;
            }
            build_lift();
        }
    }
    if (cost != 0) {
        printf("0 0\n");
        return 0;
    }
    output_graph();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _norm(F, v):
    """Scale a nonzero vector so its first nonzero coordinate is 1."""
    c = next(x for x in v if x)
    inv = F.inv(c)
    return tuple(F.mul(inv, x) for x in v)


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1). Lines are generated from the
    smallest point on each line, with a numpy-vectorised collinearity test.
    """
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    P = len(pts)
    index = {v: i for i, v in enumerate(pts)}
    A = np.array(pts, dtype=np.int64)
    mul, add = F.mul_table, F.add_table
    neg = np.array([F.neg(a) for a in range(q)], dtype=np.int64)
    covered = np.zeros((P, P), dtype=bool)
    idx = np.arange(P)
    lines = []
    for i in range(P):
        x = pts[i]
        t1 = mul[x[0], A[:, 1]]
        t2 = mul[x[1], A[:, 0]]
        t3 = mul[x[2], A[:, 3]]
        t4 = mul[x[3], A[:, 2]]
        form = add[add[t1, neg[t2]], add[t3, neg[t4]]]
        base = (form == 0) & (idx > i)
        cand = np.nonzero(base & ~covered[i])[0]
        while cand.size:
            j = int(cand[0])
            y = pts[j]
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[_norm(F, v)])
            Larr = np.array(sorted(L), dtype=np.int64)
            lines.append(Larr)
            covered[np.ix_(Larr, Larr)] = True
            cand = np.nonzero(base & ~covered[i])[0]
    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((int(p), P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, capped at q <= 9 for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order (distances only shrink)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _twin_grow(n, edges, d, rng, deadline):
    """Add twin vertices (same neighbourhood) while all neighbours have spare degree."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
        order = list(range(n))
        rng.shuffle(order)
        for x in order:
            if time.monotonic() >= deadline:
                break
            nb = adj[x]
            if not nb or any(deg[y] >= d for y in nb):
                continue
            v = n
            n += 1
            adj.append(list(nb))
            deg.append(len(nb))
            for y in nb:
                adj[y].append(v)
                deg[y] += 1
                edges.append((y, v))
            changed = True
    return n, edges


def _group_choices(G, rng):
    """Semidirect factorisations (M, K2, R) of a group of order G, with M >= 2 and K2 <= 64."""
    out = []
    for K2 in range(1, min(G, 64) + 1):
        if G % K2:
            continue
        M = G // K2
        if M < 2:
            continue
        out.append((M, K2, 1))  # R = 1 is the direct product Z_M x Z_K2
        if M >= 3 and K2 >= 2:
            for _ in range(8):
                r = rng.randrange(2, M)
                if math.gcd(r, M) == 1 and pow(r, K2, M) == 1 % M:
                    out.append((M, K2, r))
                    break
    return out


def _lift_phase(d, D, seed, deadline, rng, consider, best_n):
    """Repeatedly run the C annealer on lifts of 2K-vertex bases over groups just above the best order."""
    Ks = [1, 2, 3, 4, 5, 6]
    target = {}
    errors = 0
    call = 0
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 4.0 or errors >= 3:
            break
        K = rng.choice(Ks)
        G = max(target.get(K, 0), best_n() // (2 * K) + 1)
        target[K] = G
        choices = _group_choices(G, rng)
        if not choices:
            target[K] = G + 1
            continue
        M, K2, R = rng.choice(choices)
        budget = min(12.0, remaining - 2.0)
        call += 1
        try:
            out = lib.run_c(LIFT_C, [d, D, seed * 7919 + call, f"{budget:.2f}", K, M, K2, R],
                            timeout=budget + 5.0)
            n, edges = lib.parse_graph_text(out)
        except Exception:
            errors += 1
            continue
        if n > best_n() and lib.is_valid(n, edges, d, D):
            consider(n, edges)
            target[K] = G + 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Calibration: D = 3 with d - 1 a prime power is the Moore-optimal incidence graph.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, e0, d, D):
            return n0, e0

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n_val = best[0]

    def consider(n, e):
        nonlocal best, best_n_val
        if n > best_n_val and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n_val = n

    def best_n():
        return best_n_val

    deadline = start + 0.8 * tl - 1.0

    if D == 3:
        # Projective planes for the largest prime powers q + 1 <= d, plus twin growth.
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            pn, pe = lib.projective_plane_incidence(q)
            consider(pn, pe)
            tn, te = _twin_grow(pn, pe, d, rng, start + 0.5 * tl)
            consider(tn, te)

    elif D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            sat_e = _saturate_edges(gq[0], gq[1], d, rng)
            consider(gq[0], sat_e)
            tn, te = _twin_grow(gq[0], sat_e, d, rng, start + 0.45 * tl)
            consider(tn, te)
            if d >= 5:
                _lift_phase(d, D, seed, deadline, rng, consider, best_n)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
