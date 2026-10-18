"""Bi-Cayley lift search, exact C annealing version.

Changes from the parent:
- The lift search moves into C. Each candidate is a bi-Cayley graph over Z_m x| Z_k2
  with k base blocks per side (k = 1..6), a random permutation per layer, and a voltage per
  dart. Simulated annealing minimises the exact number of (block representative, vertex)
  pairs at distance > D, plus a penalty for duplicate darts. By G-invariance, zero cost
  means the lift has diameter <= D.
- The C engine runs many group/base choices in one process and ratchets the target order
  upward. It returns the largest valid lift it finds.
- Python keeps the exact small constructions (projective planes, Araujo-Pardo-Lopez,
  W(q)) and the K_{d,d} fallback. Every output is checked with lib.is_valid.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley lift annealing over semidirect products Z_M x| Z_K2.
 * Usage: prog d D seed time_limit
 * stdout: "n m" + edges of the largest valid lift found, or "0 0".
 *
 * Vertices: A block i (0..K-1) = i*G + g, B block j = (K+j)*G + h, G = M*K2.
 * Layer l pairs A block i with B block perm[l][i] through voltage volt[l][i]:
 *   A_{i,g} ~ B_{p,g*s}.   Left multiplication is an automorphism, so
 *   diameter <= D  <=>  every block representative reaches all N vertices within D.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 65536
#define MAXDEG 32
#define MAXK 8
#define MAXG 8192
#define PENALTY 1000L

static int d, D;
static int K, M, K2, R, G, NN;
static int rpow[64];
static int perm[MAXDEG][MAXK];
static int volt[MAXDEG][MAXK];
static int vinv[MAXDEG][MAXK];
static int nbr[MAXN][MAXDEG];
static int bestnbr[MAXN][MAXDEG];
static int bestN = 0, bestNA = 0;
static int vis[MAXN];
static int qbuf[MAXN];
static int vstamp = 0;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long gcdl(long a, long b) {
    while (b) {
        long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static void set_group_pows(void) {
    rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) rpow[b] = (int)((long)rpow[b - 1] * R % M);
}

/* Element code x = a*K2 + b, meaning (a, b) in Z_M x| Z_K2 with r^b acting on a. */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    int t = (int)((long)rpow[b] * c % M);
    int aa = (a + t) % M;
    return aa * K2 + (b + e) % K2;
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    int t = (int)((long)rpow[nb] * a % M);
    int na = (M - t) % M;
    return na * K2 + nb;
}

static int sample_group(long target) {
    static const int k2s[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8,
                                9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    for (int tries = 0; tries < 300; tries++) {
        int k2 = k2s[rndint(20)];
        if (k2 > 1 && (long)k2 * 20L > target) continue; /* keep overshoot small */
        long m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (m * k2 > MAXG) continue;
        int r = 1;
        if (k2 > 1) {
            r = -1;
            for (int t = 0; t < 100 && r < 0; t++) {
                long c = (m > 2) ? 2 + rndint((int)(m - 2)) : 1;
                if (gcdl(c, m) == 1 && powmod(c, k2, m) == 1 % m) r = (int)c;
            }
            if (r < 0) continue;
        }
        M = (int)m;
        K2 = k2;
        R = r;
        G = M * K2;
        set_group_pows();
        return 1;
    }
    return 0;
}

/* Write layer l's darts for A block i (and the matching B block). */
static void set_block(int l, int i) {
    int j = perm[l][i];
    int s = volt[l][i], si = vinv[l][i];
    for (int g = 0; g < G; g++) {
        nbr[i * G + g][l] = (K + j) * G + gmul(g, s);
        nbr[(K + j) * G + g][l] = i * G + gmul(g, si);
    }
}

/* Exact cost: sum over the 2K block representatives of the vertices not within distance D. */
static long eval_cost(void) {
    long cost = 0;
    for (int s = 0; s < 2 * K; s++) {
        vstamp++;
        int head = 0, tail = 0;
        int src = s * G;
        qbuf[tail++] = src;
        vis[src] = vstamp;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int v = qbuf[head++];
                for (int l = 0; l < d; l++) {
                    int u = nbr[v][l];
                    if (vis[u] != vstamp) {
                        vis[u] = vstamp;
                        qbuf[tail++] = u;
                    }
                }
            }
        }
        cost += NN - tail;
    }
    return cost;
}

/* Duplicate darts (same A block, same B block, same voltage) would create multi-edges. */
static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1][i] == perm[l2][i] && volt[l1][i] == volt[l2][i]) c++;
    return c;
}

static void save_best(void) {
    if (NN <= bestN) return;
    for (int v = 0; v < NN; v++)
        for (int l = 0; l < d; l++) bestnbr[v][l] = nbr[v][l];
    bestN = NN;
    bestNA = K * G;
}

static int anneal(long iters, long patience, double tend) {
    NN = 2 * K * G;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = t;
        }
        for (int i = 0; i < K; i++) {
            volt[l][i] = rndint(G);
            vinv[l][i] = ginv(volt[l][i]);
        }
        for (int i = 0; i < K; i++) set_block(l, i);
    }

    long cost = eval_cost() + PENALTY * dupcount();
    long cost0 = cost > 1 ? cost : 1;
    double T0 = 2.0 + 0.02 * (double)cost0;
    long bestc = cost, last = 0;

    for (long it = 0; it < iters && cost > 0; it++) {
        if ((it & 7) == 0 && now() > tend) break;
        if (it - last > patience) break;
        double T = 0.3 + T0 * (1.0 - (double)it / (double)iters);

        if (K >= 2 && rndint(2) == 1) {
            /* swap the B targets of two A blocks in one layer */
            int l = rndint(d);
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int t = perm[l][i1];
            perm[l][i1] = perm[l][i2];
            perm[l][i2] = t;
            set_block(l, i1);
            set_block(l, i2);
            long c2 = eval_cost() + PENALTY * dupcount();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                t = perm[l][i1];
                perm[l][i1] = perm[l][i2];
                perm[l][i2] = t;
                set_block(l, i1);
                set_block(l, i2);
            }
        } else {
            /* change one voltage */
            int l = rndint(d), i = rndint(K);
            int old = volt[l][i], oldi = vinv[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            volt[l][i] = nw;
            vinv[l][i] = ginv(nw);
            set_block(l, i);
            long c2 = eval_cost() + PENALTY * dupcount();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                volt[l][i] = old;
                vinv[l][i] = oldi;
                set_block(l, i);
            }
        }
        if (cost < bestc) {
            bestc = cost;
            last = it;
        }
    }
    if (cost != 0) return 0;
    save_best();
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double tend = now() + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) {
        printf("0 0\n");
        return 0;
    }

    long mb = moore_bound();
    while (now() < tend) {
        long nt;
        if (bestN == 0) nt = 2L * d;
        else nt = bestN + 2 + rndint((int)(bestN / 25 + 1));
        if (nt > mb) break;
        int k = 1 + rndint(MAXK - 2); /* base blocks per side: 1..6 */
        long gt = (nt + 2L * k - 1) / (2L * k);
        if (gt < 2) gt = 2;
        if (!sample_group(gt)) continue;
        long cand = 2L * k * G;
        if (cand > MAXN || cand > mb || cand <= bestN) continue;
        K = k;
        anneal(6000, 1500, tend);
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %ld\n", bestN, (long)bestNA * d);
    for (int v = 0; v < bestNA; v++)
        for (int l = 0; l < d; l++) printf("%d %d\n", v, bestnbr[v][l]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions.
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


# ----------------------------------------------------------------------------
# Saturation: greedily add missing bipartite edges between deficient vertices.
# Distances only shrink, so validity is kept; callers still verify with lib.is_valid.
# ----------------------------------------------------------------------------

def _saturate(n, edges, d, D):
    """Greedily add missing bipartite edges between deficient vertices; returns (n, edges)."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if color[y] == -1:
                    color[y] = 1 - color[x]
                    stack.append(y)
    A = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    B = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    out = {(min(u, v), max(u, v)) for u, v in edges}
    for a in A:
        for b in B:
            if len(adj[a]) >= d:
                break
            if len(adj[b]) >= d or b in adj[a]:
                continue
            adj[a].add(b)
            adj[b].add(a)
            out.add((min(a, b), max(a, b)))
    return n, sorted(out)


def _safe_saturate(n, edges, d, D):
    """Saturate, but fall back to the input if anything goes wrong or the result is invalid."""
    try:
        sn, se = _saturate(n, edges, d, D)
        if lib.is_valid(sn, se, d, D):
            return sn, se
    except Exception:
        pass
    return n, edges


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    def consider_saturated(n, e):
        sn, se = _safe_saturate(n, e, d, D)
        consider(sn, se)
        consider(n, e)

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider_saturated(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main engine: exact bi-Cayley lift annealing in C, using the remaining time.
    remaining = final - time.monotonic() - 1.0
    if remaining > 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, int(seed), round(remaining, 2)],
                             timeout=remaining + 10)
            n, e = lib.parse_graph_text(text)
            consider_saturated(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
