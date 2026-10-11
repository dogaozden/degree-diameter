import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley graphs over the semidirect product Z_m x| Z_k.
#
# Vertices are (0, x) and (1, x) for x in G (|G| = m*k). Fix a connection set
# S of d distinct group elements and join (0, x) to (1, x*s) for s in S. Left
# multiplication is an automorphism, so each side is vertex-transitive, and
# the diameter test only needs BFS from (0, identity) and (1, identity).
# Simulated annealing changes one element of S at a time. Cost is the number of
# unreached (source, target) pairs from the two sources; cost 0 means diameter <= D.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 4096
#define MAXK 256
#define MAXD 64
#define MAXN (2*MAXG)

static int d, D, m, k, G, N;
static int powr[MAXK];
static int S[MAXD], invS[MAXD];
static char inS[MAXG];
static int vis[MAXN], dist[MAXN], qu[MAXN];
static int stampCur = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int n) { return (int)(nextr() % (uint64_t)n); }

static double rnd01(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

/* (a,b)*(c,e) = (a + r^b c, b + e), element (a,b) coded as a*k + b */
static int gmul(int x, int y) {
    int a = x / k, b = x % k, c = y / k, e = y % k;
    return ((a + powr[b] * c) % m) * k + (b + e) % k;
}

static int ginv(int x) {
    int a = x / k, b = x % k;
    int nb = (k - b) % k;
    long long t = ((long long)(m - powr[nb]) % m) * a % m;
    return (int)t * k + nb;
}

static int reach_bad(int src) {
    stampCur++;
    int qh = 0, qt = 0;
    qu[qt++] = src;
    vis[src] = stampCur;
    dist[src] = 0;
    while (qh < qt) {
        int u = qu[qh++];
        if (dist[u] >= D) continue;
        int du = dist[u] + 1;
        if (u < G) {
            for (int i = 0; i < d; i++) {
                int v = G + gmul(u, S[i]);
                if (vis[v] != stampCur) {
                    vis[v] = stampCur;
                    dist[v] = du;
                    qu[qt++] = v;
                }
            }
        } else {
            int z = u - G;
            for (int i = 0; i < d; i++) {
                int v = gmul(z, invS[i]);
                if (vis[v] != stampCur) {
                    vis[v] = stampCur;
                    dist[v] = du;
                    qu[qt++] = v;
                }
            }
        }
    }
    return N - qt;
}

static long long cost(void) {
    int b0 = reach_bad(0);
    int b1 = reach_bad(G);
    return (long long)b0 + (long long)b1;
}

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    m = atoi(argv[5]);
    k = atoi(argv[6]);
    int r = atoi(argv[7]);
    if (d < 1 || d > MAXD || D < 1 || m < 2 || k < 1 || k > MAXK || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    G = m * k;
    if (G > MAXG || G <= d) {
        printf("0 0\n");
        return 0;
    }
    N = 2 * G;
    rs = seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    powr[0] = 1 % m;
    for (int b = 1; b < k; b++) powr[b] = (int)((long long)powr[b - 1] * r % m);
    if (((long long)powr[k - 1] * r) % m != 1 % m) {
        printf("0 0\n");
        return 0;
    }

    for (int i = 0; i < d; i++) {
        int x;
        do { x = rnd(G); } while (inS[x]);
        inS[x] = 1;
        S[i] = x;
        invS[i] = ginv(x);
    }

    long long cur = cost();
    double t0 = (double)clock() / CLOCKS_PER_SEC;
    double frac = 0.0;
    long long it = 0;
    while (cur > 0) {
        if ((it & 63) == 0) {
            double el = (double)clock() / CLOCKS_PER_SEC - t0;
            if (el >= tl) break;
            frac = el / tl;
        }
        it++;
        int i = rnd(d);
        int x;
        do { x = rnd(G); } while (inS[x]);
        int old = S[i];
        inS[old] = 0;
        inS[x] = 1;
        S[i] = x;
        invS[i] = ginv(x);
        long long c2 = cost();
        long long dl = c2 - cur;
        double T = 0.6 * (1.0 - frac) + 0.05;
        if (dl <= 0 || rnd01() < exp(-(double)dl / T)) {
            cur = c2;
        } else {
            inS[x] = 0;
            inS[old] = 1;
            S[i] = old;
            invS[i] = ginv(old);
        }
    }

    if (cur != 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", N, G * d);
    for (int x = 0; x < G; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, G + gmul(x, S[i]));
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q): degree q+1, diameter 4."""
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
    """W(q) for the largest prime power q <= d - 1 (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _group_options(G, rng):
    """(m, k, r) triples with |Z_m x| Z_k| = G; non-cyclic options first, shuffled within each class."""
    nonab, cyc = [], []
    for k in range(1, min(G, 24) + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            cyc.append((m, 1, 1))
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if len(rs) > 6:
            rs = rng.sample(rs, 6)
        nonab.extend((m, k, r) for r in rs)
    rng.shuffle(nonab)
    rng.shuffle(cyc)
    return nonab + cyc


def _bicayley_search(d, D, rng, g_start, deadline, consider):
    """Sweep the order G = |group| upward, running the C annealer on each candidate group."""
    G = g_start
    while G <= 4000 and time.monotonic() < deadline - 1.0:
        opts = _group_options(G, rng)
        for m, k, r in opts[:3]:
            rem = deadline - time.monotonic()
            if rem < 1.5:
                return
            slice_s = min(2.5, rem - 0.5)
            try:
                out = lib.run_c(C_SOURCE,
                                [d, D, rng.randrange(1, 1 << 30), f"{slice_s:.2f}", m, k, r],
                                stdin_graph=None, timeout=slice_s + 5.0)
                n, e = lib.parse_graph_text(out)
            except Exception:
                continue
            if n > 0 and lib.is_valid(n, e, d, D):
                consider(n, e)
                break
        G += 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

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
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Quick structured base graphs.
    try:
        if D >= 4:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        if D == 3:
            qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:2]
            for q in qs:
                pn, pe = lib.projective_plane_incidence(q)
                consider(pn, pe)
    except Exception:
        pass

    # Main search: bi-Cayley graphs over non-abelian groups, one order at a time.
    deadline = start + 0.85 * tl
    if d >= 3 and D >= 2:
        try:
            g_start = max(best_n // 2 + 1, d + 2)
            _bicayley_search(d, D, rng, g_start, deadline, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
