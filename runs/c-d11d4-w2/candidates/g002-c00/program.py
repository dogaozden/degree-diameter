import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over voltage lifts of a bipartite base graph
# with k vertices per side and degree DEG, lifted over the semidirect product
# Z_GM x| Z_GK (element (a, b) coded a*GK + b, (a, b)(c, d) = (a + r^b c, b + d)).
#
# Cost = number of (base source, vertex) pairs at distance > DIAM. Left
# multiplication by the group is an automorphism of every lift, so the
# diameter is exact when every base vertex's identity fibre reaches all
# vertices within DIAM. Parallel darts with equal voltage give duplicate
# edges; they are removed on output (degrees only drop, so validity holds).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXB 8
#define MAXDEG 32
#define MAXV 8192
#define STALL 30000

static int DEG, DIAM, BK, GM, GK, RR, NG, V;
static int pw[64];
static int perm[MAXDEG][MAXB], volt[MAXDEG][MAXB];
static int bperm[MAXDEG][MAXB], bvolt[MAXDEG][MAXB];
static int sperm[MAXDEG][MAXB], svolt[MAXDEG][MAXB];
static int adj[MAXV][MAXDEG];
static int adjn[MAXV];
static unsigned int vis[MAXV];
static unsigned int stamp = 0;
static int qu[MAXV];
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

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int gmul(int x, int g) {
    int a = x / GK, b = x % GK;
    int c = g / GK, d = g % GK;
    long long t = (long long)pw[b] * c;
    int a2 = (int)((a + t) % GM);
    int b2 = (b + d) % GK;
    return a2 * GK + b2;
}

static void build(void) {
    V = 2 * BK * NG;
    memset(adjn, 0, sizeof(int) * (size_t)V);
    for (int t = 0; t < DEG; t++) {
        for (int i = 0; i < BK; i++) {
            int j = BK + perm[t][i];
            int g = volt[t][i];
            for (int x = 0; x < NG; x++) {
                int a = i * NG + x;
                int b = j * NG + gmul(x, g);
                adj[a][adjn[a]++] = b;
                adj[b][adjn[b]++] = a;
            }
        }
    }
}

static long long cost(void) {
    build();
    long long bad = 0;
    for (int u = 0; u < 2 * BK; u++) {
        stamp++;
        if (stamp == 0) {
            memset(vis, 0, sizeof vis);
            stamp = 1;
        }
        int src = u * NG;
        int head = 0, tail = 0;
        vis[src] = stamp;
        qu[tail++] = src;
        for (int lev = 0; lev < DIAM; lev++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int x = qu[head++];
                for (int i = 0; i < DEG; i++) {
                    int y = adj[x][i];
                    if (vis[y] != stamp) {
                        vis[y] = stamp;
                        qu[tail++] = y;
                    }
                }
            }
        }
        bad += V - tail;
    }
    return bad;
}

static void shuffle_perm(int *p) {
    for (int i = BK - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t = p[i];
        p[i] = p[j];
        p[j] = t;
    }
}

static void save_cur(void) {
    memcpy(sperm, perm, sizeof perm);
    memcpy(svolt, volt, sizeof volt);
}

static void restore_cur(void) {
    memcpy(perm, sperm, sizeof perm);
    memcpy(volt, svolt, sizeof volt);
}

static void save_best(void) {
    memcpy(bperm, perm, sizeof perm);
    memcpy(bvolt, volt, sizeof volt);
}

static void restore_best(void) {
    memcpy(perm, bperm, sizeof perm);
    memcpy(volt, bvolt, sizeof volt);
}

static void output(void) {
    long long m = 0;
    int A = BK * NG;
    for (int a = 0; a < A; a++) {
        for (int i = 0; i < adjn[a]; i++) {
            int dup = 0;
            for (int k = 0; k < i; k++)
                if (adj[a][k] == adj[a][i]) {
                    dup = 1;
                    break;
                }
            if (!dup) m++;
        }
    }
    printf("%d %lld\n", V, m);
    for (int a = 0; a < A; a++) {
        for (int i = 0; i < adjn[a]; i++) {
            int dup = 0;
            for (int k = 0; k < i; k++)
                if (adj[a][k] == adj[a][i]) {
                    dup = 1;
                    break;
                }
            if (!dup) printf("%d %d\n", a, adj[a][i]);
        }
    }
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
    BK = atoi(argv[5]);
    GM = atoi(argv[6]);
    GK = atoi(argv[7]);
    RR = atoi(argv[8]);
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1 || BK < 1 || BK > MAXB ||
        GM < 1 || GK < 1 || GK > 64 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    NG = GM * GK;
    if (2LL * BK * NG > MAXV) {
        printf("0 0\n");
        return 0;
    }
    RR = ((RR % GM) + GM) % GM;
    if (gcd_i(RR, GM) != 1) {
        printf("0 0\n");
        return 0;
    }
    pw[0] = 1 % GM;
    for (int b = 1; b < GK; b++) pw[b] = (int)((long long)pw[b - 1] * RR % GM);
    if (((long long)pw[GK - 1] * RR) % GM != 1 % GM) {
        printf("0 0\n");
        return 0;
    }

    rs = seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    for (int t = 0; t < DEG; t++) {
        for (int i = 0; i < BK; i++) perm[t][i] = i;
        shuffle_perm(perm[t]);
        for (int i = 0; i < BK; i++) volt[t][i] = rnd(NG);
    }

    long long cur = cost();
    long long bestc = cur;
    save_best();
    clock_t c0 = clock();
    double frac = 0.0, T = 1.0;
    long stall = 0, iter = 0;

    while (cur > 0) {
        if ((iter & 127) == 0) {
            frac = ((double)(clock() - c0) / CLOCKS_PER_SEC) / tl;
            if (frac >= 1.0) break;
            T = 0.05 + 1.5 * (1.0 - frac);
        }
        iter++;
        save_cur();
        int t = rnd(DEG);
        if (rnd01() < 0.85) {
            int i = rnd(BK);
            volt[t][i] = rnd(NG);
        } else {
            shuffle_perm(perm[t]);
            for (int i = 0; i < BK; i++) volt[t][i] = rnd(NG);
        }
        long long c2 = cost();
        double dl = (double)(c2 - cur);
        if (dl <= 0 || rnd01() < exp(-dl / T)) {
            cur = c2;
            if (cur < bestc) {
                bestc = cur;
                save_best();
                stall = 0;
            } else {
                stall++;
            }
        } else {
            restore_cur();
            stall++;
        }
        if (stall > STALL) {
            restore_best();
            for (int k = 0; k < 3; k++) {
                int t2 = rnd(DEG);
                int i2 = rnd(BK);
                volt[t2][i2] = rnd(NG);
            }
            cur = cost();
            stall = 0;
        }
    }

    cur = cost();
    if (cur == 0) output();
    else printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4, order 2(q+1)(q^2+1)."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q <= 9 with q + 1 <= d (kept small for speed)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _saturate_gq(P, n, edges, d, rng):
    """Join non-incident point-line pairs with spare degree (points are 0..P-1, lines P..n-1)."""
    deg = [0] * n
    existing = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        existing.add((u, v))
    out = list(edges)
    pts = [p for p in range(P) if deg[p] < d]
    lns = [l for l in range(P, n) if deg[l] < d]
    pairs = [(p, l) for p in pts for l in lns if (p, l) not in existing]
    rng.shuffle(pairs)
    for p, l in pairs:
        if deg[p] < d and deg[l] < d:
            out.append((p, l))
            deg[p] += 1
            deg[l] += 1
    return out


def _group_options(N, rng):
    """Semidirect products Z_GM x| Z_GK of order N as (GM, GK, r) triples, always including cyclic."""
    opts = [(N, 1, 1)]
    for GK in range(2, 13):
        if N % GK:
            continue
        GM = N // GK
        if GM < 2:
            continue
        rs_ = [r for r in range(1, GM)
               if math.gcd(r, GM) == 1 and pow(r, GK, GM) == 1 % GM]
        rng.shuffle(rs_)
        for r in rs_[:6]:
            opts.append((GM, GK, r))
    return opts


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

    # Safe fallback: K_{d,d}.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    hard_deadline = start + 0.85 * tl - 2.0

    # D >= 4: generalized quadrangle W(q) with spare degree filled in.
    if D >= 4 and d >= 5 and hard_deadline - time.monotonic() > 15:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            P = gq[0] // 2
            sat_edges = _saturate_gq(P, gq[0], gq[1], d, rng)
            consider(gq[0], sat_edges)

    # Main search: lifts of small base graphs over semidirect products, annealed in C.
    if D >= 2 and d >= 2:
        bases = [2, 2, 2, 3, 3, 4, 5]
        T = best_n + 16
        step = 16
        attempt = 0
        while True:
            remaining = hard_deadline - time.monotonic()
            if remaining < 4.0:
                break
            k = rng.choice(bases)
            need = max(T, best_n + 2)
            N = -(-need // (2 * k)) + rng.randrange(0, 3)
            opts = _group_options(N, rng)
            GM, GK, R = rng.choice(opts)
            slice_ = min(remaining - 2.0, max(3.0, remaining * 0.3))
            if slice_ < 2.0:
                break
            c_seed = (seed * 7919 + attempt) % 2000000011
            try:
                out = lib.run_c(C_SOURCE, [d, D, c_seed, f"{slice_:.2f}", k, GM, GK, R],
                                timeout=slice_ + 4.0)
                n2, e2 = lib.parse_graph_text(out)
            except Exception:
                break
            if n2 > best_n and lib.is_valid(n2, e2, d, D):
                consider(n2, e2)
                step = min(step * 2, 128)
            else:
                step = max(2, step // 2)
            T = best_n + step
            attempt += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
