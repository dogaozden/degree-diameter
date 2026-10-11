import itertools
import math
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over voltage lifts of a regular bipartite base
# multigraph with k + k vertices, lifted over the abelian group Z_a x Z_b.
#
# Base: for each layer j < DEG, a permutation tgt[.][j] of the k B-vertices, so the
# base is DEG-regular. Dart (u, j) carries voltage vol[u][j] in the group.
# The lift has 2k * G vertices, (x, g) with x in 0..2k-1 and g in the group.
# It is a bipartite, DEG-regular graph (duplicate edges are penalised).
#
# Lifts are vertex-transitive within each fibre, so the diameter test only needs
# BFS from the 2k vertices (x, 0). Cost = number of unreached (source, vertex)
# pairs, plus NN per duplicate dart pair. Cost 0 means the lift is valid.
#
# Moves: change one voltage, or swap two targets within one layer (keeps regularity).
# ----------------------------------------------------------------------------

LIFT_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 8
#define MAXD 16
#define MAXG 1024
#define MAXN (2 * MAXK * MAXG)

static int DEG, DIAM, K, GA, GB, G, NN;
static int tgt[MAXK][MAXD];
static int vol[MAXK][MAXD];
static int inU[MAXK][MAXD];
static int inJ[MAXK][MAXD];
static int ADDT[MAXG * MAXG];
static int NEGT[MAXG];
static int stampArr[MAXN];
static int curStamp = 0;
static int qbuf[MAXN];
static uint64_t rs = 88172645463325252ULL;

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

static void build_tables(void) {
    for (int x = 0; x < G; x++) {
        int x1 = x / GB, y1 = x % GB;
        NEGT[x] = ((GA - x1) % GA) * GB + ((GB - y1) % GB);
        for (int y = 0; y < G; y++) {
            int x2 = y / GB, y2 = y % GB;
            ADDT[x * G + y] = ((x1 + x2) % GA) * GB + ((y1 + y2) % GB);
        }
    }
}

/* In-darts of each B-vertex (each receives exactly DEG darts). */
static void build_in(void) {
    int cnt[MAXK];
    memset(cnt, 0, sizeof cnt);
    for (int u = 0; u < K; u++)
        for (int j = 0; j < DEG; j++) {
            int v = tgt[u][j];
            inU[v][cnt[v]] = u;
            inJ[v][cnt[v]] = j;
            cnt[v]++;
        }
}

/* Pairs of darts from the same A-vertex with equal target and voltage (duplicate edges). */
static long long dup_count(void) {
    long long c = 0;
    for (int u = 0; u < K; u++)
        for (int j = 0; j < DEG; j++)
            for (int l = j + 1; l < DEG; l++)
                if (tgt[u][j] == tgt[u][l] && vol[u][j] == vol[u][l]) c++;
    return c;
}

static long long eval_cost(void) {
    int n = NN;
    long long cost = 0;
    for (int s = 0; s < 2 * K; s++) {
        curStamp++;
        int head = 0, tail = 0;
        int src = s * G;
        stampArr[src] = curStamp;
        qbuf[tail++] = src;
        for (int lev = 0; lev < DIAM; lev++) {
            int end = tail;
            for (; head < end; head++) {
                int id = qbuf[head];
                int x = id / G;
                int g = id - x * G;
                if (x < K) {
                    for (int j = 0; j < DEG; j++) {
                        int nb = (K + tgt[x][j]) * G + ADDT[g * G + vol[x][j]];
                        if (stampArr[nb] != curStamp) {
                            stampArr[nb] = curStamp;
                            qbuf[tail++] = nb;
                        }
                    }
                } else {
                    int v = x - K;
                    for (int t = 0; t < DEG; t++) {
                        int u = inU[v][t];
                        int j = inJ[v][t];
                        int nb = u * G + ADDT[g * G + NEGT[vol[u][j]]];
                        if (stampArr[nb] != curStamp) {
                            stampArr[nb] = curStamp;
                            qbuf[tail++] = nb;
                        }
                    }
                }
            }
        }
        cost += n - tail;
    }
    return cost;
}

static long long full_cost(void) {
    build_in();
    return eval_cost() + (long long)NN * dup_count();
}

static void output_graph(void) {
    long long m = (long long)K * DEG * G;
    printf("%d %lld\n", NN, m);
    for (int u = 0; u < K; u++)
        for (int j = 0; j < DEG; j++) {
            int v = K + tgt[u][j];
            for (int g = 0; g < G; g++)
                printf("%d %d\n", u * G + g, v * G + ADDT[g * G + vol[u][j]]);
        }
}

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    K = atoi(argv[5]);
    GA = atoi(argv[6]);
    GB = atoi(argv[7]);
    if (DEG < 1 || DEG > MAXD || DIAM < 1 || K < 1 || K > MAXK || GA < 1 || GB < 1 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    G = GA * GB;
    if (G < 2 || G > MAXG) {
        printf("0 0\n");
        return 0;
    }
    NN = 2 * K * G;
    if (NN > MAXN) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();
    build_tables();

    /* random initial layers: each layer is a permutation of the B side */
    for (int j = 0; j < DEG; j++) {
        int p[MAXK];
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int t = rnd(i + 1);
            int tmp = p[i];
            p[i] = p[t];
            p[t] = tmp;
        }
        for (int i = 0; i < K; i++) {
            tgt[i][j] = p[i];
            vol[i][j] = rnd(G);
        }
    }

    long long cur = full_cost();
    if (cur == 0) {
        output_graph();
        return 0;
    }

    const double T0 = 4.0, T1 = 0.25;
    double t0 = (double)clock() / CLOCKS_PER_SEC;
    double el = 0.0, T = T0;
    long long it = 0;
    while (1) {
        if ((it & 15) == 0) {
            el = (double)clock() / CLOCKS_PER_SEC - t0;
            if (el >= tl) break;
            double ph = el / tl * 4.0;
            double pos = ph - floor(ph);
            T = T0 * pow(T1 / T0, pos);
        }
        it++;
        if (K >= 2 && rnd01() < 0.5) {
            int j = rnd(DEG);
            int i1 = rnd(K);
            int i2 = rnd(K - 1);
            if (i2 >= i1) i2++;
            int t1 = tgt[i1][j], t2 = tgt[i2][j];
            tgt[i1][j] = t2;
            tgt[i2][j] = t1;
            long long c2 = full_cost();
            double dl = (double)(c2 - cur);
            if (dl <= 0 || rnd01() < exp(-dl / T)) {
                cur = c2;
            } else {
                tgt[i1][j] = t1;
                tgt[i2][j] = t2;
            }
        } else {
            int u = rnd(K);
            int j = rnd(DEG);
            int old = vol[u][j];
            int nvv = rnd(G - 1);
            if (nvv >= old) nvv++;
            vol[u][j] = nvv;
            long long c2 = full_cost();
            double dl = (double)(c2 - cur);
            if (dl <= 0 || rnd01() < exp(-dl / T)) {
                cur = c2;
            } else {
                vol[u][j] = old;
            }
        }
        if (cur == 0) {
            output_graph();
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

RECORDS = {(11, 4): 1734, (3, 3): 14}


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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to q <= 9 for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _shape(G):
    """Factor G = a * b as Z_a x Z_b: prefer a non-cyclic split, else the most balanced one."""
    divs = [a for a in range(1, math.isqrt(G) + 1) if G % a == 0]
    nc = [a for a in divs if a > 1 and math.gcd(a, G // a) > 1]
    a = nc[-1] if nc else divs[-1]
    return a, G // a


def _lift_configs(T):
    """(k, G) pairs whose lifts have 2*k*G > T vertices, then one tie configuration at T."""
    cfgs = []
    for k in (3, 5, 6, 4, 8, 2, 7):
        cfgs.append((k, -(-(T + 1) // (2 * k))))
    cfgs.append((3, -(-T // 6)))
    out, seen = [], set()
    for k, G in cfgs:
        if 2 <= G <= 1024 and 2 * k * G <= 16384 and (k, G) not in seen:
            seen.add((k, G))
            out.append((k, G))
    return out


def _run_lift(d, D, seed, k, a, b, budget):
    """Run the C lift annealer for `budget` seconds; return parsed (n, edges), n = 0 on failure."""
    out = lib.run_c(LIFT_C, [d, D, seed, f"{budget:.2f}", k, a, b],
                    stdin_graph=None, timeout=budget + 5.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    deadline = start + max(0.5, 0.86 * tl - 2.0)

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
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    try:
        # Quick structured starts.
        if D == 3 and d >= 3:
            qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
            if qs:
                consider(*lib.projective_plane_incidence(qs[0]))
        if D >= 4:
            gq = _best_gq(d)
            if gq is not None:
                consider(*gq)
    except Exception:
        pass

    # Main phase: abelian voltage lifts of small bipartite regular bases, with
    # group orders chosen so the lift is just above the target order. Time is
    # split equally across configurations, and unused time carries forward.
    try:
        T = max(best_n, RECORDS.get((d, D), 0))
        cfgs = _lift_configs(T)
        for idx, (k, G) in enumerate(cfgs):
            remaining = deadline - time.monotonic()
            budget = remaining / (len(cfgs) - idx)
            if budget < 0.8:
                break
            a, b = _shape(G)
            try:
                n2, e2 = _run_lift(d, D, seed * 131 + idx, k, a, b, budget)
                consider(n2, e2)
            except Exception:
                pass
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
