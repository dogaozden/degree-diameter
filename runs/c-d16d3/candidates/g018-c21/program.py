import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy
#
# 1. Safe fallback: K_{d,d}, valid for every D >= 2.
# 2. Arc-extended projective plane graphs (diameter 3), as in the parent.
#    For d = 16 this is the 394-vertex incumbent.
# 3. NEW: a C engine that searches bi-Cayley (voltage) lifts over semidirect
#    products Z_m x| Z_k2 with K base vertices per side and a d-regular base
#    structure. Each layer L is a permutation p_L of the K base vertices, and
#    dart (L, i) carries a voltage s in the group, joining A_{i,g} to
#    B_{p_L(i), g*s}. Left multiplication is an automorphism, so only the 2K
#    base representatives need BFS. Cost = unreached (rep, vertex) pairs within
#    distance D, plus a penalty for duplicate darts. Simulated annealing runs
#    with restarts, and the target order ratchets upward after each success.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 1200
#define DUP_PEN 3
#define ITERS 60000

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int dd = 0, DD = 0;
static int KB = 0, GG = 0, NN = 0;
static int *mt = NULL, *perm = NULL, *volt = NULL, *adj = NULL, *mark = NULL, *queue = NULL;
static int stamp = 0;
static double tend = 0.0;
static int *best_adj = NULL;
static int bestN = 0, bestK = 0, bestG = 0;

static long lgcd(long a, long b) {
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

/* Semidirect product Z_m x| Z_k2 with r^k2 = 1 mod m; element a*k2+b,
   (a,b)(c,e) = (a + r^b c, b + e). Order G = m*k2. */
static void setup_group(int G, int k2, int m, long r) {
    long *pw = malloc(sizeof(long) * (size_t)k2);
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (pw[b - 1] * r) % m;
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            long na = ((long)a + pw[b] * (long)c) % m;
            int nb = (b + e) % k2;
            mt[x * G + y] = (int)(na * k2 + nb);
        }
    }
    free(pw);
}

static int bfs(int src) {
    stamp++;
    int head = 0, tail = 0;
    queue[tail++] = src;
    mark[src] = stamp;
    for (int lvl = 0; lvl < DD && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int u = queue[head++];
            const int *nb = adj + (size_t)u * dd;
            for (int t = 0; t < dd; t++) {
                int v = nb[t];
                if (mark[v] != stamp) {
                    mark[v] = stamp;
                    queue[tail++] = v;
                }
            }
        }
    }
    return tail;
}

static long eval_cost(void) {
    long c = 0;
    for (int i = 0; i < KB; i++)
        for (int L1 = 0; L1 < dd; L1++)
            for (int L2 = L1 + 1; L2 < dd; L2++)
                if (perm[L1 * KB + i] == perm[L2 * KB + i] &&
                    volt[L1 * KB + i] == volt[L2 * KB + i])
                    c += DUP_PEN;
    for (int L = 0; L < dd; L++) {
        for (int i = 0; i < KB; i++) {
            int j = perm[L * KB + i], s = volt[L * KB + i];
            for (int g = 0; g < GG; g++) {
                int a = i * GG + g;
                int b = (KB + j) * GG + mt[g * GG + s];
                adj[(size_t)a * dd + L] = b;
                adj[(size_t)b * dd + L] = a;
            }
        }
    }
    for (int i = 0; i < KB; i++) {
        c += NN - bfs(i * GG);
        c += NN - bfs((KB + i) * GG);
    }
    return c;
}

static void save_best(void) {
    if (NN <= bestN) return;
    free(best_adj);
    best_adj = malloc(sizeof(int) * (size_t)NN * dd);
    memcpy(best_adj, adj, sizeof(int) * (size_t)NN * dd);
    bestN = NN;
    bestK = KB;
    bestG = GG;
}

static int anneal(long iters, double T0, double T1) {
    long cur = eval_cost();
    if (cur == 0) {
        save_best();
        return 1;
    }
    for (long it = 0; it < iters; it++) {
        if (elapsed() > tend) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int type, idx = 0, old = 0, L = 0, i1 = 0, i2 = 0;
        if (KB == 1 || rnd01() < 0.6) {
            type = 0;
            idx = rndi(dd * KB);
            old = volt[idx];
            int nw = rndi(GG);
            if (nw == old) continue;
            volt[idx] = nw;
        } else {
            type = 1;
            L = rndi(dd);
            i1 = rndi(KB);
            i2 = rndi(KB);
            if (i1 == i2) continue;
            int a = L * KB + i1, b = L * KB + i2;
            int t = perm[a];
            perm[a] = perm[b];
            perm[b] = t;
        }
        long c2 = eval_cost();
        long delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = c2;
            if (cur == 0) {
                save_best();
                return 1;
            }
        } else {
            if (type == 0) {
                volt[idx] = old;
            } else {
                int a = L * KB + i1, b = L * KB + i2;
                int t = perm[a];
                perm[a] = perm[b];
                perm[b] = t;
            }
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    rs ^= (sd + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    long target = atol(argv[5]);
    int ch;
    while ((ch = getchar()) != EOF) {
    }
    if (dd < 2 || DD < 2) {
        printf("0 0\n");
        return 0;
    }
    double t0 = elapsed();
    tend = t0 + budget;
    static const int KOPT[] = {1, 2, 2, 3, 3, 4, 4, 5, 6};
    const int NK = 9;

    while (elapsed() < tend) {
        int K = KOPT[rndi(NK)];
        long Gmin = (target + 2L * K - 1) / (2L * K);
        if (Gmin < 2) Gmin = 2;
        long extra = Gmin / 30 + 1;
        long G = Gmin + rndi((int)extra);
        if (G > MAXG) continue;
        int Gi = (int)G;

        int divs[MAXG];
        int nd = 0;
        for (int x = 1; x <= Gi; x++)
            if (Gi % x == 0) divs[nd++] = x;
        int k2 = divs[rndi(nd)];
        int m = Gi / k2;
        long r = 0;
        if (k2 > 1 && m >= 2) {
            int okr = 0;
            for (int tr = 0; tr < 200 && !okr; tr++) {
                long cand = 1 + rndi(m - 1);
                if (lgcd(cand, m) != 1) continue;
                if (powmod(cand, k2, m) != 1 % m) continue;
                r = cand;
                okr = 1;
            }
            if (!okr) {
                k2 = 1;
                m = Gi;
                r = 0;
            }
        }

        KB = K;
        GG = Gi;
        NN = 2 * KB * GG;
        free(mt);
        free(perm);
        free(volt);
        free(adj);
        free(mark);
        free(queue);
        mt = malloc(sizeof(int) * (size_t)GG * GG);
        setup_group(GG, k2, m, r);
        perm = malloc(sizeof(int) * (size_t)dd * KB);
        volt = malloc(sizeof(int) * (size_t)dd * KB);
        adj = malloc(sizeof(int) * (size_t)NN * dd);
        mark = calloc((size_t)NN, sizeof(int));
        queue = malloc(sizeof(int) * (size_t)NN);
        for (int L = 0; L < dd; L++) {
            for (int i = 0; i < KB; i++) perm[L * KB + i] = i;
            for (int i = KB - 1; i > 0; i--) {
                int j = rndi(i + 1);
                int t = perm[L * KB + i];
                perm[L * KB + i] = perm[L * KB + j];
                perm[L * KB + j] = t;
            }
            for (int i = 0; i < KB; i++) volt[L * KB + i] = rndi(GG);
        }

        int ok = anneal(ITERS, 3.0, 0.08);
        if (ok && bestN + 1 > target) target = bestN + 1;
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    int NA = bestK * bestG;
    long M = (long)NA * dd;
    printf("%d %ld\n", bestN, M);
    for (int a = 0; a < NA; a++)
        for (int t = 0; t < dd; t++)
            printf("%d %d\n", a, best_adj[(size_t)a * dd + t]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), from the parent.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, nbr):
    """True if every target t is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements x so that every target is hit by <= s chosen elements."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4), from the parent.
# ----------------------------------------------------------------------------

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
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    end = t_start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    rng = random.Random(seed * 7919 + d)

    # Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        for n_c, e_c in _arc_extensions(d, end, rng):
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # New bold path: C bi-Cayley voltage-lift annealing with ratcheting target.
    bound = lib.moore_bound(d, D)
    if best_n < bound:
        remaining = end - time.monotonic() - 1.0
        if remaining > 2.0:
            try:
                timeout = max(1.0, time_limit * 0.95 - (time.monotonic() - t_start))
                out = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), best_n + 1],
                                stdin_graph=None, timeout=timeout)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
