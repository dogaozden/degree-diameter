import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: annealed voltage lifts over semidirect products Z_m x| Z_k2.
#
# Base: K A-vertices and K B-vertices, gd layers of permutations, so every
# vertex has degree exactly gd. Dart (i, j, s) joins A_{i,g} to B_{j,g*s}.
# Left multiplication is an automorphism, so the diameter is <= D iff a BFS
# of depth D from each of the 2K representatives reaches every vertex.
# Input args: d D seed budget_seconds. Output: "n m" plus edges (or "0 0").
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int gd = 3, gD = 3;
static int K = 1, G = 1, NV = 2;
static int *MT = NULL;
static int *DJ = NULL, *DS = NULL;
static int *ADJ = NULL, *DEG = NULL, *VIS = NULL, *QU = NULL;
static int stamp = 0;
static int best_n = 0, best_m = 0;
static int *best_u = NULL, *best_v = NULL;
static clock_t deadline;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int powmod(int r, int e, int m) {
    long long x = 1 % m, b = r % m;
    while (e > 0) {
        if (e & 1) x = x * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return (int)x;
}

static void build_group(int k2, int m, int r) {
    G = m * k2;
    free(MT);
    MT = malloc(sizeof(int) * (size_t)G * (size_t)G);
    int *pw = malloc(sizeof(int) * (size_t)k2);
    for (int b = 0; b < k2; b++) pw[b] = powmod(r, b, m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            int A = (int)(((long long)a + (long long)pw[b] * c) % m);
            int B = (b + e) % k2;
            MT[x * G + y] = A * k2 + B;
        }
    }
    free(pw);
}

static void choose_group(int Gt) {
    int divs[512];
    int nd = 0;
    for (int k2 = 1; k2 <= Gt && nd < 512; k2++)
        if (Gt % k2 == 0) divs[nd++] = k2;
    int k2 = divs[rndi(nd)];
    int m = Gt / k2;
    int r = 1;
    if (m == 1) {
        r = 0;
    } else if (k2 >= 2) {
        int found = 0;
        for (int tries = 0; tries < 300 && !found; tries++) {
            int cand = 1 + rndi(m - 1);
            if (gcd_i(cand, m) == 1 && powmod(cand, k2, m) == 1 % m) {
                r = cand;
                found = 1;
            }
        }
        if (!found) r = 1;
    }
    build_group(k2, m, r);
}

static int eval_cost(void) {
    int nd = K * gd;
    int N = NV;
    memset(DEG, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < nd; t++) {
        int i = t % K, j = DJ[t], s = DS[t];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (K + j) * G + MT[g * G + s];
            if (DEG[a] >= gd || DEG[b] >= gd) return N * N;
            ADJ[a * gd + DEG[a]++] = b;
            ADJ[b * gd + DEG[b]++] = a;
        }
    }
    int total = 0;
    for (int rr = 0; rr < 2 * K; rr++) {
        int src = rr * G;
        stamp++;
        if (stamp > 2000000000) {
            memset(VIS, 0, sizeof(int) * (size_t)N);
            stamp = 1;
        }
        int head = 0, tail = 0;
        VIS[src] = stamp;
        QU[tail++] = src;
        for (int lev = 0; lev < gD && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = QU[head++];
                const int *au = ADJ + (size_t)u * gd;
                for (int e = 0; e < gd; e++) {
                    int v = au[e];
                    if (VIS[v] != stamp) {
                        VIS[v] = stamp;
                        QU[tail++] = v;
                    }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static int anneal(int iters, double T0) {
    int nd = K * gd;
    int cost = eval_cost();
    for (int t = 0; t < iters && cost > 0; t++) {
        if ((t & 511) == 0 && clock() > deadline) break;
        double T = T0 * (1.0 - (double)t / (double)iters) + 0.05;
        if (rndi(10) < 7) {
            int idx = rndi(nd);
            int old = DS[idx];
            int nw = rndi(G);
            if (nw == old) continue;
            DS[idx] = nw;
            int c2 = eval_cost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else DS[idx] = old;
        } else {
            int l = rndi(gd);
            int i1 = rndi(K), i2 = rndi(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp;
            int c2 = eval_cost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else { tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp; }
        }
    }
    return cost;
}

static int cmp_ll(const void *a, const void *b) {
    long long x = *(const long long *)a, y = *(const long long *)b;
    return (x > y) - (x < y);
}

static void snapshot(void) {
    int nd = K * gd;
    int E = nd * G;
    long long *codes = malloc(sizeof(long long) * (size_t)E);
    int c = 0;
    for (int t = 0; t < nd; t++) {
        int i = t % K, j = DJ[t], s = DS[t];
        for (int g = 0; g < G; g++) {
            long long a = (long long)(i * G + g);
            long long b = (long long)((K + j) * G + MT[g * G + s]);
            long long lo = a < b ? a : b, hi = a < b ? b : a;
            codes[c++] = lo * (long long)NV + hi;
        }
    }
    qsort(codes, (size_t)E, sizeof(long long), cmp_ll);
    long long *uq = malloc(sizeof(long long) * (size_t)E);
    int m = 0;
    for (int x = 0; x < E; x++)
        if (x == 0 || codes[x] != codes[x - 1]) uq[m++] = codes[x];
    free(best_u); free(best_v);
    best_u = malloc(sizeof(int) * (size_t)m);
    best_v = malloc(sizeof(int) * (size_t)m);
    for (int x = 0; x < m; x++) {
        best_u[x] = (int)(uq[x] / NV);
        best_v[x] = (int)(uq[x] % NV);
    }
    best_m = m;
    best_n = NV;
    free(uq);
    free(codes);
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    gd = atoi(argv[1]);
    gD = atoi(argv[2]);
    int seed = atoi(argv[3]);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 16; i++) rnd64();
    if (gd < 2 || gD < 2) { printf("0 0\n"); return 0; }
    deadline = clock() + (clock_t)(budget * CLOCKS_PER_SEC);
    const int iters = 100000;
    const int Ks[6] = {1, 1, 1, 2, 2, 3};
    while (clock() < deadline) {
        K = Ks[rndi(6)];
        int Gmin = best_n / (2 * K) + 1;
        if (Gmin < 2) Gmin = 2;
        int spread = Gmin / 8 + 3;
        int Gt = Gmin + rndi(spread);
        if (Gt > 2500) break;
        choose_group(Gt);
        NV = 2 * K * G;
        ADJ = malloc(sizeof(int) * (size_t)NV * gd);
        DEG = malloc(sizeof(int) * (size_t)NV);
        VIS = calloc((size_t)NV, sizeof(int));
        QU = malloc(sizeof(int) * (size_t)NV);
        DJ = malloc(sizeof(int) * (size_t)K * gd);
        DS = malloc(sizeof(int) * (size_t)K * gd);
        for (int l = 0; l < gd; l++) {
            int p[8];
            for (int i = 0; i < K; i++) p[i] = i;
            for (int i = K - 1; i > 0; i--) {
                int j = rndi(i + 1);
                int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
            }
            for (int i = 0; i < K; i++) {
                DJ[l * K + i] = p[i];
                DS[l * K + i] = rndi(G);
            }
        }
        int c = anneal(iters, 1.5);
        if (c == 0 && NV > best_n) snapshot();
        free(ADJ); free(DEG); free(VIS); free(QU); free(DJ); free(DS);
        ADJ = NULL; DEG = NULL; VIS = NULL; QU = NULL; DJ = NULL; DS = NULL;
    }
    if (best_n == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int x = 0; x < best_m; x++) printf("%d %d\n", best_u[x], best_v[x]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe constructive baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _best_araujo(d):
    """Araujo-Pardo and Lopez graph for q = d - 2 when q is a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
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
# Python fallback search, used only if the C engine fails to run.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _search(d, D, k, G, rng, iters, deadline):
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    G = order
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = []
    for p in layers:
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    best_cost = cost
    best_darts = [list(x) for x in darts]
    best_perms = list(perms)

    T0 = 3.0
    for t in range(iters):
        if best_cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - t / iters) + 0.05
        idx = rng.randrange(len(darts))
        old_s = darts[idx][2]
        old_perm = perms[idx]
        new_s = rng.randrange(G)
        darts[idx][2] = new_s
        perms[idx] = _right_perm(mul, G, new_s)
        c2 = _cost(k, G, D, darts, perms)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost < best_cost:
                best_cost = cost
                best_darts = [list(x) for x in darts]
                best_perms = list(perms)
        else:
            darts[idx][2] = old_s
            perms[idx] = old_perm

    if best_cost == 0:
        return _edges(k, G, best_darts, best_perms)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        for make in (lambda: _best_pg(d), lambda: _best_araujo(d)):
            try:
                g = make()
            except Exception:
                g = None
            if g is not None:
                consider(g[0], g[1])
    if D >= 4:
        try:
            gq = _best_gq(d)
        except Exception:
            gq = None
        if gq is not None:
            consider(gq[0], gq[1])

    # Calibration cases already at the Moore bound return immediately.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Main search: the C engine, given most of the time budget.
    c_ok = False
    budget = max(1.0, 0.8 * time_limit - 3.0)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)], timeout=0.92 * time_limit)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
        c_ok = True
    except (RuntimeError, ValueError):
        c_ok = False

    # If the C engine failed, use the Python annealing search instead.
    if not c_ok:
        deadline = start + 0.75 * time_limit
        while time.monotonic() < deadline:
            k = rng.choice([1, 1, 1, 2, 2, 3])
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 6 + 1)))
            res = _search(d, D, k, G, rng, 1500, deadline)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
