import itertools
import math
import random
import re
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: simulated annealing over the voltages of a bi-Cayley lift
# over the metacyclic group Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b).
#
# Base graph: K vertices per side, DEG layers. Each layer is a permutation of
# 0..K-1, so every vertex has degree DEG. Dart e = l*K + i joins A_i to
# B_{dJ[e]} with voltage dS[e]: A_{i,g} ~ B_{j,g*s} for all g.
# Left multiplication is an automorphism, so BFS from the 2K representatives
# decides the diameter exactly.
#
# Moves: change one voltage, or (K > 1) swap two targets inside one layer.
# Cost = unreached (rep, vertex) pairs + duplicate-dart penalty.
#
# Usage: prog d D K m k2 r seed slice_seconds
# Success: prints "n m" and the edges. Failure: prints "0 0" then "# cost c".
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
#define RL 50000
#define STAG 9000

static int DEG, DIAM, K, MM, K2, G, N, NE;
static int *POWR;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx, *bestS, *bestJ, *pbuf;
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

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, d = y % K2;
    long long t = ((long long)a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + d) % K2);
}

static void set_perm(int e) {
    int s = dS[e];
    int *pm = perm + (size_t)e * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
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
    if (argc < 9) {
        fprintf(stderr, "usage: prog d D K m k2 r seed slice\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    MM = atoi(argv[4]);
    K2 = atoi(argv[5]);
    int r = atoi(argv[6]);
    uint64_t seed = strtoull(argv[7], NULL, 10);
    double slice = atof(argv[8]);

    if (DEG < 1 || DIAM < 1 || K < 1 || MM < 1 || K2 < 1 || K2 > 4096 || MM * K2 > 20000) {
        printf("0 0\n# cost %d\n", BIGCOST);
        return 0;
    }
    if (r < 1) r = 1;
    {
        int a = r, b = MM, t;
        while (b) { t = a % b; a = b; b = t; }
        if (a != 1) { printf("0 0\n# cost %d\n", BIGCOST); return 0; }
    }
    POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n# cost %d\n", BIGCOST); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) {
        printf("0 0\n# cost %d\n", BIGCOST);
        return 0;
    }

    G = MM * K2;
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
    pbuf = malloc(sizeof(int) * K);
    if (!dI || !dJ || !dS || !bestS || !bestJ || !perm || !adj || !cnt || !fr || !nx || !vis || !pbuf) {
        printf("0 0\n# cost %d\n", BIGCOST);
        return 0;
    }

    clock_t t0 = clock();
    int found = 0;
    int bestCost = BIGCOST;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestCost >= BIGCOST || rnd01() < 0.3) {
            for (int l = 0; l < DEG; l++) {
                for (int i = 0; i < K; i++) pbuf[i] = i;
                for (int i = K - 1; i > 0; i--) {
                    int j = rndint(i + 1);
                    int t = pbuf[i]; pbuf[i] = pbuf[j]; pbuf[j] = t;
                }
                for (int i = 0; i < K; i++) {
                    dI[l * K + i] = i;
                    dJ[l * K + i] = pbuf[i];
                }
            }
            for (int e = 0; e < NE; e++) dS[e] = rndint(G);
            for (int e = 0; e < NE; e++) set_perm(e);
            T0 = 2.0;
        } else {
            memcpy(dJ, bestJ, sizeof(int) * (size_t)NE);
            memcpy(dS, bestS, sizeof(int) * (size_t)NE);
            int kick = NE / 6 + 1;
            for (int q = 0; q < kick; q++) dS[rndint(NE)] = rndint(G);
            for (int e = 0; e < NE; e++) set_perm(e);
            T0 = 0.9;
        }

        int cur = cost_fn();
        if (cur < bestCost) { bestCost = cur; save_best(); }
        if (cur == 0) { found = 1; break; }

        int runBest = cur;
        int since = 0;
        for (int it = 0; it < RL; it++) {
            if ((it & 127) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.03;
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
        printf("0 0\n# cost %d\n", bestCost);
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact / safe constructions (kept as fallbacks).
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
# Metacyclic group options for the race.
# ----------------------------------------------------------------------------

_R_CACHE = {}


def _r_options(m, k2):
    """All r in [2, m) with gcd(r, m) = 1 and r^k2 = 1 mod m (cached)."""
    key = (m, k2)
    if key not in _R_CACHE:
        _R_CACHE[key] = [c for c in range(2, m)
                         if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
    return _R_CACHE[key]


def _divisors(n):
    ds = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            ds.append(i)
            if i * i != n:
                ds.append(n // i)
        i += 1
    return ds


def _group_options(G, rng, max_r=2):
    """Pairs (m, k2, r) with m * k2 = G: direct products plus a few semidirect twists."""
    opts = []
    for k2 in _divisors(G):
        m = G // k2
        if m < 2 or k2 > 4096:
            continue
        rs = [1]
        if k2 > 1:
            cands = list(_r_options(m, k2))
            if cands:
                rng.shuffle(cands)
                rs += cands[:max_r]
        for r in rs:
            opts.append((m, k2, r))
    return opts


def _candidates(aims, rng, count):
    """Bi-Cayley configurations (K, m, k2, r) whose vertex count 2*K*G reaches each aim."""
    pool = []
    for aim in aims:
        for K in (1, 2, 3, 4):
            Glo = -(-aim // (2 * K))
            span = max(3, Glo // 12)
            for G in range(max(2, Glo), max(2, Glo) + span):
                for (m, k2, r) in _group_options(G, rng):
                    pool.append((K, m, k2, r))
    rng.shuffle(pool)
    pool.sort(key=lambda c: c[0] > 2)  # prefer K = 1 and 2 (closest to known records)
    seen, out = set(), []
    for c in pool:
        if c not in seen:
            seen.add(c)
            out.append(c)
        if len(out) >= count:
            break
    return out


def _run_cfg(d, D, cfg, slice_s, seed):
    """Run one C anneal. Returns ("ok", (n, edges)) or ("cost", best_cost)."""
    K, m, k2, r = cfg
    out = lib.run_c(C_SOURCE, [d, D, K, m, k2, r, seed, f"{slice_s:.2f}"],
                    timeout=slice_s + 8.0)
    nums = out.split()
    if len(nums) >= 2 and int(nums[0]) > 0 and int(nums[1]) > 0:
        return "ok", lib.parse_graph_text(out)
    mt = re.search(r"cost\s+(\d+)", out)
    return "cost", (int(mt.group(1)) if mt else 1 << 30)


def _race(d, D, cands, deadline, rng, best_n):
    """Successive halving over candidate configurations. Returns a valid (n, edges) with n > best_n, or None."""
    live = list(cands)
    slice_s = 1.5
    while live:
        res = []
        for cfg in live:
            left = deadline - time.monotonic()
            s = min(slice_s, left - 0.3)
            if s < 0.5:
                break
            try:
                kind, val = _run_cfg(d, D, cfg, s, rng.randrange(1, 10 ** 9))
            except (RuntimeError, ValueError):
                return None
            if kind == "ok":
                n, e = val
                if n > best_n and lib.is_valid(n, e, d, D):
                    return n, e
                continue
            res.append((val, cfg))
        if not res:
            break
        res.sort(key=lambda t: t[0])
        live = [c for _, c in res[:max(2, len(res) // 2)]]
        slice_s *= 1.8
        if deadline - time.monotonic() < 0.8:
            break
    return None


# ----------------------------------------------------------------------------
# Greedy spare-degree extension (no-op for regular graphs).
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
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
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

    # Main search: racing over metacyclic bi-Cayley lifts, with growing targets.
    if d >= 3 and D >= 3:
        try:
            while time.monotonic() < deadline - 2.0:
                bn = best[0]
                cands = _candidates([bn + 2, int(bn * 1.1) + 2], rng, 12)
                if not cands:
                    break
                got = _race(d, D, cands, deadline - 1.0, rng, bn)
                if got is None:
                    break
                n, e = got
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Spare-degree extension on the best graph.
    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, deadline)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
