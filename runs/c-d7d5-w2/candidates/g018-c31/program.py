import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: simulated annealing over the voltages of a bi-Cayley lift
# over an arbitrary finite group G given by its multiplication table.
#
# Input (stdin): "G M" then 2M integers, the first G*G of which form the
# row-major table MT[x*G+y] = x*y. Identity is element 0.
# Base graph: K vertices per side, DEG layers, each layer a permutation of
# 0..K-1. Dart e = l*K + i joins A_i to B_{dJ[e]} with voltage dS[e]:
# A_{i,g} ~ B_{j,g*s} for all g. Left multiplication is an automorphism, so
# BFS from the 2K representatives A_{i,e}, B_{j,e} decides the diameter.
#
# Cost: each BFS runs LMAX = DIAM+3 levels. A vertex at distance t > DIAM
# costs (t - DIAM); an unreached vertex costs (LMAX - DIAM + 2). Duplicate
# darts are penalised. The cost is zero iff the lift has diameter <= DIAM.
#
# Usage: prog d D K seed slice_seconds
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

static int DEG, DIAM, K, G, N, NE;
static int *MT;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx;
static int *bestS, *bestJ;
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
        fprintf(stderr, "usage: prog d D K seed slice\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double slice = atof(argv[5]);

    if (DEG < 1 || DIAM < 1 || K < 1) { printf("0 0\n"); return 0; }

    int gg = 0, mm = 0;
    if (scanf("%d %d", &gg, &mm) != 2 || gg < 1 || gg > 1000 || mm < 0) {
        printf("0 0\n");
        return 0;
    }
    G = gg;
    long long total = (long long)G * G;
    if (2LL * mm < total) { printf("0 0\n"); return 0; }
    MT = malloc(sizeof(int) * (size_t)total);
    if (!MT) { printf("0 0\n"); return 0; }
    for (long long i = 0; i < 2LL * mm; i++) {
        long long v = 0;
        if (scanf("%lld", &v) != 1) { printf("0 0\n"); return 0; }
        if (i < total) {
            if (v < 0 || v >= G) { printf("0 0\n"); return 0; }
            MT[i] = (int)v;
        }
    }
    for (int y = 0; y < G; y++) {
        if (MT[y] != y || MT[(size_t)y * G] != y) { printf("0 0\n"); return 0; }
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
    const int RL = 60000;

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
# Exact construction and safe fallback.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group families, each given as (order, multiplication table with identity 0).
# Families beyond metacyclic: Heisenberg groups, affine groups AGL(1,q),
# SL(2,q), and direct products with cyclic groups.
# ----------------------------------------------------------------------------

CAP = 900
K2_LIST = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21, 24, 27, 28,
           30, 36, 40, 42, 48, 49, 54, 56, 63, 72, 81]


def _table(G, mul):
    return [[mul(x, y) for y in range(G)] for x in range(G)]


def _tab_meta(m, k, r):
    """Metacyclic Z_m x|_r Z_k (k = 1 gives the cyclic group Z_m)."""
    G, mul, _ = lib.semidirect_group(m, k, r)
    return G, _table(G, mul)


def _tab_heis(p):
    """Heisenberg group of order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    G = p ** 3

    def mul(x, y):
        a1, r1 = divmod(x, p * p)
        b1, c1 = divmod(r1, p)
        a2, r2 = divmod(y, p * p)
        b2, c2 = divmod(r2, p)
        return ((a1 + a2) % p) * p * p + ((b1 + b2) % p) * p + (c1 + c2 + a1 * b2) % p

    return G, _table(G, mul)


def _tab_aff(q):
    """Affine group AGL(1,q) = {x -> a x + b}, a != 0, order q(q-1)."""
    F = lib.GF(q)
    AD = F.add_table.tolist()
    MU = F.mul_table.tolist()
    elems = [(1, 0)] + [(a, b) for a in range(1, q) for b in range(q) if (a, b) != (1, 0)]
    idx = {e: i for i, e in enumerate(elems)}

    def mul(x, y):
        a, b = elems[x]
        c, d = elems[y]
        return idx[(MU[a][c], AD[MU[a][d]][b])]

    G = len(elems)
    return G, _table(G, mul)


def _tab_sl2(q):
    """Special linear group SL(2,q), identity first."""
    F = lib.GF(q)
    AD = F.add_table.tolist()
    MU = F.mul_table.tolist()
    NEG = [next(z for z in range(q) if AD[y][z] == 0) for y in range(q)]
    mats = [(1, 0, 0, 1)]
    for a, b, c, d in itertools.product(range(q), repeat=4):
        if (a, b, c, d) == (1, 0, 0, 1):
            continue
        det = AD[MU[a][d]][NEG[MU[b][c]]]
        if det == 1:
            mats.append((a, b, c, d))
    idx = {m: i for i, m in enumerate(mats)}

    def mul(x, y):
        a, b, c, d = mats[x]
        e, f, g, h = mats[y]
        return idx[(AD[MU[a][e]][MU[b][g]], AD[MU[a][f]][MU[b][h]],
                    AD[MU[c][e]][MU[d][g]], AD[MU[c][f]][MU[d][h]])]

    G = len(mats)
    return G, _table(G, mul)


def _tab_prod(A, B):
    """Direct product of two tables; element (x1, x2) coded as x1*GB + x2."""
    GA, TA = A
    GB, TB = B
    T = []
    for x1 in range(GA):
        r1 = TA[x1]
        for x2 in range(GB):
            r2 = TB[x2]
            T.append([r1[y1] * GB + r2[y2] for y1 in range(GA) for y2 in range(GB)])
    return GA * GB, T


def _build_table(spec):
    kind = spec[0]
    if kind == "heis":
        return _tab_heis(spec[1])
    if kind == "aff":
        return _tab_aff(spec[1])
    if kind == "sl2":
        return _tab_sl2(spec[1])
    if kind == "meta":
        return _tab_meta(spec[1], spec[2], spec[3])
    if kind == "cyc":
        return _tab_meta(spec[1], 1, 1)
    if kind == "prod":
        return _tab_prod(_build_table(spec[1]), _build_table(spec[2]))
    raise ValueError(kind)


def _pick_spec(target, rng):
    """Choose a group spec whose order lies in [target, CAP], preferring orders near target."""
    out = []
    for p in (3, 5, 7):
        out.append((p ** 3, ("heis", p)))
    for q in (16, 17, 19, 23, 25, 27, 29):
        out.append((q * (q - 1), ("aff", q)))
    for q in (5, 7, 8):
        out.append((q * (q * q - 1), ("sl2", q)))
    for k in range(2, 34):
        out.append((27 * k, ("prod", ("heis", 3), ("cyc", k))))
    for k in range(2, 8):
        out.append((125 * k, ("prod", ("heis", 5), ("cyc", k))))
    for k in range(2, 4):
        out.append((240 * k, ("prod", ("aff", 16), ("cyc", k))))
    out.append((729, ("prod", ("heis", 3), ("heis", 3))))
    out.append((672, ("prod", ("sl2", 7), ("cyc", 2))))
    for k2 in K2_LIST:
        lo = max(2, -(-target // k2))
        for m in range(lo, lo + 4):
            o = m * k2
            if o > CAP:
                break
            if k2 == 1:
                r = 1
            else:
                rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
                if not rs:
                    continue
                r = rng.choice(rs)
            out.append((o, ("meta", m, k2, r)))
    cands = [(o, s) for o, s in out if target <= o <= CAP]
    if not cands:
        return None
    near = [c for c in cands if c[0] <= 1.3 * target + 12]
    pool = near if near else sorted(cands, key=lambda c: c[0])[:8]
    return rng.choice(pool)[1]


def _pack(G, T):
    """Pack the table into the (n, edges) form that lib.run_c writes as "G M" + M pairs."""
    flat = [v for row in T for v in row]
    if len(flat) % 2:
        flat.append(0)
    return G, [(flat[i], flat[i + 1]) for i in range(0, len(flat), 2)]


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
    budget = max(1.0, min(0.88 * time_limit, time_limit - 4.5))
    deadline = start + budget
    search_deadline = start + 0.9 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
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

    # Group-lift search with adaptive growth.
    step = 0.08
    while True:
        remaining = search_deadline - time.monotonic()
        if remaining < 4.0:
            break
        slice_s = min(remaining - 3.0, 12.0)
        K = rng.choice([1, 1, 2, 2, 3, 4])
        want = best[0] * (1.0 + step)
        target = max(2, math.ceil(want / (2 * K)))
        spec = _pick_spec(target, rng)
        if spec is None:
            step = max(0.005, step * 0.7)
            continue
        try:
            G, T = _build_table(spec)
        except Exception:
            step = max(0.005, step * 0.7)
            continue
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, K, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                stdin_graph=_pack(G, T),
                timeout=slice_s + 20.0,
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
