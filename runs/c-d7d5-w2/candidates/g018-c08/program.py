import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C search engine: simulated annealing for bi-Cayley lifts over an arbitrary
# finite group given by its multiplication table (identity = element 0).
#
# Base graph: K vertices per side, DEG layers, each layer a permutation of
# 0..K-1, so every vertex has degree DEG. Dart e = l*K + i joins A_i to
# B_{dJ[e]} with voltage dS[e]: A_{i,g} ~ B_{j, g*s} for all g.
# Left multiplication is an automorphism, so BFS from the 2K representatives
# A_{i,e}, B_{j,e} decides the diameter exactly.
#
# Excess-distance cost: a vertex at distance t > DIAM costs (t - DIAM); a vertex
# not reached within LMAX levels costs (LMAX - DIAM + 2). Duplicate darts are
# penalised. The total is zero iff the lift has diameter <= DIAM.
#
# Usage: prog DEG DIAM K seed slice_seconds
# stdin: "G G*G" then G*G lines "x*G+y  x*y" (group multiplication table).
# stdout: valid graph ("n m" + edges) or "0 0".
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
#define STAG 5000
#define RL 30000

static int DEG, DIAM, K, G, N, NE;
static int *MUL;
static int *dI, *dJ, *dS, *bestS, *bestJ, *adj, *cnt, *fr, *nx, *p;
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

static int cost_fn(void) {
    int dup = 0;
    for (int e1 = 0; e1 < NE; e1++)
        for (int e2 = e1 + 1; e2 < NE; e2++)
            if (dI[e1] == dI[e2] && dJ[e1] == dJ[e2] && dS[e1] == dS[e2]) dup++;

    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < NE; e++) {
        int ba = dI[e] * G, bb = (K + dJ[e]) * G, s = dS[e];
        for (int g = 0; g < G; g++) {
            int a = ba + g, b = bb + MUL[g * G + s];
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
        printf("0 0\n");
        return 0;
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

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { printf("0 0\n"); return 0; }
    G = n0;
    if (G < 1 || G > 4000 || m0 != G * G) { printf("0 0\n"); return 0; }
    MUL = malloc(sizeof(int) * (size_t)m0);
    if (!MUL) { printf("0 0\n"); return 0; }
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || u >= m0 || v < 0 || v >= G) { printf("0 0\n"); return 0; }
        MUL[u] = v;
    }
    /* Identity must be element 0. */
    for (int y = 0; y < G; y++) {
        if (MUL[y] != y || MUL[y * G] != y) { printf("0 0\n"); return 0; }
    }

    NE = DEG * K;
    N = 2 * K * G;

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    dI = malloc(sizeof(int) * NE);
    dJ = malloc(sizeof(int) * NE);
    dS = malloc(sizeof(int) * NE);
    bestS = malloc(sizeof(int) * NE);
    bestJ = malloc(sizeof(int) * NE);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    vis = calloc((size_t)N, sizeof(uint32_t));
    p = malloc(sizeof(int) * K);
    if (!dI || !dJ || !dS || !bestS || !bestJ || !adj || !cnt || !fr || !nx || !vis || !p) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    int found = 0;
    int bestCost = BIGCOST;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestCost >= BIGCOST || rnd01() < 0.2) {
            /* Fresh random lift. */
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
            for (int e = 0; e < NE; e++) dS[e] = rndint(G);
            T0 = 1.5;
        } else {
            /* Reheat from the best state with a random kick. */
            memcpy(dJ, bestJ, sizeof(int) * (size_t)NE);
            memcpy(dS, bestS, sizeof(int) * (size_t)NE);
            int kick = NE / 6 + 1;
            for (int q = 0; q < kick; q++) dS[rndint(NE)] = rndint(G);
            T0 = 0.6;
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
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    dS[e] = old;
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
                printf("%d %d\n", dI[e] * G + g, (K + dJ[e]) * G + MUL[g * G + dS[e]]);
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
# Exact / safe constructions (unchanged from the parent).
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
# New construction family: bi-Cayley (group-lift) graphs over many groups.
#
# Groups are given by multiplication tables with identity = element 0:
#   ("sd", m, k, r): Z_m x|_r Z_k, element (a, b) coded as a*k + b,
#                    (a,b)(c,d) = (a + r^b c, b + d).
#   ("af", q, t):    F_q x| H, H the order-t subgroup of F_q^*,
#                    (a,h)(b,k) = (a + h b, h k). Non-metacyclic in general.
# The search anneals the voltages over the group, with K base vertices per side.
# The lift has 2*K*|G| vertices and is d-regular, so a success beats the record
# order whenever 2*K*|G| exceeds the current best.
# ----------------------------------------------------------------------------

SLICE = 3.0
_GF_CACHE = {}


def _gf(q):
    if q not in _GF_CACHE:
        _GF_CACHE[q] = lib.GF(q)
    return _GF_CACHE[q]


def _groups_in_window(lo, hi):
    """Candidate group descriptions with order in [lo, hi]."""
    out = []
    for m in range(2, hi + 1):
        for k in range(1, hi // m + 1):
            n = m * k
            if n < lo or n > hi:
                continue
            if k == 1:
                out.append(("sd", m, 1, 1))
                continue
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    out.append(("sd", m, k, r))
    for q in range(2, hi + 1):
        if not lib.is_prime_power(q):
            continue
        for t in range(2, q):
            if (q - 1) % t:
                continue
            n = q * t
            if lo <= n <= hi:
                out.append(("af", q, t))
    return out


def _group_table(c):
    """Return (order, table) with table[x*N + y] = x*y, identity 0."""
    if c[0] == "sd":
        _, m, k, r = c
        pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
        N = m * k
        codes = np.arange(N, dtype=np.int64)
        A = codes // k
        B = codes % k
        ra = (A[:, None] + pw[B][:, None] * A[None, :]) % m
        rb = (B[:, None] + B[None, :]) % k
        return N, ra * k + rb
    _, q, t = c
    F = _gf(q)
    g = F.primitive_element()
    step = (q - 1) // t
    H = [F.pow(g, step * i) for i in range(t)]
    Hv = np.array(H, dtype=np.int64)
    pos = np.full(q, -1, dtype=np.int64)
    pos[Hv] = np.arange(t, dtype=np.int64)
    N = q * t
    codes = np.arange(N, dtype=np.int64)
    a = codes // t
    hv = Hv[codes % t]
    hb = F.mul_table[hv[:, None], a[None, :]]        # h_x * a_y
    ares = F.add_table[a[:, None], hb]               # a_x + h_x a_y
    hres = pos[F.mul_table[hv[:, None], hv[None, :]]]
    return N, ares * t + hres


def _pairs(N, table):
    return list(zip(range(N * N), table.ravel().tolist()))


def _search(d, D, state, rng, deadline):
    """Adaptively search group lifts larger than state[0]. state = [(n, edges)] is updated in place."""
    tried = set()
    widen = 0.15
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            return
        K = rng.choice([1, 1, 1, 2, 2, 3])
        cur_n = state[0][0]
        lo = max(d, 2, math.ceil((cur_n + 2) / (2 * K)))
        hi = int(lo * (1.0 + widen)) + 3
        cands = [c for c in _groups_in_window(lo, hi) if (c, K) not in tried]
        if not cands:
            widen = min(widen + 0.1, 3.0)
            continue
        rng.shuffle(cands)
        for c in cands:
            remaining = deadline - time.monotonic()
            if remaining < 2.0:
                return
            tried.add((c, K))
            try:
                N, table = _group_table(c)
            except Exception:
                continue
            if N < lo or N > hi or N * N > 2_000_000:
                continue
            slice_s = min(SLICE, remaining - 1.5)
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, K, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                    stdin_graph=(N, _pairs(N, table)),
                    timeout=slice_s + 5.0,
                )
            except RuntimeError:
                return
            try:
                n, e = lib.parse_graph_text(out)
            except ValueError:
                continue
            if n > state[0][0] and lib.is_valid(n, e, d, D):
                state[0] = (n, e)
                break


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 2.5))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is larger and valid."""
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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, start + 0.1 * budget)
        consider(n2, e2)
    except Exception:
        pass

    if d >= 2 and D >= 3 and time.monotonic() < deadline - 2.0:
        state = [best]
        try:
            _search(d, D, state, rng, deadline)
        except Exception:
            pass
        consider(state[0][0], state[0][1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
