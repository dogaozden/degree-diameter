import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: simulated annealing over the voltages of a bi-Cayley lift
# over a finite group G = Z_m^t x|_M Z_k (t = 1 or 2, M in GL(t, Z_m), M^k = I).
#
# The group is built inside C from its parameters, so no table is sent over
# stdin. Element (v, b) is coded as vindex*k + b, with vindex the base-m
# digits of v. Product: (v, b)(w, c) = (v + M^b w, b + c). The t = 2 case gives
# non-metacyclic groups (for example Z_m^2 x| Z_k), which the metacyclic-only
# family of the parent could not reach.
#
# Base graph: K vertices per side, DEG layers, each layer a permutation of
# 0..K-1, so every vertex has degree DEG. Dart e = l*K + i joins A_i to
# B_{dJ[e]} with voltage dS[e]: A_{i,g} ~ B_{j, g*s} for all g. Left
# multiplication is an automorphism, so BFS from the 2K identity
# representatives decides the diameter exactly.
#
# Cost: excess distance. A vertex at distance t > DIAM costs (t - DIAM).
# A vertex unreached within LMAX levels costs (LMAX - DIAM + 2). Zero iff the
# lift has diameter <= DIAM. Duplicate darts are penalised.
#
# Moves: change a voltage, or swap two targets within one layer (K > 1).
# Anneal with reheats from the best state and stagnation restarts.
#
# Usage: prog d D K t m k a b c dd seed slice
#   (M = [[a, b], [c, dd]] for t = 2; for t = 1 only a is used as r.)
# Prints a valid graph ("n m" + edges) or "0 0".
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
#define STAG 6000
#define GMAX 2100
#define RL 60000

static int DEG, DIAM, K, G, N, NE;
static int *MUL;
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

static void matmul(const int *A, const int *B, int *C, int t, int m) {
    int tmp[4];
    for (int i = 0; i < t; i++)
        for (int j = 0; j < t; j++) {
            long long s = 0;
            for (int l = 0; l < t; l++) s += (long long)A[i * t + l] * B[l * t + j];
            tmp[i * t + j] = (int)(s % m);
        }
    memcpy(C, tmp, sizeof(int) * (size_t)(t * t));
}

/* Build the multiplication table of G = Z_m^t x|_M Z_k. Returns 1 on success. */
static int build_group(int t, int m, int k, const int *Min) {
    int tt = t * t;
    long long V = 1;
    for (int i = 0; i < t; i++) V *= m;
    long long Gl = V * k;
    if (V < 1 || Gl < 1 || Gl > GMAX) return 0;
    G = (int)Gl;
    int Mm[4] = {0, 0, 0, 0};
    for (int i = 0; i < tt; i++) Mm[i] = ((Min[i] % m) + m) % m;
    int *Mp = malloc(sizeof(int) * (size_t)k * tt);
    int *VD = malloc(sizeof(int) * (size_t)V * t);
    MUL = malloc(sizeof(int) * (size_t)G * G);
    if (!Mp || !VD || !MUL) return 0;
    for (int i = 0; i < tt; i++) Mp[i] = 0;
    for (int i = 0; i < t; i++) Mp[i * t + i] = 1 % m;
    for (int b = 1; b < k; b++) matmul(Mp + (b - 1) * tt, Mm, Mp + b * tt, t, m);
    /* M^k must be the identity mod m. */
    int chk[4];
    matmul(Mp + (k - 1) * tt, Mm, chk, t, m);
    for (int i = 0; i < t; i++)
        for (int j = 0; j < t; j++)
            if (chk[i * t + j] != ((i == j) ? 1 % m : 0)) return 0;
    /* Digits of each vector index, most significant first. */
    for (long long v = 0; v < V; v++) {
        long long rem = v;
        for (int i = t - 1; i >= 0; i--) {
            VD[(size_t)v * t + i] = (int)(rem % m);
            rem /= m;
        }
    }
    for (int x = 0; x < G; x++) {
        int bx = x % k, vx = x / k;
        for (int y = 0; y < G; y++) {
            int by = y % k, vy = y / k;
            int code = 0;
            for (int i = 0; i < t; i++) {
                long long s = VD[vx * t + i];
                for (int j = 0; j < t; j++)
                    s += (long long)Mp[bx * tt + i * t + j] * VD[vy * t + j];
                code = code * m + (int)(s % m);
            }
            MUL[x * G + y] = code * k + (bx + by) % k;
        }
    }
    free(Mp);
    free(VD);
    return 1;
}

static void set_perm(int e) {
    int s = dS[e];
    int *pm = perm + (size_t)e * G;
    for (int g = 0; g < G; g++) pm[g] = MUL[g * G + s];
}

/* Excess-distance cost. Zero iff every representative reaches every vertex
   within DIAM steps (valid lift), plus a duplicate-dart penalty. */
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
        int src = ri * G;  /* identity element is code 0 */
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
    if (argc < 13) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    int t = atoi(argv[4]);
    int m = atoi(argv[5]);
    int k = atoi(argv[6]);
    int Mv[4];
    for (int i = 0; i < 4; i++) Mv[i] = atoi(argv[7 + i]);
    uint64_t seed = strtoull(argv[11], NULL, 10);
    double slice = atof(argv[12]);

    if (DEG < 1 || DIAM < 1 || K < 1 || (t != 1 && t != 2) || m < 1 || k < 1) {
        printf("0 0\n");
        return 0;
    }
    if (!build_group(t, m, k, Mv)) {
        printf("0 0\n");
        return 0;
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
    perm = malloc(sizeof(int) * (size_t)NE * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    vis = calloc((size_t)N, sizeof(uint32_t));
    pbuf = malloc(sizeof(int) * K);
    if (!dI || !dJ || !dS || !bestS || !bestJ || !perm || !adj || !cnt ||
        !fr || !nx || !vis || !pbuf) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    int found = 0;
    int bestCost = BIGCOST;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestCost >= BIGCOST || rnd01() < 0.25) {
            /* Fresh random lift. */
            for (int l = 0; l < DEG; l++) {
                for (int i = 0; i < K; i++) pbuf[i] = i;
                for (int i = K - 1; i > 0; i--) {
                    int j = rndint(i + 1);
                    int tmp = pbuf[i]; pbuf[i] = pbuf[j]; pbuf[j] = tmp;
                }
                for (int i = 0; i < K; i++) {
                    dI[l * K + i] = i;
                    dJ[l * K + i] = pbuf[i];
                }
            }
            for (int e = 0; e < NE; e++) {
                dS[e] = rndint(G);
                set_perm(e);
            }
            T0 = 2.0;
        } else {
            /* Reheat from the best state found so far, with a random kick. */
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
                int tmp = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = tmp;
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    tmp = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = tmp;
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
# Exact / safe constructions.
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
# Spare-degree extension (no-op for regular lifts).
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
# Group sampling: metacyclic Z_m x|_r Z_k and 2-dimensional Z_m^2 x|_M Z_k.
# ----------------------------------------------------------------------------

K2_CHOICES = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21, 24,
              27, 28, 30, 32, 36, 40, 42, 48, 54, 56, 63, 72, 84, 96, 108, 126, 168]


def _mat_mul2(A, B, m):
    """Product of 2x2 matrices given as flat 4-tuples, mod m."""
    a0, a1, a2, a3 = A
    b0, b1, b2, b3 = B
    return ((a0 * b0 + a1 * b2) % m, (a0 * b1 + a1 * b3) % m,
            (a2 * b0 + a3 * b2) % m, (a2 * b1 + a3 * b3) % m)


def _mat_pow_is_identity(M, m, k):
    """True if M^k is the identity mod m."""
    I = (1 % m, 0, 0, 1 % m)
    P = I
    for _ in range(k):
        P = _mat_mul2(P, M, m)
    return P == I


def _sample_group(lo, hi, rng):
    """Return (t, m, k, M) describing a group of order in [lo, hi], or None.

    t = 1: Z_m x|_r Z_k with M = (r, 0, 0, 0). t = 2: Z_m^2 x|_M Z_k with M
    a 2x2 matrix over Z_m satisfying M^k = I (non-metacyclic groups).
    The group order is m^t * k.
    """
    if lo > hi or hi < 2:
        return None
    for _ in range(300):
        k = rng.choice(K2_CHOICES)
        t = rng.choice([1, 1, 2])
        if t == 1:
            m_lo = max(2, -(-lo // k))
            m_hi = hi // k
            if m_lo > m_hi:
                continue
            m = rng.randint(m_lo, m_hi)
            cands = [r for r in range(1, m)
                     if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if not cands:
                continue
            return 1, m, k, (rng.choice(cands), 0, 0, 0)
        # t = 2: need m*m*k in [lo, hi].
        s_lo = -(-lo // k)
        s_hi = hi // k
        m_lo = max(2, math.isqrt(s_lo))
        if m_lo * m_lo < s_lo:
            m_lo += 1
        m_hi = math.isqrt(s_hi)
        if m_lo > m_hi:
            continue
        m = rng.randint(m_lo, m_hi)
        if k == 1:
            return 2, m, 1, (1, 0, 0, 1)
        M = None
        for _ in range(150):
            cand = tuple(rng.randrange(m) for _ in range(4))
            if _mat_pow_is_identity(cand, m, k):
                M = cand
                break
        if M is None:
            M = (1, 0, 0, 1)  # direct product Z_m^2 x Z_k is always valid
        return 2, m, k, M
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 5.0))
    deadline = start + budget
    search_deadline = start + 0.93 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is larger and valid. Returns True when the best improved."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

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

    # Main search: annealed bi-Cayley lifts over a wider group family.
    # `step` is the fractional growth aimed for next. Success widens it,
    # failure narrows it. A failed slice is retried once with the same
    # group and K before the step narrows.
    step = 0.25
    retry = None
    while True:
        remaining = search_deadline - time.monotonic()
        if remaining < 2.0:
            break
        slice_s = min(remaining, 14.0)
        if retry is not None:
            K, grp = retry
            retry = None
            is_retry = True
        else:
            is_retry = False
            K = rng.choice([1, 1, 1, 2, 2, 3])
            want = best[0] * (1.0 + step)
            lo = max(2, math.ceil(want / (2 * K)))
            hi = min(2000, lo + max(2, lo // 25))
            grp = _sample_group(lo, hi, rng)
            if grp is None:
                step = max(0.003, step * 0.8)
                continue
        t, m, k2, M = grp
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, K, t, m, k2, M[0], M[1], M[2], M[3],
                 rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                timeout=slice_s + 10.0,
            )
        except RuntimeError:
            break
        try:
            n, e = lib.parse_graph_text(out)
            ok = consider(n, e)
        except ValueError:
            ok = False
        if ok:
            step = min(0.5, step * 1.3)
        elif not is_retry:
            retry = (K, grp)
        else:
            step = max(0.003, step * 0.7)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Spare-degree extension with the remaining time.
    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, deadline)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
