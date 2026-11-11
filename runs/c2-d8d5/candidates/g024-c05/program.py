"""Bold change: C-side bi-Cayley lift annealer over many base sizes and semidirect groups.

Each candidate is Z_m x| Z_s with a random base size k. Layers are permutation matchings
between A-blocks and B-blocks with group voltages. Within each block the group acts regularly,
so diameter is checked from the 2k block representatives. Exact constructions and a Python
bi-Cayley fallback remain as safety nets.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact and small constructions (calibration cases return immediately).
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
# Python bi-Cayley fallback (used only if the C engine fails).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b set when representative block b is within distance D."""
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(k, N, reach):
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing with stagnation exit. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))
    best_cost = cost
    last_improve = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last_improve > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last_improve = cost, t
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
            if cost < best_cost:
                best_cost, last_improve = cost, t
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


def _bicayley_phase(best, d, D, rng, deadline, consider_fn):
    """Python fallback: bandit over base sizes; each trial tries to beat the current best order."""
    ks = (1, 2, 3, 4)
    trials = {k: 0 for k in ks}
    wins = {k: 0 for k in ks}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(ks)
        return max(ks, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        best_n = best[0]
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            new = consider_fn(res[0], res[1])
            if new is not None:
                best = new
    return best


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lifts over semidirect groups, annealed on block-representative
# reach bitsets. Base sizes k in {1..12}; all groups Z_m x| Z_s of order N.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bipartite degree-diameter search: bi-Cayley lifts over Z_m x|_r Z_s.
 * Usage:  prog DEG DIA seed time_limit   (stdin is ignored)
 * stdout: "n m" + edge lines for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 4096
#define MAXN 4096
#define MAXD 16
#define MAXK 16
#define MAXDIV 512
#define BITW (MAXV / 64)
#define PEN 40
#define MAXIT 30000

static int DEG, DIA;
static double t_end;
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
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static long powmodl(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Group Z_GM x|_r Z_GS with element a*GS + b and (a,b)(c,e) = (a + r^b c, b + e). */
static int GM, GS, NN;
static int rp[MAXN];

static int gmul(int x, int y) {
    int a = x / GS, b = x % GS, c = y / GS, e = y % GS;
    long t = ((long)a + (long)rp[b] * c) % GM;
    return (int)(t * GS + (b + e) % GS);
}

static int ginv(int x) {
    int a = x / GS, b = x % GS;
    int nb = (GS - b) % GS;
    long t = (long)rp[nb] * a % GM;
    long c = (GM - t) % GM;
    return (int)(c * GS + nb);
}

static void choose_group(int N) {
    int divs[MAXDIV], nd = 0;
    for (int s = 1; s <= N && nd < MAXDIV; s++)
        if (N % s == 0) divs[nd++] = s;
    int s = divs[rndint(nd)];
    int m = N / s;
    int r = 1;
    if (m > 1 && s > 1 && rnd01() < 0.8) {
        for (int t = 0; t < 200; t++) {
            int cand = 1 + rndint(m - 1);
            if (gcdl(cand, m) == 1 && powmodl(cand, s, m) == 1 % m) { r = cand; break; }
        }
    }
    GM = m;
    GS = s;
    NN = N;
    rp[0] = 1 % m;
    for (int b = 1; b < s; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
}

/* Configuration: K base vertices per side, DEG layers. A block i (vertex i*NN+g) joins
 * B block LAY[l][i] (vertex (K+j)*NN+h) with h = g*VOL[l][i]. */
static int K;
static int LAY[MAXD][MAXK], LINV[MAXD][MAXK], VOL[MAXD][MAXK], VINV[MAXD][MAXK];
static int nbr[MAXD][MAXV];
static uint64_t RA[MAXV], RB[MAXV];
static int backup[MAXV];

static void rebuild_layer(int l) {
    int N = NN;
    for (int i = 0; i < K; i++) {
        int j = LAY[l][i], s = VOL[l][i];
        for (int g = 0; g < N; g++)
            nbr[l][i * N + g] = (K + j) * N + gmul(g, s);
    }
    for (int j = 0; j < K; j++) {
        int i = LINV[l][j], si = VINV[l][i];
        for (int h = 0; h < N; h++)
            nbr[l][(K + j) * N + h] = i * N + gmul(h, si);
    }
}

static void random_config(void) {
    for (int l = 0; l < DEG; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            LAY[l][i] = perm[i];
            LINV[l][perm[i]] = i;
        }
        for (int i = 0; i < K; i++) {
            VOL[l][i] = rndint(NN);
            VINV[l][i] = ginv(VOL[l][i]);
        }
        rebuild_layer(l);
    }
}

static void swap_lay(int l, int i1, int i2) {
    int j1 = LAY[l][i1], j2 = LAY[l][i2];
    LAY[l][i1] = j2;
    LAY[l][i2] = j1;
    LINV[l][j2] = i1;
    LINV[l][j1] = i2;
}

/* Duplicate edges: two layers with the same base pair (i, j) and the same voltage. */
static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int a = 0; a < DEG; a++)
            for (int b = a + 1; b < DEG; b++)
                if (LAY[a][i] == LAY[b][i] && VOL[a][i] == VOL[b][i]) c++;
    return c;
}

/* Cost = number of (block representative, vertex) pairs at distance > DIA, plus penalties. */
static long evaluate(void) {
    int N = NN, Nt = 2 * K * N;
    uint64_t *cur = RA, *nxt = RB;
    for (int v = 0; v < Nt; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[b * N] = 1ULL << b;
    for (int r = 0; r < DIA; r++) {
        int changed = 0;
        for (int v = 0; v < Nt; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < DEG; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long miss = 0;
    int full = 2 * K;
    for (int v = 0; v < Nt; v++) miss += full - __builtin_popcountll(cur[v]);
    return miss + PEN * dup_count();
}

static long anneal(long maxit, double deadline) {
    int Nt = 2 * K * NN;
    long cost = evaluate();
    const double T0 = 3.0, T1 = 0.05;
    for (long it = 0; it < maxit && cost > 0; it++) {
        if ((it & 127) == 0 && now() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)maxit);
        int l = rndint(DEG);
        int i = rndint(K);
        int type = (K >= 2 && rnd01() < 0.5) ? 1 : 0;
        int i2 = -1, nv = 0, oldv = 0, oldvinv = 0;
        if (type == 1) {
            i2 = rndint(K);
            if (i2 == i) continue;
        } else {
            nv = rndint(NN);
            if (nv == VOL[l][i]) continue;
            oldv = VOL[l][i];
            oldvinv = VINV[l][i];
        }
        memcpy(backup, nbr[l], sizeof(int) * (size_t)Nt);
        if (type == 1) {
            swap_lay(l, i, i2);
        } else {
            VOL[l][i] = nv;
            VINV[l][i] = ginv(nv);
        }
        rebuild_layer(l);
        long nc = evaluate();
        long delta = nc - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cost = nc;
        } else {
            if (type == 1) swap_lay(l, i, i2);
            else {
                VOL[l][i] = oldv;
                VINV[l][i] = oldvinv;
            }
            memcpy(nbr[l], backup, sizeof(int) * (size_t)Nt);
        }
    }
    return cost;
}

static uint64_t BA[MAXV * BITW], BB[MAXV * BITW];

/* Exact check of the current lift: simple, DEG-regular, diameter <= DIA. */
static int full_check(int Nt) {
    int W = (Nt + 63) / 64;
    for (int v = 0; v < Nt; v++) {
        for (int a = 0; a < DEG; a++) {
            int u = nbr[a][v];
            if (u < 0 || u >= Nt || u == v) return 0;
            for (int b = 0; b < a; b++)
                if (nbr[b][v] == u) return 0;
        }
    }
    uint64_t *cur = BA, *nxt = BB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)Nt * W);
    for (int v = 0; v < Nt; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < DIA; r++) {
        for (int v = 0; v < Nt; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int a = 0; a < DEG; a++) {
                const uint64_t *s2 = cur + (size_t)nbr[a][v] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    for (int v = 0; v < Nt; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        if (c != Nt) return 0;
    }
    return 1;
}

static int best_n = 0, bestK = 0, bestN = 0;
static int bestnbr[MAXD][MAXV];

static void save_best(void) {
    int Nt = 2 * K * NN;
    for (int l = 0; l < DEG; l++) memcpy(bestnbr[l], nbr[l], sizeof(int) * (size_t)Nt);
    bestK = K;
    bestN = NN;
    best_n = Nt;
}

static void print_best(void) {
    if (best_n == 0) { printf("0 0\n"); return; }
    int A = bestK * bestN;
    printf("%d %d\n", best_n, A * DEG);
    for (int v = 0; v < A; v++)
        for (int l = 0; l < DEG; l++)
            printf("%d %d\n", v, bestnbr[l][v]);
}

static long moore_bound(void) {
    if (DIA <= 0 || DEG <= 0) return 1;
    if (DEG == 1) return 2;
    if (DEG == 2) return 2L * DIA;
    long s = 0, p = 1;
    for (int i = 0; i < DIA; i++) {
        s += p;
        p *= (DEG - 1);
        if (s > 1000000000L) break;
    }
    return 2 * s;
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    DEG = atoi(argv[1]);
    DIA = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (DEG < 2 || DIA < 2 || DEG > MAXD) { printf("0 0\n"); return 0; }

    long moore = moore_bound();
    static const int KS[] = {1, 2, 3, 4, 5, 6, 8, 10, 12};
    int fails = 0;
    while (now() < t_end) {
        K = KS[rndint(9)];
        long lo = best_n / (2L * K) + 1;
        long hi = MAXV / (2L * K);
        if (moore / (2L * K) < hi) hi = moore / (2L * K);
        if (lo > hi) { fails++; continue; }
        long N = lo + ((fails > 30) ? 0 : rndint(4));
        if (N > hi) N = hi;
        if (N < 1) { fails++; continue; }
        NN = (int)N;
        choose_group(NN);
        random_config();
        long cost = anneal(MAXIT, t_end);
        if (cost == 0 && full_check(2 * K * NN)) {
            save_best();
            fails = 0;
        } else {
            fails++;
        }
    }
    print_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Return the new graph if it is a larger valid graph, else None."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return best
        return None

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if D >= 2 and d >= 2:
        c_budget = end - time.monotonic() - 0.5
        c_failed = False
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=None, timeout=c_budget + 8)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                c_failed = True
        # If the C engine could not run, use the Python bi-Cayley search with the remaining time.
        if c_failed:
            best = _bicayley_phase(best, d, D, rng, end, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
