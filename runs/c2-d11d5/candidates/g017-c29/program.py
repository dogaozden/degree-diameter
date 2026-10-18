"""Bi-Cayley voltage-lift search with the annealer in C, plus exact small constructions.

New in this version: the whole lift search (random semidirect group sampling, layered
voltage assignments, simulated annealing, and an adaptive base-size bandit) runs natively in C.
Reachability uses one uint64 bitmask per vertex over the 2k block identities. Left
multiplication is an automorphism inside each block, so this check is exact for the diameter.
Each move therefore costs O(N * d * D) native operations.

Every returned graph is checked with lib.is_valid. A numpy/Python lift search is the fallback
if the C engine fails, and K_{d,d} (or a projective-plane or Araujo-Pardo-Lopez graph) is always
kept as the base.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


C_SOURCE = r'''
/* Bi-Cayley lift annealer over Z_m x| Z_k2.
 * Usage:  prog d D seed time_limit
 * Vertices: A_{i,g} = i*G + g (i < K), B_{j,h} = (K+j)*G + h.
 * Layer l pairs A_i with B_{lay[l][i]} via voltage vol[l][i]: A_{i,g} ~ B_{p, g*s}.
 * Each layer is a permutation, so every vertex has degree d.
 * Diameter test: distance from every block identity (b,1) to every vertex <= D.
 * This is exact because left multiplication is an automorphism that moves (a,g) to (a,1).
 * stdout: "n m" + edges of the best valid lift found, or "0 0".
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 60000
#define MAXD 16
#define MAXK 4
#define PEN 2000L

static int DEG, DIA, K, G, N;
static uint64_t rs = 88172645463325252ULL;
static double t_end;

static int gm, gk2;
static long gpw[64];

static int lay[MAXD][MAXK], inv[MAXD][MAXK], vol[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static int bn[MAXD][MAXN];
static uint64_t RA[MAXN], RB[MAXN];
static uint64_t *resr = RA;
static long lastbad = 0;
static int bestN = 0, bK = 0, bG = 0, bDEG = 0;

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
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double dmax(double a, double b) { return a > b ? a : b; }

static long pw_mod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long gcdl(long a, long b) {
    while (b) {
        long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/* (a,b)(c,e) = (a + r^b c, b + e), element coded as a*k2 + b. */
static int gmul(int x, int y) {
    int a = x / gk2, b = x % gk2, c = y / gk2, e = y % gk2;
    long t = (gpw[b] * (long)c + a) % gm;
    return (int)t * gk2 + (b + e) % gk2;
}

/* Inverse of (a,b) is (-r^{-b} a, -b). */
static int ginv(int x) {
    int a = x / gk2, b = x % gk2;
    int nb = (gk2 - b) % gk2;
    long t = ((gm - gpw[nb]) % gm) * (long)a % gm;
    return (int)t * gk2 + nb;
}

static int sample_group(long target) {
    static const int K2[17] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 16, 18, 20, 24};
    int k2 = K2[rndint(17)];
    long m = (target + k2 - 1) / k2;
    if (m < 2) m = 2;
    long r = 1 % m;
    if (k2 >= 2 && m >= 3) {
        int ok = 0;
        if (k2 == 2 && rnd01() < 0.3 && pw_mod(m - 1, 2, m) == 1) {
            r = m - 1;
            ok = 1;
        }
        for (int tries = 0; !ok && tries < 300; tries++) {
            long c = 2 + rndint((int)(m - 2));
            if (gcdl(c, m) == 1 && pw_mod(c, k2, m) == 1) {
                r = c;
                ok = 1;
            }
        }
        if (!ok) return 0;
    }
    gm = (int)m;
    gk2 = k2;
    G = gm * gk2;
    long p = 1 % m;
    for (int b = 0; b < k2; b++) {
        gpw[b] = p;
        p = p * r % m;
    }
    return 1;
}

static void set_dart(int l, int i) {
    int j = lay[l][i], s = vol[l][i];
    int sinv = ginv(s);
    int bA = i * G, bB = (K + j) * G;
    for (int g = 0; g < G; g++) {
        nbr[l][bA + g] = bB + gmul(g, s);
        nbr[l][bB + g] = bA + gmul(g, sinv);
    }
}

static void swap_layer(int l, int i1, int i2) {
    int t = lay[l][i1];
    lay[l][i1] = lay[l][i2];
    lay[l][i2] = t;
    inv[l][lay[l][i1]] = i1;
    inv[l][lay[l][i2]] = i2;
    set_dart(l, i1);
    set_dart(l, i2);
}

/* Number of (block identity, vertex) pairs at distance > DIA. */
static long reach_cost(void) {
    uint64_t *cur = RA, *nxt = RB;
    int NN = N;
    for (int v = 0; v < NN; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[(long)b * G] |= 1ULL << b;
    for (int r = 0; r < DIA; r++) {
        int changed = 0;
        for (int v = 0; v < NN; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < DEG; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    resr = cur;
    long bad = 0;
    for (int v = 0; v < NN; v++) bad += 2 * K - __builtin_popcountll(cur[v]);
    return bad;
}

/* Same (i, p, s) used by two layers gives a double edge. */
static long dup_count(void) {
    long c = 0;
    for (int l = 0; l < DEG; l++)
        for (int l2 = l + 1; l2 < DEG; l2++)
            for (int i = 0; i < K; i++)
                if (lay[l][i] == lay[l2][i] && vol[l][i] == vol[l2][i]) c++;
    return c;
}

static long full_cost(void) {
    long dup = dup_count();
    lastbad = reach_cost();
    return lastbad + PEN * dup;
}

/* Simulated annealing from a random lift. Returns 1 if a valid lift is left in nbr. */
static int anneal(long iters, long patience) {
    N = 2 * K * G;
    uint64_t full = (1ULL << (2 * K)) - 1;
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) lay[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        for (int i = 0; i < K; i++) {
            inv[l][lay[l][i]] = i;
            vol[l][i] = rndint(G);
            set_dart(l, i);
        }
    }
    long cost = full_cost();
    long best = cost, last = 0;
    for (long t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && now() > t_end) break;
        double temp = 0.2 + 5.0 * (1.0 - (double)t / (double)iters);

        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(DEG);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            swap_layer(l, i1, i2);
            long c2 = full_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < best) {
                    best = cost;
                    last = t;
                }
            } else {
                swap_layer(l, i1, i2);
            }
            continue;
        }

        /* Voltage move, aimed at a block of an unreached vertex half of the time. */
        int tgt = -1;
        if (lastbad > 0 && rnd01() < 0.5) {
            for (int tr = 0; tr < 30; tr++) {
                int v = rndint(N);
                if (resr[v] != full) {
                    tgt = v;
                    break;
                }
            }
        }
        int l = rndint(DEG);
        int i;
        if (tgt >= 0) {
            int blk = tgt / G;
            if (blk < K) i = blk;
            else i = inv[l][blk - K];
        } else {
            i = rndint(K);
        }
        int old = vol[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        vol[l][i] = nw;
        set_dart(l, i);
        long c2 = full_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < best) {
                best = cost;
                last = t;
            }
        } else {
            vol[l][i] = old;
            set_dart(l, i);
        }
    }
    return cost == 0;
}

static long moore_cap(void) {
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
    long long seed = atoll(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit;
    rs ^= ((uint64_t)seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (DEG < 3 || DEG > MAXD || DIA < 3) {
        printf("0 0\n");
        return 0;
    }
    long cap = moore_cap();
    if (cap > 50000) cap = 50000;

    double goal = 4.0 * DEG;
    long trials[MAXK + 1] = {0}, wins[MAXK + 1] = {0};
    while (now() < t_end) {
        if (bestN >= cap) break;
        if (goal > (double)cap) goal = (double)cap;

        int k = 1;
        if (rnd01() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bs = -1.0;
            for (int kk = 1; kk <= MAXK; kk++) {
                double sc = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rnd01();
                if (sc > bs) {
                    bs = sc;
                    k = kk;
                }
            }
        }
        long target = (long)(goal / (2.0 * k)) + rndint(3);
        if (target < 2) target = 2;
        if (!sample_group(target)) {
            goal = dmax(bestN * 1.02, goal * 0.99);
            continue;
        }
        long NN = 2L * k * G;
        if (NN <= bestN) {
            goal = dmax(goal, bestN * 1.02);
            continue;
        }
        if (NN > MAXN) {
            goal = dmax(bestN * 1.02, goal * 0.97);
            continue;
        }

        K = k;
        N = (int)NN;
        trials[k]++;
        int ok = anneal(12000, 2500);
        if (ok) {
            wins[k]++;
            bestN = N;
            bK = K;
            bG = G;
            bDEG = DEG;
            for (int l = 0; l < DEG; l++) memcpy(bn[l], nbr[l], sizeof(int) * (size_t)N);
            goal = N * 1.04;
        } else {
            goal = dmax(bestN * 1.02, goal * 0.99);
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    int A = bK * bG;
    printf("%d %ld\n", bestN, (long)A * bDEG);
    for (int v = 0; v < A; v++)
        for (int l = 0; l < bDEG; l++) printf("%d %d\n", v, bn[l][v]);
    return 0;
}
'''


_KS = (1, 2, 3, 4)
_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


# ----------------------------------------------------------------------------
# Exact small constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Python fallback (used only if the C engine fails): the same bi-Cayley lift search.
# ----------------------------------------------------------------------------

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
    """Return (G, Ts, Invs) with Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h."""
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
    """Bitmask per vertex: bit b set when block identity b is within distance D."""
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
    """Simulated annealing with stagnation restarts. Returns (n, edges) or None."""
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


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions (the calibration case returns immediately).
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D < 3 or d < 3:
        return best

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total
    budget = max(0.5, 0.85 * time_limit - 4.0)

    # Main phase: the whole lift search runs in C at native speed.
    c_ok = True
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=None, timeout=budget + 5)
        consider(*lib.parse_graph_text(text))
    except Exception:
        c_ok = False

    # Fallback phase: only if the C engine failed, use the Python lift search.
    if not c_ok:
        rng = random.Random(seed)
        goal = float(best_n) * 1.05
        while time.monotonic() < final - 1.0:
            k = rng.choice(_KS)
            target = max(2, int(goal // (2 * k)) + rng.randrange(0, 3))
            g = _sample_group(target, rng)
            if g is None:
                goal = max(float(best_n) * 1.02, goal * 0.99)
                continue
            m, k2, r = g
            G, Ts, Invs = _semidirect_tables(m, k2, r)
            if 2 * k * G <= best_n:
                goal = max(goal, best_n * 1.02)
                continue
            res = _search(d, D, k, G, Ts, Invs, rng, final, 4000, 1200)
            if res is not None:
                consider(res[0], res[1])
                goal = max(goal, res[0] * 1.04)
            else:
                goal = max(float(best_n) * 1.02, goal * 0.99)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
