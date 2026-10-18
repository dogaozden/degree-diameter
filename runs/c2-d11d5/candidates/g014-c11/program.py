"""Combined program: a C voltage-lift engine over semidirect bi-Cayley groups, with exact
distance checks by BFS from block representatives, plus a Python lift search and grow
fallback. Every returned graph is checked with lib.is_valid; K_{d,d} is the fallback.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Bi-Cayley voltage-lift search over semidirect groups Z_m x| Z_k2.
 * Vertices: A_{i,g} = i*G + g (i < K), B_{j,h} = (K+j)*G + h, G = m*k2.
 * Layer l joins A_{i,g} to B_{perm[l][i], g*S[l][i]}; every layer is a permutation,
 * so the lift is d-regular and bipartite. Left multiplication is an automorphism,
 * so distances from the 2K block representatives decide diameter exactly.
 * Usage: prog d D seed time_limit goal_n
 * Output: "n m" + edges of the largest valid lift found, or "0 0".
 */

#define MAXV 16384
#define MAXD 16
#define MAXK 8

static int d, D;
static int K, K2, M, G, N;
static long long RR;
static long long PW[64];
static int perm[MAXD][MAXK], invp[MAXD][MAXK], S[MAXD][MAXK], sinv[MAXD][MAXK];
static int nbr[MAXV * MAXD];
static unsigned int mark[MAXV];
static unsigned int stampc = 0;
static int qbuf[MAXV];
static uint64_t rs = 88172645463325252ULL;
static long long PEN = 1;

static int bK, bM, bK2, bN;
static long long bR;
static int bperm[MAXD][MAXK], bS[MAXD][MAXK];
static int bestN = 0;

static double now_s(void) {
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

static long long pmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long long ggcd(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static void set_group(int k, int m, int k2, long long r) {
    K = k;
    M = m;
    K2 = k2;
    G = m * k2;
    N = 2 * K * G;
    RR = r;
    for (int b = 0; b < K2; b++) PW[b] = pmod(r, b, m);
    PEN = 4LL * N;
}

/* (a,b)*(c,e) = (a + r^b c, b + e) */
static int mul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long t = ((long long)a + PW[b] * (long long)c) % M;
    return (int)(t * K2 + (b + e) % K2);
}

/* Right inverse: x * inv_el(x) = identity. */
static int inv_el(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long long c = ((long long)M - (PW[nb] * (long long)a) % M) % M;
    return (int)(c * K2 + nb);
}

static void recompute_inv_layer(int l) {
    for (int i = 0; i < K; i++) invp[l][perm[l][i]] = i;
}

static void build_nbr(void) {
    for (int blk = 0; blk < 2 * K; blk++) {
        for (int g = 0; g < G; g++) {
            int *row = nbr + (size_t)(blk * G + g) * d;
            if (blk < K) {
                for (int l = 0; l < d; l++)
                    row[l] = (K + perm[l][blk]) * G + mul(g, S[l][blk]);
            } else {
                int j = blk - K;
                for (int l = 0; l < d; l++) {
                    int i = invp[l][j];
                    row[l] = i * G + mul(g, sinv[l][i]);
                }
            }
        }
    }
}

/* Sum over block representatives of vertices NOT within distance D. */
static long long unreached_cost(void) {
    long long total = 0;
    for (int b0 = 0; b0 < 2 * K; b0++) {
        stampc++;
        if (stampc == 0) {
            memset(mark, 0, sizeof(mark));
            stampc = 1;
        }
        int head = 0, tail = 0;
        int s = b0 * G;
        mark[s] = stampc;
        qbuf[tail++] = s;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int lend = tail;
            while (head < lend) {
                int u = qbuf[head++];
                const int *row = nbr + (size_t)u * d;
                for (int l = 0; l < d; l++) {
                    int w = row[l];
                    if (mark[w] != stampc) {
                        mark[w] = stampc;
                        qbuf[tail++] = w;
                    }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

/* Number of repeated (i, perm, voltage) triples, i.e. multi-edges. */
static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (perm[l][i] == perm[l2][i] && S[l][i] == S[l2][i]) c++;
    return c;
}

static long long evaluate(void) {
    build_nbr();
    return unreached_cost() + PEN * (long long)dupcount();
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = t;
        }
        recompute_inv_layer(l);
        for (int i = 0; i < K; i++) {
            S[l][i] = rndint(G);
            sinv[l][i] = inv_el(S[l][i]);
        }
    }
}

/* Simulated annealing on the current group. Returns final cost (0 = valid lift). */
static long long anneal(long long iters, long long patience, double deadline) {
    random_state();
    long long cost = evaluate();
    if (cost == 0) return 0;
    double T0 = 0.02 * (double)cost + 2.0, T1 = 0.3;
    long long last = 0, bestc = cost;
    for (long long t = 0; t < iters; t++) {
        if ((t & 15) == 0 && now_s() > deadline) break;
        if (t - last > patience) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        if (K >= 2 && rnd01() < 0.3) {
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K);
            if (i1 == i2) continue;
            int tmp = perm[l][i1];
            perm[l][i1] = perm[l][i2];
            perm[l][i2] = tmp;
            recompute_inv_layer(l);
            long long c2 = evaluate();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                tmp = perm[l][i1];
                perm[l][i1] = perm[l][i2];
                perm[l][i2] = tmp;
                recompute_inv_layer(l);
            }
        } else {
            int l = rndint(d), i = rndint(K);
            int old = S[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            S[l][i] = nw;
            sinv[l][i] = inv_el(nw);
            long long c2 = evaluate();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                S[l][i] = old;
                sinv[l][i] = inv_el(old);
            }
        }
        if (cost < bestc) {
            bestc = cost;
            last = t;
        }
        if (cost == 0) break;
    }
    return cost;
}

static void save_best(void) {
    bK = K;
    bM = M;
    bK2 = K2;
    bR = RR;
    bN = N;
    memcpy(bperm, perm, sizeof(perm));
    memcpy(bS, S, sizeof(S));
}

static void restore_best(void) {
    set_group(bK, bM, bK2, bR);
    memcpy(perm, bperm, sizeof(perm));
    memcpy(S, bS, sizeof(S));
    for (int l = 0; l < d; l++) {
        recompute_inv_layer(l);
        for (int i = 0; i < K; i++) sinv[l][i] = inv_el(S[l][i]);
    }
}

static const int K2OPT[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit goal_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long long goal = atoll(argv[5]);
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now_s() + limit;
    if (goal < 4) goal = 4;

    while (now_s() < tend) {
        if (goal > MAXV) goal = MAXV;
        int k = 1 + rndint(4);
        long long target = goal / (2LL * k) + rndint(3);
        if (target < 2) target = 2;
        int k2 = K2OPT[rndint(20)];
        long long m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (2LL * k * m * k2 > MAXV) {
            goal = goal - goal / 100 - 1;
            continue;
        }
        if (2LL * k * m * k2 <= bestN) {
            if (goal < (long long)bestN + 2) goal = (long long)bestN + 2;
            continue;
        }
        long long r = 1;
        if (k2 > 1 && m > 2) {
            int found = 0;
            for (int tr = 0; tr < 300 && !found; tr++) {
                long long c = 2 + (long long)(rnd() % (uint64_t)(m - 2));
                if (ggcd(c, m) == 1 && pmod(c, k2, m) == 1 % m) {
                    r = c;
                    found = 1;
                }
            }
            if (!found) continue;
        }
        set_group(k, (int)m, k2, r);
        double now = now_s();
        double slice = tend - now;
        if (slice > 6.0) slice = 6.0;
        if (slice <= 0.0) break;
        long long c = anneal(3000, 800, now + slice);
        if (c == 0) {
            bestN = N;
            save_best();
            goal = (long long)(N * 1.01) + 2;
        } else {
            long long g2 = (long long)(bestN * 1.005) + 2;
            long long g3 = goal - goal / 200;
            goal = g2 > g3 ? g2 : g3;
        }
    }

    if (bestN <= 0) {
        printf("0 0\n");
        return 0;
    }
    restore_best();
    build_nbr();
    long long edges = (long long)K * G * d;
    printf("%d %lld\n", N, edges);
    for (int u = 0; u < K * G; u++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", u, nbr[(size_t)u * d + l]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions.
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


# ----------------------------------------------------------------------------
# Python bi-Cayley lift search (fallback and warm start).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_PY_GMAX = 1500


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
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
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
    """Simulated annealing with stagnation stop. Returns (n, edges) or None."""
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

    total = max(1.0, 0.8 * time_limit - 2.0)
    final = t0 + total
    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions (calibration-style cases return immediately).
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
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    def python_lifts(until):
        goal = float(best_n) * 1.05
        while time.monotonic() < until:
            k = rng.choice(_KS)
            target = max(2, int(goal // (2 * k)) + rng.randrange(0, 3))
            target = min(target, _PY_GMAX)
            g = _sample_group(target, rng)
            if g is None:
                goal = max(float(best_n) * 1.02, goal * 0.99)
                continue
            m, k2, r = g
            if 2 * k * m * k2 <= best_n:
                goal = max(goal, best_n * 1.02)
                continue
            G, Ts, Invs = _semidirect_tables(m, k2, r)
            res = _search(d, D, k, G, Ts, Invs, rng, until, 4000, 1200)
            if res is not None:
                consider(res[0], res[1])
                goal = max(goal, res[0] * 1.04)
            else:
                goal = max(float(best_n) * 1.02, goal * 0.99)

    # Phase A: short Python lift search for a warm start (and a fallback if C fails).
    python_lifts(t0 + 0.15 * total)

    # Phase B: C voltage-lift engine with the bulk of the budget.
    remaining = final - time.monotonic() - 2.0
    if remaining > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), best_n + 2],
                             stdin_graph=None, timeout=remaining + 20)
            n_c, e_c = lib.parse_graph_text(text)
            consider(n_c, e_c)
        except Exception:
            pass

    # Phase C: leftover time in Python (if C failed early or finished with time left).
    python_lifts(final)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
