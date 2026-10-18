"""Cayley bipartite-double search for large-order degree-diameter graphs.

Main engine (C): bipartite double of a Cayley graph on Z_m x| Z_k. Left vertex g is
adjacent to right vertex g*s for s in a d-element set S. Left multiplication is an
automorphism, so diameter <= D reduces to two BFS runs (from a left and a right vertex).
Simulated annealing over S finds valid sets, and the group order grows one step at a time.
A short Python bi-Cayley phase provides a baseline and a fallback.
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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (Python baseline search).
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


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
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
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
    """Bandit over base sizes k; each trial tries to beat the current best order."""
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

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
# C engine: bipartite double of a Cayley graph on Z_m x|_r Z_k.
# Left (g,0) ~ right (g*s,1) for s in S, |S| = d. Diameter <= D is checked by two
# BFS runs (from a left and a right vertex) because left multiplication is an
# automorphism. Simulated annealing over S; the group order increases stepwise.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Cayley bipartite double search.
 * Usage: prog d D seed time_limit Nlow
 * Searches for a valid graph on 2N vertices with N > Nlow.
 * stdin is ignored. stdout: "n m" + edge lines, or "0 0" if nothing beats Nlow.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXG 3000
#define MAXV (2 * MAXG)
#define ITERS 20000

static int d, D;
static double t_end;
static int N, gm, gk, gr;
static int rp[MAXG];
static int16_t MULT[MAXG * MAXG];
static int INV[MAXG];
static int S[MAXD], Sinv[MAXD];
static int bestS[MAXD];
static int bm_, bk_, br_;
static uint32_t vis[MAXV];
static uint32_t stamp_ctr = 0;
static int qbuf[MAXV];

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
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

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static int gmul_raw(int x, int y) {
    int a = x / gk, b = x % gk, c = y / gk, e = y % gk;
    return (int)(((long)a + (long)rp[b] * c) % gm) * gk + (b + e) % gk;
}

/* Build the multiplication table and inverses for Z_m x|_r Z_k. Identity is 0. */
static void set_group(int m, int k, int r) {
    gm = m; gk = k; gr = r; N = m * k;
    rp[0] = 1 % gm;
    for (int b = 1; b < gk; b++) rp[b] = (int)((long)rp[b - 1] * gr % gm);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            MULT[(long)x * N + y] = (int16_t)gmul_raw(x, y);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MULT[(long)x * N + y] == 0) { INV[x] = y; break; }
}

/* Pick a random valid (m, k, r) with m*k = n, uniformly over all such triples. */
static void choose_group(int n, int *om, int *ok, int *orr) {
    long cnt = 0;
    int bm = 1, bk = n, br = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            cnt++;
            if (rnd() % (uint64_t)cnt == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rnd() % (uint64_t)cnt == 0) { bm = m; bk = k; br = r; }
        }
    }
    *om = bm; *ok = bk; *orr = br;
}

static int reach_count(int src) {
    int head = 0, tail = 0, count = 1, depth = 0;
    stamp_ctr++;
    vis[src] = stamp_ctr;
    qbuf[tail++] = src;
    while (head < tail && depth < D) {
        int end = tail;
        while (head < end) {
            int v = qbuf[head++];
            if (v < N) {
                const int16_t *row = MULT + (long)v * N;
                for (int t = 0; t < d; t++) {
                    int u = N + row[S[t]];
                    if (vis[u] != stamp_ctr) { vis[u] = stamp_ctr; qbuf[tail++] = u; count++; }
                }
            } else {
                const int16_t *row = MULT + (long)(v - N) * N;
                for (int t = 0; t < d; t++) {
                    int u = row[Sinv[t]];
                    if (vis[u] != stamp_ctr) { vis[u] = stamp_ctr; qbuf[tail++] = u; count++; }
                }
            }
        }
        depth++;
    }
    return count;
}

/* Number of (source, target) pairs still farther than D, counted from the two sources. */
static int cost_of(void) {
    int c1 = reach_count(0);
    int c2 = reach_count(N);
    return (2 * N - c1) + (2 * N - c2);
}

static int used(int x, int upto, int skip) {
    for (int j = 0; j < upto; j++)
        if (j != skip && S[j] == x) return 1;
    return 0;
}

/* Simulated annealing over S for the current group. Returns 1 if cost reaches 0. */
static int try_group(void) {
    for (int t = 0; t < d; t++) {
        int x;
        do { x = rndint(N); } while (used(x, t, -1));
        S[t] = x;
        Sinv[t] = INV[x];
    }
    int c = cost_of();
    for (int it = 0; it < ITERS && c > 0; it++) {
        if ((it & 63) == 0 && now() > t_end) return 0;
        double T = 1.05 * (1.0 - (double)it / ITERS) + 0.05;
        int t = rndint(d);
        int x;
        do { x = rndint(N); } while (used(x, d, t));
        int old = S[t];
        S[t] = x;
        Sinv[t] = INV[x];
        int c2 = cost_of();
        if (c2 <= c || rnd01() < exp((double)(c - c2) / T)) {
            c = c2;
        } else {
            S[t] = old;
            Sinv[t] = INV[old];
        }
    }
    return c == 0;
}

static void print_solution(void) {
    printf("%d %ld\n", 2 * N, (long)N * d);
    for (int g = 0; g < N; g++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", g, N + (int)MULT[(long)g * N + S[t]]);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit Nlow\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int Nlow = atoi(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    int found = 0;
    if (d >= 1 && D >= 2 && d <= MAXD) {
        long mb = moore_bound();
        int cur = Nlow;
        while (now() < t_end) {
            int target = cur + 1;
            if (target < d + 1) target = d + 1;
            if (2L * target > mb || target > MAXG) break;
            int m, k, r;
            choose_group(target, &m, &k, &r);
            set_group(m, k, r);
            if (try_group()) {
                found = 1;
                cur = target;
                bm_ = m; bk_ = k; br_ = r;
                memcpy(bestS, S, sizeof(int) * d);
            }
        }
    }

    if (found) {
        set_group(bm_, bk_, br_);
        memcpy(S, bestS, sizeof(int) * d);
        for (int t = 0; t < d; t++) Sinv[t] = INV[S[t]];
        print_solution();
    } else {
        printf("0 0\n");
    }
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

    # Safe fallback: the bipartite double of K_{d,d} type graph, diameter 2 <= D.
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

    if D >= 2 and time.monotonic() < end:
        # Phase 1 (Python): short bi-Cayley baseline, also the hedge if C fails.
        py_end = t0 + usable * 0.2
        best = _bicayley_phase(best, d, D, rng, py_end, consider)

        # Phase 2 (C): Cayley bipartite double search above the current order.
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2), best[0] // 2],
                                 stdin_graph=None, timeout=c_budget + 8)
                out = lib.parse_graph_text(text)
                consider(out[0], out[1])
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
