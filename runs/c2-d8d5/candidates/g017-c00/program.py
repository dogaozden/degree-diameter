"""Bold variant: Haar-graph annealing in C over many groups, seeded by a short Python bi-Cayley lift search."""
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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (Python search).
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{p,g*s}.
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
# C engine: Haar graphs (bi-Cayley over one group) with simulated annealing on
# the connection set S. Left multiplication is an automorphism, so the diameter
# only needs BFS from A_e and B_e; a final check runs BFS from every vertex.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Haar-graph annealing.
 * Group G of order N (Z_m x|_r Z_k, element a*k+b). Vertices A_g = g, B_h = N+h.
 * Edges A_g ~ B_{g*s} for s in S, |S| = d (distinct). Degree d, bipartite.
 * Usage: prog d D seed time_limit n0
 * stdout: "n m" + edges of the largest valid Haar graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 2048
#define MAXD 32

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
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

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* Group state. */
static int N, GM, GK, GR;
static int rp[MAXG];
static int RM[MAXG * MAXG];   /* RM[s*N+g] = g*s */
static int INV[MAXG];

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    return (int)(((long)a + (long)rp[b] * c) % GM) * GK + (b + e) % GK;
}

/* Pick a random (m,k,r) with m*k = n, r^k = 1 mod m, gcd(r,m) = 1 (uniform over candidates). */
static int choose_group(int n) {
    int cm = 0, ck = 0, cr = 0;
    long cnt = 0;
    for (int k = 1; k <= n; k++) {
        if (n % k) continue;
        int m = n / k;
        int rmax = (m == 1) ? 1 : m - 1;
        for (int r = 1; r <= rmax; r++) {
            if (k == 1 && r != 1) continue;
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { cm = m; ck = k; cr = r; }
        }
    }
    if (cnt == 0) return 0;
    GM = cm; GK = ck; GR = cr;
    return 1;
}

static void build_group(void) {
    rp[0] = 1 % GM;
    for (int b = 1; b < GK; b++) rp[b] = (int)((long)rp[b - 1] * GR % GM);
    for (int s = 0; s < N; s++)
        for (int g = 0; g < N; g++)
            RM[s * N + g] = gmul(g, s);
    for (int s = 0; s < N; s++) INV[s] = 0;
    for (int s = 0; s < N; s++)
        for (int x = 0; x < N; x++)
            if (RM[s * N + x] == 0) { INV[s] = x; break; }
}

/* Connection set. */
static int S[MAXD], SI[MAXD];

static int in_prefix(int k, int x) {
    for (int j = 0; j < k; j++)
        if (S[j] == x) return 1;
    return 0;
}

/* Scratch for BFS. */
static int dist_[2 * MAXG], qb[2 * MAXG], vis[2 * MAXG];
static int stamp = 0;

/* Number of vertices NOT within distance D of src. */
static int unreached(int src) {
    int V = 2 * N;
    stamp++;
    int head = 0, tail = 0, cnt = 1;
    qb[tail++] = src;
    vis[src] = stamp;
    dist_[src] = 0;
    while (head < tail) {
        int v = qb[head++];
        int dv = dist_[v];
        if (dv >= D) continue;
        if (v < N) {
            for (int t = 0; t < d; t++) {
                int u = N + RM[S[t] * N + v];
                if (vis[u] != stamp) {
                    vis[u] = stamp;
                    dist_[u] = dv + 1;
                    qb[tail++] = u;
                    cnt++;
                }
            }
        } else {
            int h = v - N;
            for (int t = 0; t < d; t++) {
                int u = RM[SI[t] * N + h];
                if (vis[u] != stamp) {
                    vis[u] = stamp;
                    dist_[u] = dv + 1;
                    qb[tail++] = u;
                    cnt++;
                }
            }
        }
    }
    return V - cnt;
}

static int cost_of(void) { return unreached(0) + unreached(N); }

static int found = 0, F_N, F_M, F_K, F_R;
static int F_S[MAXD];

/* Simulated annealing over S for the current group. Returns 1 when cost 0. */
static int sa_run(long maxit, long patience) {
    for (int t = 0; t < d; t++) {
        int x;
        do { x = rndint(N); } while (in_prefix(t, x));
        S[t] = x;
        SI[t] = INV[x];
    }
    int cost = cost_of();
    int best = cost;
    long last = 0;
    for (long it = 0; it < maxit; it++) {
        if (cost == 0) break;
        if ((it & 63) == 0 && now() > t_end) return 0;
        if (it - last > patience) return 0;
        int t = rndint(d);
        int x = rndint(N);
        if (in_prefix(d, x)) continue;
        int old = S[t], oldi = SI[t];
        S[t] = x;
        SI[t] = INV[x];
        int c2 = cost_of();
        double T = 0.3 + 1.5 * (1.0 - (double)it / (double)maxit);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost < best) { best = cost; last = it; }
        } else {
            S[t] = old;
            SI[t] = oldi;
        }
    }
    return cost == 0;
}

/* Try random groups of order n until one works or the deadline passes. */
static int attempt(int n, double until) {
    while (now() < until && now() < t_end) {
        N = n;
        if (!choose_group(n)) return 0;
        build_group();
        if (sa_run(200000, 8000)) {
            found = 1;
            F_N = N; F_M = GM; F_K = GK; F_R = GR;
            memcpy(F_S, S, sizeof(int) * (size_t)d);
            return 1;
        }
    }
    return 0;
}

static void emit(void) {
    N = F_N; GM = F_M; GK = F_K; GR = F_R;
    build_group();
    for (int t = 0; t < d; t++) {
        S[t] = F_S[t];
        SI[t] = INV[S[t]];
    }
    /* Full verification: BFS from every vertex. */
    for (int v = 0; v < 2 * N; v++) {
        if (unreached(v) != 0) { printf("0 0\n"); return; }
    }
    printf("%d %ld\n", 2 * N, (long)N * d);
    for (int g = 0; g < N; g++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", g, N + RM[S[t] * N + g]);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit n0\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int n0 = atoi(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("0 0\n"); return 0; }
    if (n0 < d) n0 = d;

    /* Exponential/binary style walk over the group order N. */
    int lo = n0 - 1, step = 1;
    while (now() < t_end) {
        int nt = lo + step;
        if (nt > MAXG) {
            if (step == 1) break;
            step /= 2;
            continue;
        }
        double rem = t_end - now();
        double slice = rem * 0.3;
        if (slice < 0.5) slice = 0.5;
        if (slice > rem) slice = rem;
        if (attempt(nt, now() + slice)) {
            lo = nt;
            step *= 2;
        } else {
            if (step == 1) break;
            step /= 2;
        }
    }
    if (found) emit();
    else printf("0 0\n");
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

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Return the new graph if it is a larger valid graph, else None."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return best
        return None

    if D == 2:
        return best

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

    # Phase 1 (Python): bi-Cayley semidirect lift search. Keeps the known-good level.
    py_end = t0 + usable * 0.35
    best = _bicayley_phase(best, d, D, rng, py_end, consider)

    # Phase 2 (C): Haar-graph annealing starting just above the current order.
    c_budget = end - time.monotonic() - 0.5
    if c_budget > 1.0:
        n0 = max(d, best[0] // 2 + 1)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2), n0],
                             timeout=c_budget + 6)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
