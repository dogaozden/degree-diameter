"""Combined program: a C bi-Cayley voltage-lift annealer over semidirect groups Z_m x| Z_k2,
then the parent's Python lift search with the remaining time. Every candidate is checked with
lib.is_valid, and K_{d,d} (or an exact construction) is the fallback.

The C engine uses the left-translation symmetry of a bi-Cayley lift: distances from (i, g) equal
distances from (i, e), so validity needs only 2k BFS runs per evaluation.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


C_LIFT = r'''
/* Bi-Cayley voltage-lift annealer over G = Z_M x| Z_K2 (element a*K2+b, (a,b)(c,e)=(a+r^b c, b+e)).
 * Base: kk A-vertices and kk B-vertices. Layer l is a permutation P[l] (A index -> B index) with
 * voltage S[l][i]: A_{i,g} ~ B_{P[l][i], g*s}. Lift has N = 2*kk*G vertices, degree d, bipartite.
 * Left translations are automorphisms, so validity <=> every block identity (b,e) reaches all
 * vertices within distance D.
 * Usage:  prog d D seed secs kk M K2 r
 * stdout: "N m" + edges of a valid lift, or "0 0" if none was found in time.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 65536
#define MAXD 32
#define MAXK 8
#define PENALTY 1000L
#define PATIENCE 2000L

static int d, D, kk, M, K2, G, N;
static int pw[256];
static int P[MAXD][MAXK], PI[MAXD][MAXK], S[MAXD][MAXK], IS[MAXD][MAXK];
static int nbr[MAXN * MAXD];
static int vis[MAXN];
static int qbuf[MAXN];
static int vstamp = 0;
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

static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }

static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gmul(int x, int y) {
    int a1 = x / K2, b1 = x % K2, a2 = y / K2, b2 = y % K2;
    long long a = ((long long)a1 + (long long)pw[b1] * a2) % M;
    int b = (b1 + b2) % K2;
    return (int)a * K2 + b;
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long long t = ((long long)pw[nb] * a) % M;
    long long na = (M - t) % M;
    return (int)na * K2 + nb;
}

static void set_volt(int l, int i, int s) {
    S[l][i] = s;
    IS[l][i] = ginv(s);
}

static void swap_layer(int l, int i1, int i2) {
    int t = P[l][i1];
    P[l][i1] = P[l][i2];
    P[l][i2] = t;
    PI[l][P[l][i1]] = i1;
    PI[l][P[l][i2]] = i2;
}

static void random_init(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < kk; i++) P[l][i] = i;
        for (int i = kk - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = P[l][i];
            P[l][i] = P[l][j];
            P[l][j] = t;
        }
        for (int i = 0; i < kk; i++) PI[l][P[l][i]] = i;
        for (int i = 0; i < kk; i++) set_volt(l, i, rndint(G));
    }
}

static void build_nbr(void) {
    for (int i = 0; i < kk; i++)
        for (int g = 0; g < G; g++) {
            int v = i * G + g;
            for (int l = 0; l < d; l++) {
                int j = P[l][i];
                nbr[v * d + l] = (kk + j) * G + gmul(g, S[l][i]);
            }
        }
    for (int j = 0; j < kk; j++)
        for (int h = 0; h < G; h++) {
            int v = (kk + j) * G + h;
            for (int l = 0; l < d; l++) {
                int i = PI[l][j];
                nbr[v * d + l] = i * G + gmul(h, IS[l][i]);
            }
        }
}

static int dups(void) {
    int c = 0;
    for (int i = 0; i < kk; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (P[l1][i] == P[l2][i] && S[l1][i] == S[l2][i]) c++;
    return c;
}

/* Number of vertices within distance D of src (BFS over the lift). */
static int ball(int src) {
    vstamp++;
    int head = 0, tail = 0;
    qbuf[tail++] = src;
    vis[src] = vstamp;
    for (int dep = 0; dep < D; dep++) {
        int end = tail;
        if (head == end) break;
        while (head < end) {
            int v = qbuf[head++];
            const int *nb = nbr + (size_t)v * d;
            for (int l = 0; l < d; l++) {
                int w = nb[l];
                if (vis[w] != vstamp) {
                    vis[w] = vstamp;
                    qbuf[tail++] = w;
                }
            }
        }
    }
    return tail;
}

static long eval_cost(void) {
    long unreached = 0;
    for (int b = 0; b < 2 * kk; b++) unreached += (long)(N - ball(b * G));
    return unreached + PENALTY * (long)dups();
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: %s d D seed secs kk M K2 r\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    kk = atoi(argv[5]);
    M = atoi(argv[6]);
    K2 = atoi(argv[7]);
    int rr = atoi(argv[8]);

    double until = now() + limit * 0.92 - 0.1;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1 || kk < 1 || kk > MAXK || M < 2 || K2 < 1 || K2 > 255 ||
        rr < 0 || rr >= M) {
        printf("0 0\n");
        return 0;
    }
    G = M * K2;
    N = 2 * kk * G;
    if (N > MAXN) {
        printf("0 0\n");
        return 0;
    }
    pw[0] = 1 % M;
    for (int b = 1; b < K2; b++) pw[b] = (int)((long long)pw[b - 1] * rr % M);
    if ((long long)pw[K2 - 1] * rr % M != 1 % M) {
        printf("0 0\n");
        return 0;
    }

    int found = 0;
    while (!found && now() < until) {
        random_init();
        build_nbr();
        long cost = eval_cost();
        long best = cost;
        double T = 0.01 * (double)cost + 2.0;
        long stall = 0;
        while (cost > 0 && stall < PATIENCE) {
            if (now() > until) break;
            if (kk >= 2 && rnd01() < 0.3) {
                int l = rndint(d);
                int i1 = rndint(kk);
                int i2 = rndint(kk - 1);
                if (i2 >= i1) i2++;
                swap_layer(l, i1, i2);
                build_nbr();
                long c2 = eval_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    swap_layer(l, i1, i2);
                    build_nbr();
                }
            } else {
                int l = rndint(d);
                int i = rndint(kk);
                int old = S[l][i];
                int nw = (old + 1 + rndint(G - 1)) % G;
                set_volt(l, i, nw);
                build_nbr();
                long c2 = eval_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    set_volt(l, i, old);
                    build_nbr();
                }
            }
            if (cost < best) {
                best = cost;
                stall = 0;
            } else {
                stall++;
            }
            T *= 0.997;
            if (T < 0.5) T = 0.5;
        }
        if (cost == 0) found = 1;
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    long m = (long)kk * G * d;
    printf("%d %ld\n", N, m);
    for (int v = 0; v < kk * G; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nbr[(size_t)v * d + l]);
    return 0;
}
'''

_C_MAX_N = 60000
_KS = (1, 2, 3, 4)
_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


# ----------------------------------------------------------------------------
# Small exact constructions.
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
# Saturation: add legal missing edges between deficient opposite-side vertices.
# Distances only shrink, so validity is preserved; callers still check.
# ----------------------------------------------------------------------------

def _saturate(n, edges, d, D):
    """Greedily add missing bipartite edges between deficient vertices; returns (n, edges)."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if color[y] == -1:
                    color[y] = 1 - color[x]
                    stack.append(y)
    A = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    B = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    out = {(min(u, v), max(u, v)) for u, v in edges}
    for a in A:
        for b in B:
            if len(adj[a]) >= d:
                break
            if len(adj[b]) >= d or b in adj[a]:
                continue
            adj[a].add(b)
            adj[b].add(a)
            out.add((min(a, b), max(a, b)))
    return n, sorted(out)


def _safe_saturate(n, edges, d, D):
    """Saturate, but fall back to the input if anything goes wrong or the result is invalid."""
    try:
        sn, se = _saturate(n, edges, d, D)
        if lib.is_valid(sn, se, d, D):
            return sn, se
    except Exception:
        pass
    return n, edges


# ----------------------------------------------------------------------------
# Python bi-Cayley lift helpers (numpy search, used in the second phase).
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
    """Bitmask per vertex: bit b set when block representative b is within distance D."""
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


_BUILD_KS = _KS


def _pick_k(trials, wins, rng):
    """Bandit choice of base size k (success rate with exploration)."""
    if rng.random() < 0.2:
        return rng.choice(_KS)
    return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())


def _c_lift(d, D, seed, secs, k, m, k2, r):
    """Run the C voltage-lift annealer for one group; returns (n, edges), with n = 0 if nothing was found."""
    text = lib.run_c(C_LIFT, [d, D, seed, round(secs, 2), k, m, k2, r],
                     timeout=secs + 15.0)
    return lib.parse_graph_text(text)


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 1.5)
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

    def consider_saturated(n, e):
        sn, se = _safe_saturate(n, e, d, D)
        consider(sn, se)
        consider(n, e)

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
            consider_saturated(*lib.araujo_lopez_graph(d - 2))
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

    # Phase 1: C voltage-lift annealer over semidirect groups. The order target is adaptive:
    # a success raises it by a growing step, a failure shrinks the step.
    c_deadline = t0 + 0.62 * total
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    step = 0.25
    c_errors = 0
    if d >= 2 and D >= 3:
        while c_errors < 3:
            secs = min(5.0, c_deadline - time.monotonic())
            if secs < 1.0:
                break
            k = _pick_k(trials, wins, rng)
            want = best_n * (1.0 + step)
            target = max(2, int(want // (2 * k)) + rng.randrange(0, 3))
            g = _sample_group(target, rng)
            if g is None:
                step = max(0.02, step * 0.9)
                continue
            m, k2, r = g
            G_ = m * k2
            if 2 * k * G_ <= best_n or 2 * k * G_ > _C_MAX_N:
                step = max(0.02, step * 0.9)
                continue
            trials[k] += 1
            try:
                n, e = _c_lift(d, D, rng.randrange(1 << 30), secs, k, m, k2, r)
            except Exception:
                c_errors += 1
                continue
            prev = best_n
            if n > 0:
                consider_saturated(n, e)
            if best_n > prev:
                wins[k] += 1
                step = min(0.6, step * 1.25)
            else:
                step = max(0.02, step * 0.8)

    # Phase 2: the parent's Python bi-Cayley annealer with the remaining lift time.
    lift_deadline = t0 + 0.9 * total
    trials2 = {k: 0 for k in _KS}
    wins2 = {k: 0 for k in _KS}
    goal = float(best_n) * 1.05

    while time.monotonic() < lift_deadline:
        k = _pick_k(trials2, wins2, rng)
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
        trials2[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, lift_deadline, 4000, 1200)
        if res is not None:
            wins2[k] += 1
            consider_saturated(res[0], res[1])
            goal = max(goal, best_n * 1.04)
        else:
            goal = max(float(best_n) * 1.02, goal * 0.99)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
