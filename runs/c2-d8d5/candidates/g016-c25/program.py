import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: voltage-lift annealer over semidirect products Z_m x| Z_k2.
#
# Graph: base has K left and K right vertices. The group G acts on each block
# by left multiplication, which is an automorphism of the lift. Layer l gives
# a perfect matching between left block i and right block layer[l][i] with
# voltage volt[l][i]: (L_i, x) ~ (R_j, x*s). Each vertex has degree d.
#
# Because of the group action, the lift is valid iff the ball of radius D around
# each of the 2K representatives (b, identity) covers all vertices. So a cost
# evaluation needs only 2K BFS runs. Simulated annealing moves swap layer
# targets or change voltages. Cost = unreached pairs + penalty * duplicate edges.
# ----------------------------------------------------------------------------

LIFT_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, K_, M_, K2_, R_, G_, N_;
static int *powR, *layer, *volt, *nbr, *dist, *queue, *stamp;
static int curstamp = 0;

/* element (a,b) coded as a*K2 + b; (a,b)*(c,e) = (a + R^b c, b + e) */
static int gmul(int x, int y) {
    int a = x / K2_, b = x % K2_;
    int c = y / K2_, e = y % K2_;
    long long t = ((long long)a + (long long)powR[b] * c) % M_;
    return (int)(t * K2_ + (b + e) % K2_);
}

static void build_nbr(void) {
    int K = K_, G = G_;
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K; i++) {
            int j = layer[l * K + i], s = volt[l * K + i];
            for (int x = 0; x < G; x++) {
                int u = i * G + x;
                int v = (K + j) * G + gmul(x, s);
                nbr[(size_t)u * d_ + l] = v;
                nbr[(size_t)v * d_ + l] = u;
            }
        }
    }
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K_; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (layer[l * K_ + i] == layer[l2 * K_ + i] &&
                    volt[l * K_ + i] == volt[l2 * K_ + i])
                    c++;
    return c;
}

/* Sum over the 2K representatives of the number of vertices not within D_ of them. */
static long long unreached(void) {
    long long tot = 0;
    for (int b = 0; b < 2 * K_; b++) {
        int src = b * G_;
        curstamp++;
        int h = 0, t = 0;
        queue[t++] = src;
        stamp[src] = curstamp;
        dist[src] = 0;
        while (h < t) {
            int v = queue[h++];
            if (dist[v] >= D_) continue;
            const int *nv = nbr + (size_t)v * d_;
            for (int l = 0; l < d_; l++) {
                int u = nv[l];
                if (stamp[u] != curstamp) {
                    stamp[u] = curstamp;
                    dist[u] = dist[v] + 1;
                    queue[t++] = u;
                }
            }
        }
        tot += N_ - t;
    }
    return tot;
}

#define PEN 40

static long long evalc(void) {
    build_nbr();
    return unreached() + (long long)PEN * (long long)dupcount();
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    K_ = atoi(argv[5]);
    M_ = atoi(argv[6]);
    K2_ = atoi(argv[7]);
    R_ = atoi(argv[8]);
    if (d_ < 1 || D_ < 1 || K_ < 1 || K_ > 16 || M_ < 1 || K2_ < 1) { printf("0 0\n"); return 0; }
    G_ = M_ * K2_;
    if (G_ > 4000) { printf("0 0\n"); return 0; }
    N_ = 2 * K_ * G_;

    powR = malloc(sizeof(int) * K2_);
    if (!powR) { printf("0 0\n"); return 0; }
    powR[0] = 1 % M_;
    for (int b = 1; b < K2_; b++) powR[b] = (int)((long long)powR[b - 1] * (R_ % M_) % M_);
    if (((long long)powR[K2_ - 1] * (R_ % M_)) % M_ != 1 % M_) { printf("0 0\n"); return 0; }

    layer = malloc(sizeof(int) * d_ * K_);
    volt = malloc(sizeof(int) * d_ * K_);
    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    dist = malloc(sizeof(int) * N_);
    queue = malloc(sizeof(int) * N_);
    stamp = calloc(N_, sizeof(int));
    int *perm = malloc(sizeof(int) * K_);
    if (!layer || !volt || !nbr || !dist || !queue || !stamp || !perm) { printf("0 0\n"); return 0; }

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K_; i++) perm[i] = i;
        for (int i = K_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K_; i++) layer[l * K_ + i] = perm[i];
    }
    for (int t = 0; t < d_ * K_; t++) volt[t] = rint_(G_);

    clock_t c0 = clock();
    long long cost = evalc();
    double T0 = 0.05 * (double)(cost > 0 ? cost : 1) + 2.0;
    const double T1 = 0.3;

    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);

        int l = rint_(d_);
        int kind = (K_ >= 2 && rdbl() < 0.35) ? 0 : 1;
        int i1 = rint_(K_), i2 = 0, o1 = 0;
        if (kind == 0) {
            i2 = rint_(K_ - 1);
            if (i2 >= i1) i2++;
            int *p1 = &layer[l * K_ + i1], *p2 = &layer[l * K_ + i2];
            int t = *p1; *p1 = *p2; *p2 = t;
        } else {
            int *pv = &volt[l * K_ + i1];
            o1 = *pv;
            *pv = rint_(G_);
        }

        long long nc = evalc();
        if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
            cost = nc;
        } else {
            if (kind == 0) {
                int *p1 = &layer[l * K_ + i1], *p2 = &layer[l * K_ + i2];
                int t = *p1; *p1 = *p2; *p2 = t;
            } else {
                volt[l * K_ + i1] = o1;
            }
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }
    build_nbr();
    int m = 0;
    for (int v = 0; v < N_; v++)
        for (int l = 0; l < d_; l++)
            if (nbr[(size_t)v * d_ + l] > v) m++;
    printf("%d %d\n", N_, m);
    for (int v = 0; v < N_; v++)
        for (int l = 0; l < d_; l++) {
            int u = nbr[(size_t)v * d_ + l];
            if (u > v) printf("%d %d\n", v, u);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


def _lift_search(d, D, rng, deadline, best, time_limit):
    """Repeatedly run the C voltage-lift annealer on growing target orders."""
    best_n = best[0]
    factor = 0.25  # relative growth over the current best order
    per_run = max(3.0, 0.12 * time_limit)
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 2.5:
            break
        k = rng.choice((1, 2, 2, 3, 3, 4, 4, 5, 6))
        target = max(best_n + 2, int(best_n * (1.0 + factor)) + 1)
        need = -(-target // (2 * k))
        g = _sample_group(need, rng)
        if g is None:
            continue
        m, k2, r = g
        budget = min(remaining - 1.0, per_run)
        try:
            out = lib.run_c(LIFT_C, [d, D, rng.randrange(1, 1 << 30), f"{budget:.2f}",
                                     k, m, k2, r], timeout=budget + 15.0)
            n, e = lib.parse_graph_text(out)
        except Exception:
            factor = max(0.003, factor * 0.7)
            continue
        if n > best_n and lib.is_valid(n, e, d, D):
            best, best_n = (n, e), n
            factor = min(0.3, factor * 1.5)
        else:
            factor = max(0.003, factor * 0.75)
    return best


# ----------------------------------------------------------------------------
# Python bi-Cayley annealer, kept as a hedge with the remaining time.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 with element a*k2+b."""
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
    """Simulated annealing over voltages and layer permutations. Returns (n, edges) or None."""
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 when d - 1 is a prime power (calibration case).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Phase 1 (main): voltage-lift search in C over growing orders.
    lift_end = t0 + max(2.0, min(0.6 * time_limit, time_limit - 14.0))
    if d >= 2:
        try:
            best = _lift_search(d, D, rng, lift_end, best, time_limit)
        except Exception:
            pass  # keep the valid fallback

    # Phase 2 (hedge): Python bi-Cayley annealing with a bandit over base sizes k.
    py_end = t0 + max(lift_end - t0, min(0.85 * time_limit, time_limit - 6.0))
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    try:
        while time.monotonic() < py_end:
            k = pick_k()
            base = best[0] // (2 * k)
            target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
            g = _sample_group(target, rng)
            if g is None:
                continue
            m, k2, r = g
            G, Ts, Invs = _semidirect_tables(m, k2, r)
            if 2 * k * G <= best[0]:
                continue
            trials[k] += 1
            res = _search(d, D, k, G, Ts, Invs, rng, py_end, 4000, 1200)
            if res is not None:
                wins[k] += 1
                consider(res[0], res[1])
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
