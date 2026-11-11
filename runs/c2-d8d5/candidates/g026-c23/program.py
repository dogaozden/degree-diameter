import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine with two modes.
#
# mode 0 (lift): Z_L-voltage lift of a base graph. Lifted vertex (u, i) is
#   stored as u + i*n0. Base edge (u, v) with voltage t joins (u, i) to
#   (v, (i + t) mod L) for every i. A lift keeps degrees and bipartiteness,
#   so it doubles (or multiplies) the order of a base that already works.
#   Annealing over the voltages minimises the number of ordered vertex pairs
#   at distance > D, computed with bitset ball expansion.
#
# mode 1 (grow): edge-toggle annealer with vertex growth (as before). Whenever
#   the cost reaches zero, the valid graph is saved and two isolated vertices
#   (one per side) are added.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, cap_n, cap_w, N, W;
static int *deg, *adj, *side, *bestEu, *bestEv;
static int *eu, *ev, *volt;
static u64 *bufA, *bufB;
static int best_n = 0, best_m = 0;
static int mb = 0, n0 = 0, LL = 2;

static int isadj(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a * d_ + i] == b) return 1;
    return 0;
}
static void delE1(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a * d_ + i] == b) {
            adj[a * d_ + i] = adj[a * d_ + deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}
static void addE(int a, int b) {
    adj[a * d_ + deg[a]++] = b;
    adj[b * d_ + deg[b]++] = a;
}
static void delE(int a, int b) { delE1(a, b); delE1(b, a); }

/* Ordered pairs (u, v) with distance > D_ among the first N vertices. */
static long long bad_pairs(void) {
    u64 *cur = bufA, *alt = bufB;
    W = (N + 63) / 64;
    memset(cur, 0, sizeof(u64) * (size_t)N * (size_t)cap_w);
    for (int v = 0; v < N; v++) cur[(size_t)v * cap_w + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 *x = alt + (size_t)v * cap_w;
            u64 *r = cur + (size_t)v * cap_w;
            for (int w = 0; w < W; w++) x[w] = r[w];
            for (int i = 0; i < deg[v]; i++) {
                u64 *q = cur + (size_t)adj[v * d_ + i] * cap_w;
                for (int w = 0; w < W; w++) x[w] |= q[w];
            }
            for (int w = 0; w < W; w++) if (x[w] != r[w]) changed = 1;
        }
        u64 *t = cur; cur = alt; alt = t;
        if (!changed) break;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) {
        u64 *r = cur + (size_t)v * cap_w;
        for (int w = 0; w < W; w++) cnt += __builtin_popcountll(r[w]);
    }
    return (long long)N * N - cnt;
}

static void save_best(void) {
    int m = 0;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v * d_ + i];
            if (u > v) { bestEu[m] = v; bestEv[m] = u; m++; }
        }
    }
    best_n = N;
    best_m = m;
}

static void print_best(void) {
    if (best_n == 0) { printf("0 0\n"); return; }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestEu[i], bestEv[i]);
}

static void grow_pair(void) {
    side[N] = 0; deg[N] = 0;
    side[N + 1] = 1; deg[N + 1] = 0;
    N += 2;
}

/* Rebuild the lifted graph from the base edges and current voltages. */
static void build_lift(void) {
    for (int x = 0; x < N; x++) deg[x] = 0;
    for (int e = 0; e < mb; e++) {
        int u = eu[e], v = ev[e], t = volt[e];
        for (int i = 0; i < LL; i++) {
            int x = u + i * n0;
            int y = v + ((i + t) % LL) * n0;
            addE(x, y);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 6) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    int mode = atoi(argv[5]);
    int param = argc > 6 ? atoi(argv[6]) : 2;

    int nin = 0, min_ = 0;
    if (scanf("%d %d", &nin, &min_) != 2) { nin = 0; min_ = 0; }
    if (d_ < 1 || D_ < 1 || nin < 2 || nin > 1000000 || min_ < 0 || param < 0) {
        printf("0 0\n");
        return 0;
    }

    n0 = nin;
    int grow_max = 0;
    if (mode == 0) {
        LL = param < 2 ? 2 : param;
        cap_n = n0 * LL;
    } else {
        grow_max = param;
        cap_n = n0 + 2 * grow_max + 2;
    }
    if (cap_n < n0) cap_n = n0;
    cap_w = (cap_n + 63) / 64;

    deg = calloc(cap_n, sizeof(int));
    side = malloc(sizeof(int) * (size_t)cap_n);
    adj = malloc(sizeof(int) * (size_t)cap_n * d_);
    bestEu = malloc(sizeof(int) * (size_t)cap_n * d_);
    bestEv = malloc(sizeof(int) * (size_t)cap_n * d_);
    bufA = malloc(sizeof(u64) * (size_t)cap_n * cap_w);
    bufB = malloc(sizeof(u64) * (size_t)cap_n * cap_w);
    eu = malloc(sizeof(int) * (size_t)(min_ + 1));
    ev = malloc(sizeof(int) * (size_t)(min_ + 1));
    volt = malloc(sizeof(int) * (size_t)(min_ + 1));
    int *q = malloc(sizeof(int) * (size_t)cap_n);
    if (!deg || !side || !adj || !bestEu || !bestEv || !bufA || !bufB ||
        !eu || !ev || !volt || !q) {
        printf("0 0\n");
        return 0;
    }

    /* Read and filter the input graph (simple, degree <= d_). */
    N = n0;
    mb = 0;
    for (int i = 0; i < min_; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) continue;
        if (deg[u] >= d_ || deg[v] >= d_ || isadj(u, v)) continue;
        addE(u, v);
        eu[mb] = u; ev[mb] = v; mb++;
    }

    if (mode == 0) {
        if (mb == 0) { printf("0 0\n"); return 0; }
        N = n0 * LL;
        for (int e = 0; e < mb; e++) volt[e] = rint_(LL);
        build_lift();
        clock_t c0 = clock();
        long long cost = bad_pairs();
        while (cost > 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= limit) break;
            double T = 40.0 * pow(0.5 / 40.0, el / limit);
            int e = rint_(mb);
            int old = volt[e];
            volt[e] = (old + 1 + rint_(LL - 1)) % LL;
            build_lift();
            long long nc = bad_pairs();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                volt[e] = old;
                build_lift();
            }
        }
        if (cost == 0) save_best();
    } else {
        /* Bipartition by BFS; isolated vertices take the side of their root. */
        for (int v = 0; v < N; v++) side[v] = -1;
        for (int s = 0; s < N; s++) {
            if (side[s] != -1) continue;
            side[s] = 0;
            int h = 0, t = 0;
            q[t++] = s;
            while (h < t) {
                int v = q[h++];
                for (int i = 0; i < deg[v]; i++) {
                    int u = adj[v * d_ + i];
                    if (side[u] == -1) { side[u] = 1 - side[v]; q[t++] = u; }
                }
            }
        }

        const double T0 = 30.0, T1 = 0.3;
        clock_t c0 = clock();
        long long cost = bad_pairs();
        if (cost == 0 && N > best_n) {
            save_best();
            if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(); }
        }
        while (1) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= limit) break;
            double frac = el / limit;
            double T = T0 * pow(T1 / T0, frac);

            int a = -1, b = -1;
            for (int t = 0; t < 50; t++) {
                int x = rint_(N), y = rint_(N);
                if (x == y || side[x] == side[y] || isadj(x, y)) continue;
                a = x; b = y;
                break;
            }
            if (a < 0) continue;

            int xa = -1, xb = -1;
            if (deg[a] == d_) { xa = adj[a * d_ + rint_(deg[a])]; delE(a, xa); }
            if (deg[b] == d_) { xb = adj[b * d_ + rint_(deg[b])]; delE(b, xb); }
            addE(a, b);

            long long nc = bad_pairs();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
                if (cost == 0 && N > best_n) {
                    save_best();
                    if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(); }
                }
            } else {
                delE(a, b);
                if (xa >= 0) addE(a, xa);
                if (xb >= 0) addE(b, xb);
            }
        }
    }

    print_best();
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


def _run_c(d, D, mode, seconds, seed, param, graph):
    """Run the C engine (mode 0 = Z_L lift, mode 1 = grow) and parse its output."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}", mode, param],
                    stdin_graph=graph, timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Phase 1 (about 30%): find a moderate-size bi-Cayley BASE graph. Lifting it
    # by 2 is the new step; the base should be about half the target order.
    moore = lib.moore_bound(d, D)
    base_target = max(4, int(0.155 * moore))
    base = None
    p1_end = t0 + 0.30 * time_limit
    while time.monotonic() < p1_end:
        k = rng.choice(_KS)
        Gt = max(2, -(-base_target // (2 * k)) + rng.randrange(0, 3))
        g = _sample_group(Gt, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        res = _search(d, D, k, G, Ts, Invs, rng, p1_end, 4000, 1200)
        if res is None:
            continue
        consider(res[0], res[1])
        if res[0] <= 1.2 * base_target and (base is None or res[0] > base[0]):
            base = res
    if base is None:
        base = best

    # Phase 2 (until 75%): Z_2 lift of the base, annealing the voltages.
    # A valid lift has twice the base order, so it can beat the record directly.
    lift_end = t0 + 0.75 * time_limit
    lift_budget = lift_end - time.monotonic() - 1.0
    if base[0] >= 4 and lift_budget >= 1.0:
        try:
            ln, le = _run_c(d, D, 0, lift_budget, rng.randrange(1, 1 << 30), 2, base)
            consider(ln, le)
        except Exception:
            pass  # keep the valid fallback

    # Phase 3: grow the best valid graph by vertex pairs in C, with what remains.
    c_budget = time_limit - (time.monotonic() - t0) - 4.0
    if c_budget >= 1.0:
        try:
            gn, ge = _run_c(d, D, 1, c_budget, rng.randrange(1, 1 << 30), 200, best)
            consider(gn, ge)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
