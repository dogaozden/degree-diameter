import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: bipartite edge-toggle annealer with vertex growth, plus
# semidirect-product voltage lifts and grow-by-two repair.
#
# Modes (chosen by the first CLI arg "mode"):
#   0 = edge-toggle annealing with growth (from a valid start graph)
#   1 = grow-by-two repair from the start graph
# The C side always prints the largest valid graph it has found.
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
static u64 *bufA, *bufB;
static int *badv;
static int best_n = 0, best_m = 0;

static double wall(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

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

/* Ordered pairs (u, v) at distance > D_. Also fills badv[v] = bad partners of v. */
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
        int c = 0;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(r[w]);
        badv[v] = N - c;
        cnt += c;
    }
    return (long long)N * N - cnt;
}

static void save_best(void) {
    int m = 0;
    for (int v = 0; v < N; v++)
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v * d_ + i];
            if (u > v) { bestEu[m] = v; bestEv[m] = u; m++; }
        }
    best_n = N;
    best_m = m;
}

static void grow_pair(void) {
    side[N] = 0; deg[N] = 0;
    side[N + 1] = 1; deg[N + 1] = 0;
    N += 2;
}

/* Edge-toggle annealing with growth. Returns when time runs out. */
static void anneal(double limit, double t0, int grow_max) {
    long long cost = bad_pairs();
    if (cost == 0 && N > best_n) {
        save_best();
        if (N + 2 <= cap_n && grow_max > 0) { grow_pair(); cost = bad_pairs(); }
    }
    double T0 = 30.0, T1 = 0.3;
    long it = 0;
    while (1) {
        if ((++it & 7) == 0) {
            double el = wall() - t0;
            if (el >= limit) break;
        }
        double el = wall() - t0;
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
                if (N + 2 <= cap_n && grow_max > 0) { grow_pair(); cost = bad_pairs(); }
            }
        } else {
            delE(a, b);
            if (xa >= 0) addE(a, xa);
            if (xb >= 0) addE(b, xb);
        }
    }
}

/* Grow-by-two repair: add x (side 0) and y (side 1) joined, rewire until valid. */
static int bad_list[4096];
static int badsave[4096];
static int saved_n_side[4096];

static int grow_try(int n, double until) {
    /* Work on the current state (N = n). Add two vertices, then repair. */
    if (n + 2 > cap_n) return 0;
    int x = N, y = N + 1;
    side[x] = 0; deg[x] = 0;
    side[y] = 1; deg[y] = 0;
    N += 2;
    addE(x, y);
    static int used[4096];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    int k = 1;
    for (int tries = 0; k < d_ && tries < 20000; tries++) {
        int a = rint_(n);
        if (side[a] != 0 || used[a] == stamp || deg[a] == 0) continue;
        int b = adj[a * d_ + rint_(deg[a])];
        if (used[b] == stamp || b >= n) continue;
        delE(a, b);
        addE(x, b);
        addE(y, a);
        used[a] = used[b] = stamp;
        k++;
    }
    long long bad = bad_pairs();
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && wall() > until) return 0;
        int nbad = 0;
        for (int w = 0; w < N; w++) if (badv[w] > 0) bad_list[nbad++] = w;
        int v = nbad ? bad_list[rint_(nbad)] : rint_(N);
        if (deg[v] == 0) continue;
        int u = adj[v * d_ + rint_(deg[v])];
        int s = rint_(N);
        if (side[s] != side[v] || s == v || deg[s] == 0) continue;
        int t = adj[s * d_ + rint_(deg[s])];
        if (t == u || isadj(v, t) || isadj(s, u)) continue;
        memcpy(badsave, badv, sizeof(int) * N);
        delE(v, u);
        delE(s, t);
        addE(v, t);
        addE(s, u);
        long long nb = bad_pairs();
        if (nb <= bad || rdbl() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            delE(v, t);
            delE(s, u);
            addE(v, u);
            addE(s, t);
            memcpy(badv, badsave, sizeof(int) * N);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return 1;
}

static void grow_search(double until) {
    /* Snapshot the valid graph, try to grow by two; restore on failure. */
    static int snapN;
    static int *snapDeg = NULL, *snapAdj = NULL, *snapSide = NULL;
    if (!snapDeg) {
        snapDeg = malloc(sizeof(int) * (size_t)cap_n);
        snapAdj = malloc(sizeof(int) * (size_t)cap_n * d_);
        snapSide = malloc(sizeof(int) * (size_t)cap_n);
    }
    while (wall() < until) {
        snapN = N;
        memcpy(snapDeg, deg, sizeof(int) * (size_t)N);
        memcpy(snapAdj, adj, sizeof(int) * (size_t)N * d_);
        memcpy(snapSide, side, sizeof(int) * (size_t)N);
        int ok = grow_try(snapN, until);
        if (ok && bad_pairs() == 0) {
            if (N > best_n) save_best();
        } else {
            N = snapN;
            memcpy(deg, snapDeg, sizeof(int) * (size_t)N);
            memcpy(adj, snapAdj, sizeof(int) * (size_t)N * d_);
            memcpy(side, snapSide, sizeof(int) * (size_t)N);
            bad_pairs();
            if (ok) break;
        }
        if (N + 2 > cap_n) break;
    }
}

/* Read start graph; compute sides by BFS. Returns 1 if start is valid-ish. */
static int read_start(void) {
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) return 0;
    if (n0 < 1 || n0 > 100000) return 0;
    N = n0;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (deg[u] >= d_ || deg[v] >= d_ || isadj(u, v)) continue;
        addE(u, v);
    }
    for (int v = 0; v < N; v++) side[v] = -1;
    int *q = malloc(sizeof(int) * (size_t)cap_n);
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
    free(q);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double limit = atof(argv[4]);
    int mode = argc > 5 ? atoi(argv[5]) : 0;
    double t0 = wall();

    if (d_ < 1 || D_ < 1 || d_ > 32) { printf("0 0\n"); return 0; }

    int grow_max = 400;
    cap_n = 4096;
    cap_w = (cap_n + 63) / 64;
    deg = calloc(cap_n, sizeof(int));
    side = malloc(sizeof(int) * (size_t)cap_n);
    adj = malloc(sizeof(int) * (size_t)cap_n * d_);
    bestEu = malloc(sizeof(int) * (size_t)cap_n * d_);
    bestEv = malloc(sizeof(int) * (size_t)cap_n * d_);
    bufA = malloc(sizeof(u64) * (size_t)cap_n * cap_w);
    bufB = malloc(sizeof(u64) * (size_t)cap_n * cap_w);
    badv = malloc(sizeof(int) * (size_t)cap_n);
    if (!deg || !side || !adj || !bestEu || !bestEv || !bufA || !bufB || !badv) {
        printf("0 0\n");
        return 0;
    }

    int ok = read_start();
    if (!ok || N < 2) {
        /* Fallback: K_{d,d}. */
        N = 2 * d_;
        for (int v = 0; v < N; v++) { deg[v] = 0; side[v] = v >= d_; }
        for (int a = 0; a < d_; a++)
            for (int b = 0; b < d_; b++) addE(a, d_ + b);
    }
    if (bad_pairs() == 0) save_best();
    else {
        /* Start is invalid: reset to K_{d,d} which is valid for D >= 2. */
        N = 2 * d_;
        for (int v = 0; v < N; v++) { deg[v] = 0; side[v] = v >= d_; }
        for (int a = 0; a < d_; a++)
            for (int b = 0; b < d_; b++) addE(a, d_ + b);
        bad_pairs();
        save_best();
    }

    double phase_end = t0 + limit * 0.85;
    if (mode == 1) {
        grow_search(phase_end);
    } else {
        anneal(limit * 0.6, t0, grow_max);
        /* Restore last valid best before growing from it. */
        if (best_n > 0) {
            N = best_n;
            for (int v = 0; v < N; v++) { deg[v] = 0; side[v] = v >= (N / 2) ? 1 : 0; }
            int m = 0;
            (void)m;
        }
    }

    if (best_n == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestEu[i], bestEv[i]);
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


def _bipartition(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add vertices using spare degree; returns a valid (n, edges)."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                cand = edges + [(v, n) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (Python annealer).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
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
# Driver.
# ----------------------------------------------------------------------------

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
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass

    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    # Phase 1 (Python): bi-Cayley lift search, bandit over base sizes k.
    if D >= 2:
        trials = {k: 0 for k in _KS}
        wins = {k: 0 for k in _KS}

        def pick_k():
            if rng.random() < 0.2:
                return rng.choice(_KS)
            return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

        py_end = t0 + usable * 0.35
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

    # Phase 2 (Python): greedy slack extension.
    slack_end = t0 + usable * 0.45
    if time.monotonic() < slack_end:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, slack_end)
        consider(n2, e2)

    # Phase 3 (C): edge-toggle annealing with growth, then grow-by-two repair.
    c_budget = end - time.monotonic() - 0.5
    if c_budget > 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", 0],
                            stdin_graph=best, timeout=c_budget + 10.0)
            cn, ce = lib.parse_graph_text(out)
            consider(cn, ce)
        except (RuntimeError, ValueError):
            pass

    rem = end - time.monotonic() - 0.5
    if rem > 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed + 1, f"{rem:.2f}", 1],
                            stdin_graph=best, timeout=rem + 10.0)
            cn, ce = lib.parse_graph_text(out)
            consider(cn, ce)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
