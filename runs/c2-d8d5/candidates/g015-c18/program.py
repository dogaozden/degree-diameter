import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine. One binary with two modes, chosen by argv[5]:
#
#   mode 0 (grow): edge-toggle annealer with vertex-pair growth. Starts from a
#     valid graph (or repairs an invalid one) and adds vertex pairs whenever
#     the bad-pair cost reaches zero. Same as before.
#
#   mode 1 (signed 2-lift): NEW. The input graph H (n vertices, max degree d,
#     diameter <= D) is doubled: every vertex v gets a copy v+n on the same
#     side, and every base edge (u,v) is lifted either "straight"
#     (u-v, u'-v') or "crossed" (u-v', u'-v). The lift has 2n vertices, keeps
#     the degree and stays bipartite. The annealer flips signs of base edges
#     and minimises the number of ordered vertex pairs at distance > D. Moves
#     are biased toward base edges incident to vertices that still have bad
#     pairs. The first sign pattern with zero cost is printed as the lift.
#
# The lift doubles the order at once, so it can reach sizes the vertex-pair
# growth cannot. Python decides which mode to use and whether to keep the result.
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

static int d_, D_, N, cap_n, cap_w;
static int *deg, *adj, *side, *bestEu, *bestEv;
static u64 *bufA, *bufB;
static int best_n = 0, best_m = 0;

/* lift state (mode 1) */
static int nb_, mb_;
static int *eu_, *ev_, *sg_, *inc_, *incN_;

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

/* out[v] = number of vertices at distance > D_ from v. Returns the sum. */
static long long bad_pairs(int *out) {
    u64 *cur = bufA, *alt = bufB;
    int W = (N + 63) / 64;
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
    long long total = 0;
    for (int v = 0; v < N; v++) {
        u64 *r = cur + (size_t)v * cap_w;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += __builtin_popcountll(r[w]);
        out[v] = N - pc;
        total += out[v];
    }
    return total;
}

/* ---- mode 0 helpers ---- */
static int pick_vertex(const int *bv) {
    if (rdbl() < 0.5) {
        for (int t = 0; t < 8; t++) {
            int v = rint_(N);
            if (bv[v] > 0) return v;
        }
    }
    return rint_(N);
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

static void grow_pair(void) {
    side[N] = 0; deg[N] = 0;
    side[N + 1] = 1; deg[N + 1] = 0;
    N += 2;
}

/* ---- mode 1 helpers: the two lift edges of base edge e under sign s ---- */
static void pair_of(int e, int s, int k, int *a, int *b) {
    int u = eu_[e], v = ev_[e];
    if (s == 0) {
        if (k == 0) { *a = u; *b = v; }
        else        { *a = u + nb_; *b = v + nb_; }
    } else {
        if (k == 0) { *a = u; *b = v + nb_; }
        else        { *a = u + nb_; *b = v; }
    }
}

static void set_sign(int e, int to) {
    int a, b;
    for (int k = 0; k < 2; k++) {
        pair_of(e, sg_[e], k, &a, &b);
        delE(a, b);
    }
    sg_[e] = to;
    for (int k = 0; k < 2; k++) {
        pair_of(e, to, k, &a, &b);
        addE(a, b);
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
    int grow_max = argc > 6 ? atoi(argv[6]) : 0;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (d_ < 1 || D_ < 1 || n0 < 2 || n0 > 1000000 || grow_max < 0 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    cap_n = 2 * n0 + 2 * grow_max + 4;
    cap_w = (cap_n + 63) / 64;
    deg = calloc(cap_n, sizeof(int));
    adj = malloc(sizeof(int) * (size_t)cap_n * d_);
    side = malloc(sizeof(int) * (size_t)cap_n);
    bestEu = malloc(sizeof(int) * (size_t)cap_n * d_);
    bestEv = malloc(sizeof(int) * (size_t)cap_n * d_);
    bufA = malloc(sizeof(u64) * (size_t)cap_n * cap_w);
    bufB = malloc(sizeof(u64) * (size_t)cap_n * cap_w);
    int *bvCur = malloc(sizeof(int) * (size_t)cap_n);
    int *bvNew = malloc(sizeof(int) * (size_t)cap_n);
    int *q = malloc(sizeof(int) * (size_t)cap_n);
    if (!deg || !adj || !side || !bestEu || !bestEv || !bufA || !bufB || !bvCur || !bvNew || !q) {
        printf("0 0\n");
        return 0;
    }

    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (deg[u] >= d_ || deg[v] >= d_ || isadj(u, v)) continue;
        addE(u, v);
    }

    /* ================= mode 1: signed 2-lift annealing ================= */
    if (mode == 1) {
        int nb = N;
        int *eu = malloc(sizeof(int) * (size_t)(nb * d_ + 1));
        int *ev = malloc(sizeof(int) * (size_t)(nb * d_ + 1));
        int *sg = malloc(sizeof(int) * (size_t)(nb * d_ + 1));
        int *inc = malloc(sizeof(int) * (size_t)(nb * d_ + 1));
        int *incN = calloc((size_t)nb, sizeof(int));
        if (!eu || !ev || !sg || !inc || !incN) { printf("0 0\n"); return 0; }
        int mb = 0;
        for (int v = 0; v < nb; v++) {
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v * d_ + i];
                if (u > v) { eu[mb] = v; ev[mb] = u; mb++; }
            }
        }
        if (mb == 0) { printf("0 0\n"); return 0; }
        for (int e = 0; e < mb; e++) {
            inc[eu[e] * d_ + incN[eu[e]]++] = e;
            inc[ev[e] * d_ + incN[ev[e]]++] = e;
        }
        nb_ = nb; mb_ = mb;
        eu_ = eu; ev_ = ev; sg_ = sg; inc_ = inc; incN_ = incN;

        N = 2 * nb;
        memset(deg, 0, sizeof(int) * (size_t)cap_n);
        for (int e = 0; e < mb; e++) {
            sg[e] = rint_(2);
            for (int k = 0; k < 2; k++) {
                int a, b;
                pair_of(e, sg[e], k, &a, &b);
                addE(a, b);
            }
        }

        int *oc = malloc(sizeof(int) * (size_t)cap_n);
        int *on = malloc(sizeof(int) * (size_t)cap_n);
        if (!oc || !on) { printf("0 0\n"); return 0; }
        long long cost = bad_pairs(oc);
        int found = (cost == 0);
        clock_t c0 = clock();
        const double LT0 = 40.0, LT1 = 0.5;
        while (!found) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= limit) break;
            double Tt = LT0 * pow(LT1 / LT0, el / limit);
            int e = -1;
            if (rdbl() < 0.6) {
                for (int t = 0; t < 16 && e < 0; t++) {
                    int w = rint_(N);
                    if (oc[w] > 0) {
                        int b = w % nb;
                        if (incN[b] > 0) e = inc[b * d_ + rint_(incN[b])];
                    }
                }
            }
            if (e < 0) e = rint_(mb);
            int old = sg[e];
            set_sign(e, 1 - old);
            long long nc = bad_pairs(on);
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / Tt)) {
                cost = nc;
                int *tp = oc; oc = on; on = tp;
                if (cost == 0) found = 1;
            } else {
                set_sign(e, old);
            }
        }
        if (!found) { printf("0 0\n"); return 0; }
        printf("%d %d\n", N, 2 * mb);
        for (int e = 0; e < mb; e++) {
            for (int k = 0; k < 2; k++) {
                int a, b;
                pair_of(e, sg[e], k, &a, &b);
                printf("%d %d\n", a, b);
            }
        }
        return 0;
    }

    /* ================= mode 0: vertex-pair growth annealing ================= */
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
    long long cost = bad_pairs(bvCur);
    if (cost == 0 && N > best_n) {
        save_best();
        if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(bvCur); }
    }

    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double frac = el / limit;
        double T = T0 * pow(T1 / T0, frac);

        int a = -1, b = -1;
        for (int t = 0; t < 50; t++) {
            int x = pick_vertex(bvCur), y = pick_vertex(bvCur);
            if (x == y || side[x] == side[y] || isadj(x, y)) continue;
            a = x; b = y;
            break;
        }
        if (a < 0) continue;

        int xa = -1, xb = -1;
        if (deg[a] == d_) { xa = adj[a * d_ + rint_(deg[a])]; delE(a, xa); }
        if (deg[b] == d_) { xb = adj[b * d_ + rint_(deg[b])]; delE(b, xb); }
        addE(a, b);

        long long nc = bad_pairs(bvNew);
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
            int *tp = bvCur; bvCur = bvNew; bvNew = tp;
            if (cost == 0 && N > best_n) {
                save_best();
                if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(bvCur); }
            }
        } else {
            delE(a, b);
            if (xa >= 0) addE(a, xa);
            if (xb >= 0) addE(b, xb);
        }
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
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
    """2-colouring of the graph, or None if it is not bipartite."""
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


def _run_mode(n, edges, d, D, seconds, seed, mode, param):
    """Run the C engine in one mode; returns the parsed (n, edges) (may be (0, []))."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}", mode, param],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    return _run_mode(n, edges, d, D, seconds, seed, 0, grow_max)


def _lift_in_c(n, edges, d, D, seconds, seed):
    return _run_mode(n, edges, d, D, seconds, seed, 1, 0)


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (Python annealer).
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
    T = float(time_limit)
    rng = random.Random(seed)

    def left():
        return T - (time.monotonic() - t0)

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

    # Half-size base for the signed 2-lift. The record order is about 0.3 * Moore,
    # so a base of about 0.15 * Moore lifts to roughly the record order.
    half = max(16, int(0.15 * lib.moore_bound(d, D)))

    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    def py_search(end, cap):
        """Bi-Cayley annealing until time `end` or the best order reaches `cap`."""
        nonlocal best
        while time.monotonic() < end and best[0] < cap:
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
            res = _search(d, D, k, G, Ts, Invs, rng, end, 4000, 1200)
            if res is not None:
                wins[k] += 1
                consider(res[0], res[1])

    # Phase 1: Python search up to a half-size base.
    py_search(t0 + 0.22 * T, half)

    # Phase 2: signed 2-lift of the base (doubles the order in one step).
    lifted = False
    if best[0] >= max(16, 0.6 * half):
        budget = t0 + 0.47 * T - time.monotonic()
        if budget >= 2.0:
            before = best[0]
            try:
                ln, le = _lift_in_c(best[0], best[1], d, D, budget, rng.randrange(1, 1 << 30))
                consider(ln, le)
            except Exception:
                pass  # keep the valid fallback
            lifted = best[0] > before

    # Phase 3: if the lift failed, keep the Python search going.
    if not lifted:
        py_search(t0 + 0.6 * T, 10 ** 18)

    # Phase 4: use spare degree in the current best graph.
    slack_end = t0 + 0.66 * T
    if time.monotonic() < slack_end - 1.0:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, slack_end)
        consider(n2, e2)

    # Phase 5: C annealer grows the best valid graph by vertex pairs.
    c_budget = left() - 5.0
    if c_budget >= 1.0:
        try:
            cn, ce = _grow_in_c(best[0], best[1], d, D, c_budget,
                                rng.randrange(1, 1 << 30), 200)
            consider(cn, ce)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
