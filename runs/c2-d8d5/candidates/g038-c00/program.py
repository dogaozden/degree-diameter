import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts of bipartite base graphs over semidirect products
# Z_m x| Z_k2. Each base layer l is a permutation perm_l of K base vertices
# per side, with voltage sv[l][i] on the dart from A_i to B_perm_l(i).
# Left multiplication by the group is an automorphism of the lift, so the
# diameter check only needs BFS from the 2K block identities. Cost = number
# of (source, vertex) pairs at distance > D, plus a penalty for multi-edges.
# Annealing over voltages and layer permutations, with group orders climbing
# above the best order found so far.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef unsigned long long u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

#define MAXG 2048
#define MAXK 4
#define MAXD 16
#define MAXN (2 * MAXK * MAXG)
#define MAXGROUPS 20000
#define KMAXGROUP 40
#define ITERS 20000
#define PATIENCE 5000

typedef struct { int m, k2, r; } GrpSpec;

static GrpSpec *gl = NULL;
static int ng = 0;

static int D_, d_, K_, G_, M_, K2_, R_;
static int pw_[64];
static int *mulT = NULL;
static int invT[MAXG];
static int perm_[MAXD][MAXK];
static int sv_[MAXD][MAXK];
static int adjv_[MAXN * MAXD];
static int dist_[MAXN];
static int q_[MAXN];
static clock_t c0_;
static int bperm_[MAXD][MAXK], bsv_[MAXD][MAXK];

static double elapsed(void) { return (double)(clock() - c0_) / CLOCKS_PER_SEC; }

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int powmod_(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* (a,b)*(c,e) = (a + r^b c, b + e) with element index a*k2 + b. */
static int gmul_(int m, int k2, const int *pw, int x, int y) {
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    int aa = (int)(((long long)a + (long long)pw[b] * c) % m);
    return aa * k2 + (b + e) % k2;
}

static void find_groups(int gmin, int gmax) {
    ng = 0;
    for (int k2 = 1; k2 <= KMAXGROUP; k2++) {
        int mlo = (gmin + k2 - 1) / k2;
        if (mlo < 1) mlo = 1;
        int mhi = gmax / k2;
        for (int m = mlo; m <= mhi; m++) {
            int G = m * k2;
            if (G < gmin || G > gmax) continue;
            if (k2 == 1) {
                if (ng < MAXGROUPS) { gl[ng].m = m; gl[ng].k2 = 1; gl[ng].r = 1 % m; ng++; }
                continue;
            }
            for (int r = 1; r < m; r++) {
                if (gcd_(r, m) != 1) continue;
                if (powmod_(r, k2, m) != 1 % m) continue;
                if (ng < MAXGROUPS) { gl[ng].m = m; gl[ng].k2 = k2; gl[ng].r = r; ng++; }
            }
        }
    }
}

static void setup_group(int m, int k2, int r) {
    M_ = m; K2_ = k2; R_ = r; G_ = m * k2;
    pw_[0] = 1 % m;
    for (int t = 1; t < k2; t++) pw_[t] = (int)((long long)pw_[t - 1] * r % m);
    for (int x = 0; x < G_; x++)
        for (int y = 0; y < G_; y++)
            mulT[x * G_ + y] = gmul_(m, k2, pw_, x, y);
    for (int x = 0; x < G_; x++) {
        int a = x / k2, b = x % k2;
        int nb = (k2 - b) % k2;
        int ia = (int)((m - ((long long)pw_[nb] * a) % m) % m);
        invT[x] = ia * k2 + nb;
    }
}

/* Cost = unreached (source, vertex) pairs over all 2K block identities,
   plus a penalty per duplicated dart (same target block and voltage). */
static long long eval_cost(void) {
    int K = K_, G = G_, d = d_, D = D_;
    int N = 2 * K * G;
    int pinv[MAXD][MAXK];
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) pinv[l][perm_[l][i]] = i;
    for (int i = 0; i < K; i++)
        for (int g = 0; g < G; g++) {
            int v = i * G + g;
            for (int l = 0; l < d; l++) {
                int j = perm_[l][i];
                adjv_[v * d + l] = (K + j) * G + mulT[g * G + sv_[l][i]];
            }
        }
    for (int j = 0; j < K; j++)
        for (int h = 0; h < G; h++) {
            int v = (K + j) * G + h;
            for (int l = 0; l < d; l++) {
                int i = pinv[l][j];
                adjv_[v * d + l] = i * G + mulT[h * G + invT[sv_[l][i]]];
            }
        }
    long long cost = 0;
    for (int src = 0; src < 2 * K; src++) {
        int s = src * G;
        memset(dist_, -1, sizeof(int) * (size_t)N);
        int head = 0, tail = 0;
        dist_[s] = 0;
        q_[tail++] = s;
        while (head < tail) {
            int v = q_[head++];
            if (dist_[v] >= D) continue;
            for (int l = 0; l < d; l++) {
                int u = adjv_[v * d + l];
                if (dist_[u] < 0) {
                    dist_[u] = dist_[v] + 1;
                    q_[tail++] = u;
                }
            }
        }
        cost += N - tail;
    }
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm_[l1][i] == perm_[l2][i] && sv_[l1][i] == sv_[l2][i])
                    cost += N;
    return cost;
}

static int anneal(double limit) {
    int K = K_, G = G_, d = d_;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm_[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm_[l][i]; perm_[l][i] = perm_[l][j]; perm_[l][j] = t;
        }
        for (int i = 0; i < K; i++) sv_[l][i] = rint_(G);
    }
    long long cost = eval_cost();
    double T0 = 2.0 + 0.05 * (double)cost;
    const double T1 = 0.3;
    long long best = cost;
    int last_imp = 0;
    for (int t = 0; t < ITERS && cost > 0; t++) {
        if ((t & 31) == 0 && elapsed() >= limit) break;
        if (t - last_imp > PATIENCE) break;
        double temp = T0 * pow(T1 / T0, (double)t / ITERS);
        int l = rint_(d);
        int i1 = rint_(K);
        int swapmode = (K >= 2 && rdbl() < 0.3);
        int i2 = 0, old = 0;
        if (swapmode) {
            i2 = rint_(K - 1);
            if (i2 >= i1) i2++;
            int tmp = perm_[l][i1]; perm_[l][i1] = perm_[l][i2]; perm_[l][i2] = tmp;
        } else {
            old = sv_[l][i1];
            int nv = rint_(G);
            if (G > 1) while (nv == old) nv = rint_(G);
            sv_[l][i1] = nv;
        }
        long long nc = eval_cost();
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / temp)) {
            cost = nc;
            if (cost < best) { best = cost; last_imp = t; }
        } else {
            if (swapmode) {
                int tmp = perm_[l][i1]; perm_[l][i1] = perm_[l][i2]; perm_[l][i2] = tmp;
            } else {
                sv_[l][i1] = old;
            }
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    int bar = atoi(argv[5]);
    { int ch; while ((ch = getchar()) != EOF) { } }
    if (d_ < 1 || d_ > MAXD || D_ < 1 || limit <= 0) { printf("0 0\n"); return 0; }
    if (bar < 0) bar = 0;
    gl = malloc(sizeof(GrpSpec) * MAXGROUPS);
    mulT = malloc(sizeof(int) * (size_t)MAXG * MAXG);
    if (!gl || !mulT) { printf("0 0\n"); return 0; }

    int found = 0, bK = 0, bG = 0, bM = 0, bK2 = 0, bR = 0;
    c0_ = clock();
    while (elapsed() < limit) {
        int K = 1 + rint_(MAXK);
        int gmin = bar / (2 * K) + 1;
        int span = 2 + rint_(6);
        int gmax = gmin + span;
        if (gmax > MAXG) gmax = MAXG;
        if (gmin > gmax) continue;
        K_ = K;
        find_groups(gmin, gmax);
        if (ng == 0) continue;
        GrpSpec gs = gl[rint_(ng)];
        setup_group(gs.m, gs.k2, gs.r);
        if (anneal(limit)) {
            int n = 2 * K_ * G_;
            if (n > bar) {
                bar = n;
                found = 1;
                bK = K_; bG = G_; bM = M_; bK2 = K2_; bR = R_;
                memcpy(bperm_, perm_, sizeof(perm_));
                memcpy(bsv_, sv_, sizeof(sv_));
            }
        }
    }

    if (!found) { printf("0 0\n"); return 0; }
    {
        int K = bK, G = bG, d = d_;
        int N = 2 * K * G;
        int pwb[64];
        pwb[0] = 1 % bM;
        for (int t = 1; t < bK2; t++) pwb[t] = (int)((long long)pwb[t - 1] * bR % bM);
        printf("%d %d\n", N, K * G * d);
        for (int i = 0; i < K; i++)
            for (int g = 0; g < G; g++)
                for (int l = 0; l < d; l++) {
                    int a = i * G + g;
                    int b = (K + bperm_[l][i]) * G + gmul_(bM, bK2, pwb, g, bsv_[l][i]);
                    printf("%d %d\n", a, b);
                }
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


def _c_lift(d, D, seed, seconds, bar):
    """Run the C voltage-lift search; returns (n, edges), possibly (0, [])."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}", bar],
                    stdin_graph=None, timeout=seconds + 10.0)
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

    # Phase A: C voltage-lift search over small groups, climbing in order.
    c_budget = 0.7 * time_limit - 2.0
    if c_budget >= 3.0 and d <= 16:
        try:
            cn, ce = _c_lift(d, D, rng.randrange(1, 1 << 30), c_budget, best[0])
            consider(cn, ce)
        except Exception:
            pass  # keep the valid fallback

    # Phase B: Python bi-Cayley annealing with the remaining time (hedge).
    py_end = t0 + max(1.0, time_limit - 8.0)
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

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

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
