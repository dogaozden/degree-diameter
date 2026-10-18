"""Bi-Cayley lift search with a C annealing engine and a ratcheted group order.

New in this version (relative to the parent):
  * The annealing over semidirect-product bi-Cayley lifts runs in C. Each move rebuilds
    only the one layer it touched, and reachability is evaluated on the accepted state.
  * Ratchet: every valid lift raises the threshold, so the next trial samples a group
    order just above the new record instead of the old one.
  * Araujo-Pardo-Lopez seeding: for d-2 a prime power, the record graph is the starting
    threshold for D = 3 and up.
  * The pure-Python annealer from the parent is kept as a fallback if the C engine fails.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 4
#define PEN 1000L

static int d_, D_;
static double deadline_;
static uint64_t rs_ = 88172645463325252ULL;
static int pcount[256];

static uint64_t xr(void) { rs_ ^= rs_ << 13; rs_ ^= rs_ >> 7; rs_ ^= rs_ << 17; return rs_; }
static int rnd(int n) { return (int)(xr() % (uint64_t)n); }
static double rndu(void) { return (double)(xr() >> 11) * (1.0 / 9007199254740992.0); }
static double wall_now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

/* ---- group Z_m x| Z_k2, element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e) ---- */
static int gm, gk2, gG;
static long long gpw[64];

static int gmul(int x, int y) {
    int a = x / gk2, b = x % gk2, c = y / gk2, e = y % gk2;
    long long t = ((long long)a + gpw[b] * (long long)c) % gm;
    return (int)(t * gk2 + (b + e) % gk2);
}

static int ginv(int x) {
    int a = x / gk2, b = x % gk2;
    int nb = (gk2 - b) % gk2;
    long long c = (gpw[nb] * (long long)a) % gm;
    c = (gm - c) % gm;
    return (int)(c * gk2 + nb);
}

static void set_group(int m, int k2, int r) {
    gm = m; gk2 = k2; gG = m * k2;
    long long p = 1 % m;
    for (int t = 0; t < k2; t++) {
        gpw[t] = p;
        p = (p * r) % m;
    }
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long long gcdll(long long a, long long b) {
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

static int sample_group(int target, int *om, int *ok2, int *orr) {
    static const int K2[20] = {1,1,2,2,3,4,5,6,7,8,9,10,12,14,16,18,20,24,30,36};
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2[rnd(20)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = -1;
        if (k2 == 1 || m <= 2) {
            r = 1;
        } else if (k2 == 2 && rndu() < 0.3) {
            r = m - 1;
        } else {
            for (int t = 0; t < 60 && r < 0; t++) {
                int c = 2 + rnd(m - 2);
                if (gcdll(c, m) == 1 && powmod(c, k2, m) == 1 % m) r = c;
            }
            if (r < 0) continue;
        }
        *om = m; *ok2 = k2; *orr = r;
        return 1;
    }
    return 0;
}

/* ---- lift state ---- */
static int cK, cN;
static int lay[MAXD][MAXK];
static int Sv[MAXD][MAXK];
static int *nbr = NULL;                 /* nbr[l*cN + v] */
static uint16_t *rA = NULL, *rB = NULL, *curR = NULL, *lastR = NULL;

/* Rebuild only layer l. A-block i is joined to B-block lay[l][i] with voltage Sv[l][i]. */
static void build_layer(int l) {
    int k = cK, G = gG, N = cN;
    int *nb = nbr + (size_t)l * (size_t)N;
    int lp[MAXK];
    for (int i = 0; i < k; i++) lp[lay[l][i]] = i;
    for (int i = 0; i < k; i++) {
        int j = lay[l][i], s = Sv[l][i];
        for (int g = 0; g < G; g++) nb[i * G + g] = (k + j) * G + gmul(g, s);
    }
    for (int j = 0; j < k; j++) {
        int i = lp[j];
        int si = ginv(Sv[l][i]);
        for (int h = 0; h < G; h++) nb[(k + j) * G + h] = i * G + gmul(h, si);
    }
}

/* Reach bitmasks, then cost = unreached (rep, vertex) pairs + PEN * duplicate darts. */
static long eval_cost(void) {
    int k = cK, N = cN, G = gG;
    uint16_t *cur = rA, *nxt = rB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * k; b++) cur[b * G] = (uint16_t)(1u << b);
    for (int t = 0; t < D_; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint16_t x = cur[v];
            for (int l = 0; l < d_; l++) x |= cur[nbr[(size_t)l * N + v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint16_t *tmp = cur; cur = nxt; nxt = tmp;
        if (!changed) break;
    }
    lastR = cur;
    long unreached = (long)2 * k * N;
    for (int v = 0; v < N; v++) unreached -= pcount[cur[v]];

    long long keys[MAXD * MAXK];
    int nk = 0;
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < k; i++)
            keys[nk++] = ((long long)i * k + lay[l][i]) * G + Sv[l][i];
    long dup = 0;
    for (int a = 0; a < nk; a++)
        for (int b = a + 1; b < nk; b++)
            if (keys[a] == keys[b]) dup++;
    return unreached + PEN * dup;
}

static int anneal(int iters, int patience) {
    int k = cK, N = cN, G = gG;
    int full = (1 << (2 * k)) - 1;
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k; i++) lay[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rnd(i + 1);
            int t = lay[l][i]; lay[l][i] = lay[l][j]; lay[l][j] = t;
        }
        for (int i = 0; i < k; i++) Sv[l][i] = rnd(G);
        build_layer(l);
    }
    long cost = eval_cost();
    memcpy(curR, lastR, sizeof(uint16_t) * (size_t)N);
    long c0 = cost > 1 ? cost : 1;
    long best = cost;
    int last = 0;

    for (int t = 0; t < iters && cost != 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && wall_now() > deadline_) break;
        double temp = 0.01 * (double)c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        int savL[MAXD][MAXK], savS[MAXD][MAXK];
        memcpy(savL, lay, sizeof lay);
        memcpy(savS, Sv, sizeof Sv);

        int l = 0, i = 0;
        if (k >= 2 && rndu() < 0.25) {
            /* layer swap: exchange the B-targets of two A-blocks in one layer */
            l = rnd(d_);
            int i1 = rnd(k), i2 = rnd(k - 1);
            if (i2 >= i1) i2++;
            int tt = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = tt;
            build_layer(l);
        } else {
            /* voltage move; with prob 0.4 aim at a vertex that is not yet fully reached */
            int u = -1;
            if (rndu() < 0.4) {
                for (int tr = 0; tr < 50; tr++) {
                    int v = rnd(N);
                    if (curR[v] != full) { u = v; break; }
                }
            }
            if (u >= 0) {
                int block = u / G;
                l = rnd(d_);
                if (block < k) {
                    i = block;
                } else {
                    i = 0;
                    for (int q = 0; q < k; q++)
                        if (lay[l][q] == block - k) { i = q; break; }
                }
            } else {
                l = rnd(d_);
                i = rnd(k);
            }
            int s = rnd(G);
            if (s == Sv[l][i]) continue;
            Sv[l][i] = s;
            build_layer(l);
        }

        long c2 = eval_cost();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(curR, lastR, sizeof(uint16_t) * (size_t)N);
            if (cost < best) { best = cost; last = t; }
        } else {
            memcpy(lay, savL, sizeof lay);
            memcpy(Sv, savS, sizeof Sv);
            build_layer(l);
        }
    }
    return cost == 0;
}

static int *bestE = NULL;
static int bestEcnt = 0;
static int bestN = 0;

static void save_graph(void) {
    int k = cK, G = gG, N = cN;
    int E = k * G * d_;
    int *buf = malloc(sizeof(int) * 2 * (size_t)E);
    int c = 0;
    for (int u = 0; u < k * G; u++)
        for (int l = 0; l < d_; l++) {
            buf[2 * c] = u;
            buf[2 * c + 1] = nbr[(size_t)l * N + u];
            c++;
        }
    free(bestE);
    bestE = buf;
    bestEcnt = E;
    bestN = N;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs_ ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs_ == 0) rs_ = 1;
    for (int i = 0; i < 20; i++) xr();
    for (int v = 0; v < 256; v++) {
        int c = 0;
        for (int x = v; x; x >>= 1) c += x & 1;
        pcount[v] = c;
    }

    long n0 = 0, m0 = 0;
    if (scanf("%ld %ld", &n0, &m0) != 2) n0 = 0;
    {
        int ch;
        while ((ch = getchar()) != EOF) { }
    }
    int thr = (int)n0;
    if (d_ < 3 || d_ > MAXD || D_ < 3) {
        printf("0 0\n");
        return 0;
    }

    deadline_ = wall_now() + tl;
    double trials[MAXK + 1] = {0}, wins[MAXK + 1] = {0};

    while (wall_now() < deadline_) {
        int k = 1;
        if (rndu() < 0.2) {
            k = 1 + rnd(MAXK);
        } else {
            double bv = -1.0;
            for (int kk = 1; kk <= MAXK; kk++) {
                double v = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rndu();
                if (v > bv) { bv = v; k = kk; }
            }
        }
        int base = thr / (2 * k);
        int target = base + 1 + rnd(base / 8 + 2);
        if (target < 2) target = 2;
        int m, k2, r;
        if (!sample_group(target, &m, &k2, &r)) continue;
        set_group(m, k2, r);
        int N = 2 * k * gG;
        if (N <= thr) continue;

        cK = k;
        cN = N;
        nbr = malloc(sizeof(int) * (size_t)d_ * (size_t)N);
        rA = malloc(sizeof(uint16_t) * (size_t)N);
        rB = malloc(sizeof(uint16_t) * (size_t)N);
        curR = malloc(sizeof(uint16_t) * (size_t)N);
        lastR = NULL;

        trials[k] += 1.0;
        int ok = anneal(4000, 1200);
        if (ok) {
            wins[k] += 1.0;
            save_graph();
            thr = N;   /* ratchet: the next groups must beat this */
        }
        free(nbr); free(rA); free(rB); free(curR);
        nbr = NULL; rA = rB = curR = lastR = NULL;
    }

    if (bestE) {
        printf("%d %d\n", bestN, bestEcnt);
        for (int e = 0; e < bestEcnt; e++)
            printf("%d %d\n", bestE[2 * e], bestE[2 * e + 1]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and fallback search.
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
    """Python simulated annealing (fallback). Returns (n, edges) or None."""
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
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        return 2 * D, [(i, (i + 1) % (2 * D)) for i in range(2 * D)]

    # Safe baseline: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Exact or known constructions. The Araujo-Pardo-Lopez graph is the threshold
    # the C ratchet starts from.
    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])
        if D == 3 and lib.is_prime_power(d - 1):
            return best
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    if D == 4 and time.monotonic() - t0 < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: C engine with the ratchet.
    c_deadline = t0 + min(0.85 * time_limit, time_limit - 8.0)
    cbudget = c_deadline - time.monotonic()
    c_ok = False
    if cbudget >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(cbudget, 2)],
                            stdin_graph=best, timeout=cbudget + 5.0)
            consider(*lib.parse_graph_text(out))
            c_ok = True
        except Exception:
            c_ok = False

    # Fallback: pure-Python annealing, used only if the C engine failed.
    if not c_ok:
        rng = random.Random(seed)
        deadline = t0 + min(0.85 * time_limit, time_limit - 6.0)
        trials = {k: 0 for k in _KS}
        wins = {k: 0 for k in _KS}

        def pick_k():
            if rng.random() < 0.2:
                return rng.choice(_KS)
            return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

        while time.monotonic() < deadline:
            k = pick_k()
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
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
