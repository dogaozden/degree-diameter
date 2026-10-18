"""Bold variant: Python bi-Cayley lift search (warm start), then a C voltage annealer that
searches semidirect groups Z_m x| Z_k (order G) and K-block bi-Cayley lifts directly.

Each lift is d-regular by construction (every layer is a permutation of blocks with a group
voltage). Validity is checked exactly with a bitmask BFS from the 2K block representatives,
using left-translation symmetry of the lift. Every returned graph is checked with lib.is_valid,
and K_{d,d} (or a known construction) is the fallback.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


C_SOURCE = r'''
/* Bi-Cayley voltage-lift annealer over semidirect groups.
 * Usage: prog d D seed time_limit min_n [Kmax]
 * Output: "n m" plus edges of the largest valid lift found with n >= min_n (or "0 0").
 *
 * Lift: K blocks per side, A_i = block i, B_j = block K+j, each of order G = m*k2.
 * Layer l pairs A_i with B_{pi[l][i]} through voltage s: A_{i,g} ~ B_{pi,g*s}.
 * Group: (a,b)(c,e) = (a + r^b c, b+e) mod (m, k2), needs r^k2 = 1 mod m, gcd(r,m) = 1.
 * Validity: every vertex reaches every block representative within D steps (exact, by
 * left-translation symmetry). Dup pairs (same A block, same B block, same voltage) are penalised.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 40
#define MAXK 8
#define MAXG 40000
#define MAXN 80000
#define MAXC 65536
#define PEN 1000L

static int d, D;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* ---- semidirect group ---- */
static int gm, gk, gG;
static long rp[MAXG + 1];

static int gmul(int x, int y) {
    int a = x / gk, b = x - a * gk;
    int c = y / gk, e = y - c * gk;
    int t = (int)(((long)rp[b] * c + a) % gm);
    int f = b + e;
    if (f >= gk) f -= gk;
    return t * gk + f;
}

static int ginv(int x) {
    int a = x / gk, b = x - a * gk;
    int nb = (gk - b) % gk;
    int t = (int)(((long)rp[nb] * a) % gm);
    return ((gm - t) % gm) * gk + nb;
}

static void set_group(int m, int k2, int r) {
    gm = m;
    gk = k2;
    gG = m * k2;
    rp[0] = 1 % m;
    for (int b = 1; b < k2; b++) rp[b] = rp[b - 1] * r % m;
}

/* Pick a random semidirect group of exactly order Gt. Returns 1 on success. */
static int pick_group(int Gt, int *om, int *ok, int *orr) {
    static int cm[MAXC], ck[MAXC], cr[MAXC];
    int cnt = 0;
    for (int k2 = 1; k2 <= Gt; k2++) {
        if (Gt % k2) continue;
        int m = Gt / k2;
        if (m < 2) continue;
        for (int r = 1; r < m; r++) {
            if (gcdi(r, m) != 1) continue;
            long p = 1 % m;
            for (int t = 0; t < k2; t++) p = p * r % m;
            if (p != 1 % m) continue;
            if (cnt < MAXC) { cm[cnt] = m; ck[cnt] = k2; cr[cnt] = r; cnt++; }
        }
    }
    if (!cnt) return 0;
    int c = rndint(cnt);
    *om = cm[c];
    *ok = ck[c];
    *orr = cr[c];
    return 1;
}

/* ---- lift state ---- */
static int K, G, N;
static int piL[MAXD][MAXK], svL[MAXD][MAXK], svi[MAXD][MAXK];
static int *nbr = NULL;
static size_t ncap = 0;
static uint64_t *RA = NULL, *RB = NULL, *lastR = NULL;
static size_t rcap = 0;

static int ensure(void) {
    size_t need = (size_t)d * N;
    if (need > ncap) {
        int *p = realloc(nbr, need * sizeof(int));
        if (!p) return 0;
        nbr = p;
        ncap = need;
    }
    if ((size_t)N > rcap) {
        uint64_t *a = realloc(RA, (size_t)N * sizeof(uint64_t));
        if (!a) return 0;
        RA = a;
        uint64_t *b = realloc(RB, (size_t)N * sizeof(uint64_t));
        if (!b) return 0;
        RB = b;
        rcap = (size_t)N;
    }
    return 1;
}

static void set_vol(int l, int i, int s) {
    svL[l][i] = s;
    svi[l][i] = ginv(s);
}

/* Rewrite the neighbours of A block i and of its partner B block in layer l. */
static void set_pair(int l, int i) {
    int p = piL[l][i], s = svL[l][i], si = svi[l][i];
    int *nb = nbr + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        nb[i * G + g] = (K + p) * G + gmul(g, s);
        nb[(K + p) * G + g] = i * G + gmul(g, si);
    }
}

static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (piL[l][i] == piL[l2][i] && svL[l][i] == svL[l2][i]) c++;
    return c;
}

/* Sum over vertices of unreached block representatives (0 means valid). */
static long full_cost(void) {
    int T2 = 2 * K;
    uint64_t *cur = RA, *nxt = RB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < T2; b++) cur[(size_t)b * G] = 1ULL << b;
    for (int r = 0; r < D; r++) {
        memcpy(nxt, cur, sizeof(uint64_t) * (size_t)N);
        for (int l = 0; l < d; l++) {
            const int *nb = nbr + (size_t)l * N;
            for (int v = 0; v < N; v++) nxt[v] |= cur[nb[v]];
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    uint64_t full = (1ULL << T2) - 1;
    long c = 0;
    for (int v = 0; v < N; v++) c += T2 - __builtin_popcountll(cur[v] & full);
    lastR = cur;
    return c;
}

static int anneal(double tend, long patience) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) piL[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = piL[l][i];
            piL[l][i] = piL[l][j];
            piL[l][j] = tmp;
        }
        for (int i = 0; i < K; i++) set_vol(l, i, rndint(G));
        for (int i = 0; i < K; i++) set_pair(l, i);
    }
    long cost = full_cost() + PEN * dupcount();
    double T0 = 0.02 * (double)(cost > 0 ? cost : 1);
    if (T0 < 1.0) T0 = 1.0;
    long best = cost, last = 0;

    for (long t = 0; cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 15) == 0 && now() > tend) break;
        double T = 0.3 + T0 * pow(0.998, (double)t);

        if (K >= 2 && rnd01() < 0.2) {
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = piL[l][i1];
            piL[l][i1] = piL[l][i2];
            piL[l][i2] = tmp;
            set_pair(l, i1);
            set_pair(l, i2);
            long nc = full_cost() + PEN * dupcount();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                tmp = piL[l][i1];
                piL[l][i1] = piL[l][i2];
                piL[l][i2] = tmp;
                set_pair(l, i1);
                set_pair(l, i2);
            }
        } else {
            int l = -1, i = -1, v = -1;
            if (rnd01() < 0.5) {
                for (int tr = 0; tr < 40; tr++) {
                    int u = rndint(N);
                    if (__builtin_popcountll(lastR[u]) < 2 * K) { v = u; break; }
                }
            }
            if (v >= 0) {
                l = rndint(d);
                if (v < K * G) {
                    i = v / G;
                } else {
                    int j = v / G - K;
                    for (int ii = 0; ii < K; ii++)
                        if (piL[l][ii] == j) { i = ii; break; }
                }
            } else {
                l = rndint(d);
                i = rndint(K);
            }
            if (l < 0 || i < 0) continue;
            int old = svL[l][i];
            int nv = rndint(G);
            if (nv != old) {
                set_vol(l, i, nv);
                set_pair(l, i);
                long nc = full_cost() + PEN * dupcount();
                if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                    cost = nc;
                } else {
                    set_vol(l, i, old);
                    set_pair(l, i);
                }
            }
        }
        if (cost < best) { best = cost; last = t; }
    }
    return cost == 0;
}

/* Best valid graph so far (edge arrays). */
static int *bu = NULL, *bv = NULL;
static long bm = 0;
static int best_n = 0;

static int record(void) {
    long m = (long)d * K * G;
    int *eu = malloc(sizeof(int) * (size_t)m);
    int *ev = malloc(sizeof(int) * (size_t)m);
    if (!eu || !ev) { free(eu); free(ev); return 0; }
    long c = 0;
    for (int v = 0; v < K * G; v++)
        for (int l = 0; l < d; l++) {
            eu[c] = v;
            ev[c] = nbr[(size_t)l * N + v];
            c++;
        }
    free(bu);
    free(bv);
    bu = eu;
    bv = ev;
    bm = m;
    best_n = 2 * K * G;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long minN = atol(argv[5]);
    int Kmax = argc > 6 ? atoi(argv[6]) : 3;
    if (Kmax < 1) Kmax = 1;
    if (Kmax > MAXK) Kmax = MAXK;
    if (d < 3 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }

    double t0 = now();
    double t_end = t0 + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    long goal = minN < 4 ? 4 : minN;
    while (now() < t_end) {
        int Kc = 1 + rndint(Kmax);
        long Glo = (goal + 2L * Kc - 1) / (2L * Kc);
        if (Glo < 2) Glo = 2;
        long span = Glo / 60 + 2;
        long Gc = Glo + rndint((int)span);
        if (2L * Kc * Gc > MAXN || Gc > MAXG) break;

        int gm_, gk_, gr_;
        if (!pick_group((int)Gc, &gm_, &gk_, &gr_)) continue;
        set_group(gm_, gk_, gr_);
        K = Kc;
        G = (int)Gc;
        N = 2 * K * G;
        if (!ensure()) break;

        double rem = t_end - now();
        if (rem < 0.2) break;
        double slice = rem * 0.12;
        if (slice < 1.5) slice = 1.5;
        if (slice > rem) slice = rem;

        if (anneal(now() + slice, 4000)) {
            long nn = 2L * K * G;
            if (nn > best_n) {
                if (dupcount() == 0 && full_cost() == 0) record();
            }
            if (best_n + 1 > goal) goal = best_n + 1;
        }
    }

    if (best_n > 0 && bu && bv) {
        printf("%d %ld\n", best_n, bm);
        for (long e = 0; e < bm; e++) printf("%d %d\n", bu[e], bv[e]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


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
# Saturation: greedily add missing bipartite edges between deficient vertices.
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
# Python bi-Cayley lifts over semidirect products (warm start).
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

    # Phase 1: Python bi-Cayley lift search (warm start), bandit over base sizes k.
    lift_deadline = t0 + 0.35 * total
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    goal = float(best_n) * 1.05

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < lift_deadline:
        k = pick_k()
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
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, lift_deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider_saturated(res[0], res[1])
            goal = max(goal, best_n * 1.04)
        else:
            goal = max(float(best_n) * 1.02, goal * 0.99)

    # Phase 2: C voltage annealer over semidirect groups, aiming above the current best.
    remaining = final - time.monotonic() - 1.0
    if d >= 3 and D >= 3 and remaining > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), best_n + 1, 3],
                             timeout=remaining + 15)
            n2, e2 = lib.parse_graph_text(text)
            consider_saturated(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
