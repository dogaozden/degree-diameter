"""Bi-Cayley lift search with representative-BFS cost, plus exact small constructions.

New helper: for a bi-Cayley lift over a group G, left multiplication by G is an automorphism
that is transitive on each block. So the lift has diameter <= D iff a BFS from the identity of
each of the 2k blocks reaches everything within D steps. The C annealer uses this cost
(about 2k BFS per move) instead of all-pairs bitsets, which makes moves far cheaper.

Python chooses the base size k and the semidirect group Z_m x| Z_k2 (order near the target),
and bisects in log-space between the best valid order and the Moore bound.
Every returned graph is checked with lib.is_valid; K_{d,d} is the fallback.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley lift annealer over the semidirect product Z_M x| Z_K2 (R^K2 = 1 mod M).
 * Usage: prog d D seed time_limit k M K2 R      (stdin is ignored)
 * Blocks: A-blocks 0..k-1, B-blocks k..2k-1, vertex = block*G + element, G = M*K2.
 * Layer l pairs A-block i with B-block lb[l][i] through voltage vol[l][i]:
 *   A_{i,g} ~ B_{p,g*s}.  Each layer is a permutation, so the graph is d-regular if no
 *   (i,p,s) repeats across layers.
 * Cost = sum over the 2k block identities of (vertices not reached within D)
 *        + penalty * duplicate darts.  Zero cost means a valid graph, because left
 *        multiplication by G is an automorphism that is transitive on each block.
 * stdout: "N M" and the A-side edges of the first valid lift found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 24000
#define MAXD 16
#define MAXK 16
#define MAXG 12000

static int d, D, K, M, K2, R, G, N;
static int pw[64];
static int lb[MAXD][MAXK];
static int vol[MAXD][MAXK];
static int nb[MAXV][MAXD];
static int seenm[MAXV];
static int stampc = 0;
static int qbuf[MAXV];
static uint64_t rs = 88172645463325252ULL;
static long PEN;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

/* Element x = a*K2 + b codes (a,b); product (a,b)(c,e) = (a + R^b c, b + e). */
static inline int gmul(int x, int y) {
    int a = x / K2, b = x - a * K2;
    int c = y / K2, e = y - c * K2;
    int s = b + e;
    if (s >= K2) s -= K2;
    long t = (long)a + (long)pw[b] * c;
    return (int)(t % M) * K2 + s;
}

static inline int ginv(int x) {
    int a = x / K2, b = x - a * K2;
    int nbb = (K2 - b) % K2;
    long t = (-((long)pw[nbb] * a)) % M;
    if (t < 0) t += M;
    return (int)t * K2 + nbb;
}

/* Rebuild neighbour table for layer l (A side and B side). */
static void rebuild_layer(int l) {
    for (int i = 0; i < K; i++) {
        int p = lb[l][i];
        int s = vol[l][i];
        int si = ginv(s);
        int ub = i * G, vb = (K + p) * G;
        for (int g = 0; g < G; g++) {
            nb[ub + g][l] = vb + gmul(g, s);
            nb[vb + g][l] = ub + gmul(g, si);
        }
    }
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (lb[l1][i] == lb[l2][i] && vol[l1][i] == vol[l2][i]) c++;
    return c;
}

/* Number of vertices not within distance D of src. */
static int bfs_unreached(int src) {
    stampc++;
    int head = 0, tail = 0;
    qbuf[tail++] = src;
    seenm[src] = stampc;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            int v = qbuf[head++];
            const int *row = nb[v];
            for (int l = 0; l < d; l++) {
                int u = row[l];
                if (seenm[u] != stampc) {
                    seenm[u] = stampc;
                    qbuf[tail++] = u;
                }
            }
        }
    }
    return N - tail;
}

static long evaluate(void) {
    long cost = 0;
    for (int b = 0; b < 2 * K; b++) cost += bfs_unreached(b * G);
    return cost + PEN * (long)dupcount();
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) lb[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = lb[l][i];
            lb[l][i] = lb[l][j];
            lb[l][j] = t;
        }
        for (int i = 0; i < K; i++) vol[l][i] = rndi(G);
        rebuild_layer(l);
    }
}

/* One annealing episode until time 'until'. Returns 1 when a valid lift is in the state. */
static int anneal(double until) {
    double st = now();
    double span = until - st;
    if (span <= 0) return 0;
    random_state();
    long cost = evaluate();
    const double T0 = 6.0, T1 = 0.3;
    double frac = 0.0;
    for (long it = 0; cost > 0; it++) {
        if ((it & 15) == 0) {
            double tn = now();
            if (tn >= until) break;
            frac = (tn - st) / span;
        }
        double T = T0 * pow(T1 / T0, frac);
        int l = rndi(d);
        if (K >= 2 && rnd01() < 0.3) {
            int i1 = rndi(K), i2 = rndi(K - 1);
            if (i2 >= i1) i2++;
            int t = lb[l][i1];
            lb[l][i1] = lb[l][i2];
            lb[l][i2] = t;
            rebuild_layer(l);
            long nc = evaluate();
            if (nc <= cost || rnd01() < exp((double)(cost - nc) / T)) {
                cost = nc;
            } else {
                t = lb[l][i1];
                lb[l][i1] = lb[l][i2];
                lb[l][i2] = t;
                rebuild_layer(l);
            }
        } else {
            int i = rndi(K);
            int old = vol[l][i];
            int nw = rndi(G);
            if (nw == old) continue;
            vol[l][i] = nw;
            rebuild_layer(l);
            long nc = evaluate();
            if (nc <= cost || rnd01() < exp((double)(cost - nc) / T)) {
                cost = nc;
            } else {
                vol[l][i] = old;
                rebuild_layer(l);
            }
        }
    }
    return cost == 0;
}

static void print_graph(void) {
    long m = (long)K * G * d;
    printf("%d %ld\n", N, m);
    for (int i = 0; i < K; i++)
        for (int g = 0; g < G; g++) {
            int u = i * G + g;
            for (int l = 0; l < d; l++) printf("%d %d\n", u, nb[u][l]);
        }
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: %s d D seed time k M K2 R\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    K = atoi(argv[5]);
    M = atoi(argv[6]);
    K2 = atoi(argv[7]);
    R = atoi(argv[8]);
    if (d < 1 || d > MAXD || D < 1 || K < 1 || K > MAXK || M < 1 || K2 < 1 || K2 > 63) {
        printf("0 0\n");
        return 0;
    }
    G = M * K2;
    if (G < 2 || G > MAXG || 2 * K * G > MAXV) {
        printf("0 0\n");
        return 0;
    }
    N = 2 * K * G;
    R %= M;
    if (R < 0) R += M;
    long p = 1 % M;
    for (int t = 0; t < K2; t++) {
        pw[t] = (int)p;
        p = (p * R) % M;
    }
    if (p != 1 % M) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();
    PEN = N;

    double t_end = now() + limit * 0.95 - 0.05;
    while (now() < t_end) {
        double ep = now() + 2.5;
        if (ep > t_end) ep = t_end;
        if (anneal(ep)) {
            print_graph();
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact small constructions.
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
# Semidirect group sampling.
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


_KS = (1, 2, 3, 4, 5, 6)
_MAX_N = 24000


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
            return True
        return False

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
            consider(*lib.araujo_lopez_graph(d - 2))
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

    # Lift search: bisection in log-space between the best valid order (lo)
    # and an optimistic bound (hi, starting at the Moore bound).
    lo = float(best_n)
    hi = float(lib.moore_bound(d, D))
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda kk: (wins[kk] + 1) / (trials[kk] + 2) + 0.02 * rng.random())

    lift_deadline = final - 1.0
    attempt = 0
    while time.monotonic() < lift_deadline - 1.0:
        if hi <= lo * 1.002:
            hi = lo * 1.03
        goal = math.sqrt(lo * hi) * rng.uniform(0.99, 1.01)
        goal = min(max(goal, lo * 1.001), hi)
        k = pick_k()
        target = max(2, math.ceil(goal / (2 * k)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G = m * k2
        if 2 * k * G > _MAX_N:
            continue
        slice_s = min(3.5, lift_deadline - time.monotonic())
        if slice_s < 1.0:
            break
        attempt += 1
        trials[k] += 1
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed * 7919 + attempt, round(slice_s, 2),
                                        k, m, k2, r],
                             stdin_graph=None, timeout=slice_s + 15)
            n, e = lib.parse_graph_text(text)
        except Exception:
            hi = min(hi, goal * 0.997)
            continue
        if n > 0 and consider(n, e):
            wins[k] += 1
            lo = max(lo, float(n))
        elif n > 0 and n <= best_n:
            wins[k] += 1
        else:
            hi = min(hi, goal * 0.997)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
