import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts of Z_m x| Z_k2.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h, G = m*k2.
# Layer l pairs A-block i with B-block lay[l][i] through voltage sv[l][i]:
#   A_{i,g} ~ B_{lay, g*s},  B_{j,h} ~ A_{i, h*s^-1} where lay[l][i] = j.
# Every layer is a permutation, so every vertex has degree d.
# Left translation is an automorphism, so distances from the 2k block
# representatives to all vertices decide the diameter.
#
# Moves: layer swap (k >= 2), defect-targeted voltage move, uniform voltage move.
# Cost = unreached (representative, vertex) pairs + PENALTY * duplicate darts.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PENALTY 1000

static int d, D, k, m, k2, G, N, full;
static int powr[64];
static int *lay, *sv, *nbr;
static uint8_t *curr, *newr, *pa, *pb;
static uint8_t pc[256];
static uint64_t rs = 1;

static uint64_t rng_next(void) {
    uint64_t x = rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rs = x;
    return x * 2685821657736338717ULL;
}

static int rnd(int n) { return (int)(rng_next() % (uint64_t)n); }

static double rndu(void) {
    return (double)(rng_next() >> 11) * (1.0 / 9007199254740992.0);
}

static int gmul(int x, int y) {
    int a = x / k2, b = x % k2;
    int c = y / k2, e = y % k2;
    int a2 = (int)(((int64_t)a + (int64_t)powr[b] * c) % m);
    int b2 = (b + e) % k2;
    return a2 * k2 + b2;
}

static int ginv(int s) {
    int a = s / k2, b = s % k2;
    int nb = (k2 - b) % k2;
    int64_t t = ((int64_t)powr[nb] * a) % m;
    int a2 = (int)((m - t) % m);
    return a2 * k2 + nb;
}

static void set_dart(int l, int i, int j, int s) {
    int is = ginv(s);
    int *row = nbr + (size_t)l * N;
    for (int g = 0; g < G; g++)
        row[i * G + g] = (k + j) * G + gmul(g, s);
    for (int h = 0; h < G; h++)
        row[(k + j) * G + h] = i * G + gmul(h, is);
}

static void compute_reach(void) {
    uint8_t *cur = pa, *nxt = pb;
    memset(cur, 0, (size_t)N);
    for (int b = 0; b < 2 * k; b++)
        cur[(size_t)b * G] = (uint8_t)(1u << b);
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint8_t x = cur[v];
            for (int l = 0; l < d; l++)
                x |= cur[nbr[(size_t)l * N + v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint8_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    memcpy(newr, cur, (size_t)N);
}

static int eval_cost(void) {
    compute_reach();
    long long unr = 0;
    for (int v = 0; v < N; v++)
        unr += 2 * k - pc[newr[v]];
    int n = d * k, dup = 0;
    for (int p = 0; p < n; p++) {
        int ip = p % k, jp = lay[p], sp = sv[p];
        for (int q = 0; q < p; q++) {
            if (q % k == ip && lay[q] == jp && sv[q] == sp) {
                dup++;
                break;
            }
        }
    }
    return (int)(unr + (long long)PENALTY * dup);
}

static void init_random(void) {
    for (int l = 0; l < d; l++) {
        int *L = lay + (size_t)l * k;
        for (int i = 0; i < k; i++) L[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rnd(i + 1);
            int tmp = L[i];
            L[i] = L[j];
            L[j] = tmp;
        }
    }
    for (int p = 0; p < d * k; p++) sv[p] = rnd(G);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++)
            set_dart(l, i, lay[l * k + i], sv[l * k + i]);
}

static int accept_move(int c2, int cost, double temp) {
    if (c2 <= cost) return 1;
    return rndu() < exp(-(double)(c2 - cost) / temp);
}

/* Returns 1 if a valid state was found (state left in lay/sv/nbr),
   0 if the iteration budget ran out, -1 if the clock deadline passed. */
static int anneal(long long iters, long long patience, clock_t deadline) {
    init_random();
    int cost = eval_cost();
    memcpy(curr, newr, (size_t)N);
    double c0 = cost > 1 ? (double)cost : 1.0;
    int best = cost;
    long long last = 0;

    for (long long t = 0; t < iters && cost != 0; t++) {
        if (t - last > patience) break;
        if ((t & 15) == 0 && clock() > deadline) return -1;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (k >= 2 && rndu() < 0.25) {
            int l = rnd(d);
            int i1 = rnd(k);
            int i2 = rnd(k - 1);
            if (i2 >= i1) i2++;
            int *L = lay + (size_t)l * k;
            int tmp = L[i1];
            L[i1] = L[i2];
            L[i2] = tmp;
            set_dart(l, i1, L[i1], sv[l * k + i1]);
            set_dart(l, i2, L[i2], sv[l * k + i2]);
            int c2 = eval_cost();
            if (accept_move(c2, cost, temp)) {
                cost = c2;
                memcpy(curr, newr, (size_t)N);
                if (cost < best) { best = cost; last = t; }
            } else {
                tmp = L[i1];
                L[i1] = L[i2];
                L[i2] = tmp;
                set_dart(l, i1, L[i1], sv[l * k + i1]);
                set_dart(l, i2, L[i2], sv[l * k + i2]);
            }
            continue;
        }

        int pick = -1;
        if (rndu() < 0.4) {
            int nbad = 0;
            for (int v = 0; v < N; v++) {
                if (curr[v] != full) {
                    nbad++;
                    if (rnd(nbad) == 0) pick = v;
                }
            }
        }
        int l, i;
        if (pick >= 0) {
            int block = pick / G;
            l = rnd(d);
            if (block < k) {
                i = block;
            } else {
                i = rnd(k);
                for (int ii = 0; ii < k; ii++) {
                    if (lay[l * k + ii] == block - k) { i = ii; break; }
                }
            }
        } else {
            l = rnd(d);
            i = rnd(k);
        }
        int p = l * k + i;
        int old = sv[p];
        int nw = rnd(G);
        if (nw == old) continue;
        sv[p] = nw;
        set_dart(l, i, lay[p], nw);
        int c2 = eval_cost();
        if (accept_move(c2, cost, temp)) {
            cost = c2;
            memcpy(curr, newr, (size_t)N);
            if (cost < best) { best = cost; last = t; }
        } else {
            sv[p] = old;
            set_dart(l, i, lay[p], old);
        }
    }
    return cost == 0 ? 1 : 0;
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    k = atoi(argv[3]);
    m = atoi(argv[4]);
    k2 = atoi(argv[5]);
    int r = atoi(argv[6]);
    unsigned long long seed = strtoull(argv[7], NULL, 10);
    double secs = atof(argv[8]);
    long long iters = argc > 9 ? atoll(argv[9]) : 12000;
    long long patience = argc > 10 ? atoll(argv[10]) : 3000;

    if (d < 1 || D < 1 || k < 1 || k > 4 || m < 2 || k2 < 1 || k2 > 64 || r < 0 || r >= m) {
        printf("0 0\n");
        return 0;
    }
    powr[0] = 1 % m;
    for (int t = 1; t < k2; t++)
        powr[t] = (int)((int64_t)powr[t - 1] * r % m);
    if ((int)((int64_t)powr[k2 - 1] * r % m) != 1 % m) {
        printf("0 0\n");
        return 0;
    }

    G = m * k2;
    N = 2 * k * G;
    full = (1 << (2 * k)) - 1;
    for (int x = 0; x < 256; x++) {
        int c = 0;
        for (int y = x; y; y >>= 1) c += y & 1;
        pc[x] = (uint8_t)c;
    }

    lay = malloc(sizeof(int) * (size_t)(d * k));
    sv = malloc(sizeof(int) * (size_t)(d * k));
    nbr = malloc(sizeof(int) * (size_t)d * (size_t)N);
    curr = malloc((size_t)N);
    newr = malloc((size_t)N);
    pa = malloc((size_t)N);
    pb = malloc((size_t)N);
    if (!lay || !sv || !nbr || !curr || !newr || !pa || !pb) {
        printf("0 0\n");
        return 0;
    }

    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;

    clock_t deadline = clock() + (clock_t)(secs * (double)CLOCKS_PER_SEC);
    int found = 0;
    while (clock() < deadline) {
        int res = anneal(iters, patience, deadline);
        if (res == 1) { found = 1; break; }
        if (res == -1) break;
    }

    if (found) {
        int M = k * G * d;
        printf("%d %d\n", N, M);
        for (int u = 0; u < k * G; u++)
            for (int l = 0; l < d; l++)
                printf("%d %d\n", u, nbr[(size_t)l * N + u]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""

_KS = (1, 2, 3, 4)
_SLICE = 2.5        # seconds per C call (C restarts internally within a slice)
_ITERS = 12000      # annealing steps per restart
_PATIENCE = 3000    # restart after this many steps without improvement


# ----------------------------------------------------------------------------
# Safe baseline families.
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


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))  # ceil, so the order is at least target
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1  # dihedral-type: (a,b)(c,e) = (a + (-1)^b c, b+e)
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


def _c_search(d, D, k, m, k2, r, seed, secs):
    """Run the C annealer on one group for up to `secs` seconds. Returns (n, edges) or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, k, m, k2, r, seed, f"{secs:.3f}", _ITERS, _PATIENCE],
                        timeout=secs + 30.0)
        n, edges = lib.parse_graph_text(out)
    except Exception:
        return None
    if n <= 0 or not edges:
        return None
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.92 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions: return immediately (calibration-style cases).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: C annealer per sampled group, with a bandit over base sizes k.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        remaining = deadline - time.monotonic()
        if remaining < 0.5:
            break
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G = m * k2
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        slice_s = min(_SLICE, deadline - time.monotonic())
        if slice_s < 0.3:
            break
        res = _c_search(d, D, k, m, k2, r, rng.randrange(1, 1 << 30), slice_s)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
