"""Bold variant for d=11, D=5: a C-native simulated-annealing engine over bi-Cayley lifts.

Changes from the parent:
- The inner search (voltage/permutation annealing, bitmask reachability, duplicate
  penalty, output) runs in C. Groups are passed as parameters (semidirect
  Z_m x| Z_k2 or affine AGL(1,p)) and multiplied by formula, so no big tables cross
  the process boundary.
- Base sizes k up to 8 (parent: up to 6), and the group sampler finds r with
  r^k2 = 1 mod m by enumeration, so non-abelian semidirect products actually occur.
- Bad-vertex-guided moves: annealing moves are biased toward darts that touch
  unreached (vertex, block) pairs.
- The Python slack extension is dropped. Bi-Cayley lifts are d-regular, so it can
  add nothing there, and its repeated lib.is_valid calls were slow.

Safety: every returned graph passes lib.is_valid. Fallbacks are K_{d,d}, the
projective-plane incidence graph, and W(q) for D = 4. Any C failure leaves the
best valid graph found so far.
"""
import math
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 8
#define MAXD 64
#define PEN 1000L

typedef struct {
    int type;      /* 0: Z_m x| Z_k2 (r), 1: AGL(1,p) */
    int m, k2, r, p;
    int G;
    int *pw;       /* pw[b] = r^b mod m */
    int *inv;      /* inv[s]: inv[s]*s = identity */
} Group;

static Group GR;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pc32(uint32_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

/* Group multiplication; identity has index 0 in both families. */
static int gmul(int x, int y) {
    if (GR.type == 0) {
        int k2 = GR.k2, m = GR.m;
        int a = x / k2, b = x % k2;
        int c = y / k2, e = y % k2;
        int aa = (int)(((long)a + (long)GR.pw[b] * (long)c) % m);
        int bb = (b + e) % k2;
        return aa * k2 + bb;
    } else {
        int p = GR.p;
        int a = x / p + 1, b = x % p;
        int c = y / p + 1, e = y % p;
        int ac = (a * c) % p;
        int ae = (a * e + b) % p;
        return (ac - 1) * p + ae;
    }
}

static int setup_group(int type, int p1, int p2, int p3) {
    GR.type = type;
    GR.pw = NULL;
    GR.inv = NULL;
    if (type == 0) {
        GR.m = p1; GR.k2 = p2; GR.r = p3; GR.p = 0;
        if (GR.m < 2 || GR.k2 < 1 || (long)GR.m * GR.k2 > 6000L) return 0;
        if (GR.r < 0 || GR.r >= GR.m) return 0;
        GR.pw = (int *)malloc(sizeof(int) * (size_t)GR.k2);
        if (!GR.pw) return 0;
        long v = 1 % GR.m;
        for (int b = 0; b < GR.k2; b++) {
            GR.pw[b] = (int)v;
            v = (v * (long)GR.r) % GR.m;
        }
        GR.G = GR.m * GR.k2;
    } else if (type == 1) {
        GR.p = p1; GR.m = 0; GR.k2 = 0; GR.r = 0;
        if (GR.p < 3 || GR.p > 80) return 0;
        GR.G = (GR.p - 1) * GR.p;
    } else {
        return 0;
    }
    GR.inv = (int *)malloc(sizeof(int) * (size_t)GR.G);
    if (!GR.inv) return 0;
    for (int s = 0; s < GR.G; s++) {
        int found = -1;
        for (int t = 0; t < GR.G; t++) {
            if (gmul(s, t) == 0) { found = t; break; }
        }
        if (found < 0) return 0;
        GR.inv[s] = found;
    }
    return 1;
}

/* Globals describing the current bi-Cayley lift.
 * A-block i = vertices i*G..i*G+G-1, B-block j = vertices (k+j)*G..
 * Layer l pairs A_i with B_{perm[l][i]} through voltage vol[l][i]:
 *   A_{i,g} ~ B_{j, g*s},   B_{j,h} ~ A_{i, h*s^{-1}}.  */
static int Dd, DD, Kk, GG, NN;
static int perm[MAXD][MAXK];
static int vol[MAXD][MAXK];
static int *nbr = NULL;
static uint32_t *bufA = NULL, *bufB = NULL, *accR = NULL;
static uint32_t *lastR = NULL;
static uint32_t FULL;

static void set_dart(int l, int i) {
    int j = perm[l][i], s = vol[l][i];
    int is = GR.inv[s];
    int *nb = nbr + (size_t)l * (size_t)NN;
    int base_a = i * GG;
    int base_b = (Kk + j) * GG;
    for (int g = 0; g < GG; g++) {
        nb[base_a + g] = base_b + gmul(g, s);
        nb[base_b + g] = base_a + gmul(g, is);
    }
}

/* Reachability from the 2k block representatives, then the penalised cost. */
static long eval_cost(void) {
    int N = NN, d = Dd, k = Kk;
    uint32_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint32_t) * (size_t)N);
    for (int b = 0; b < 2 * k; b++) cur[(size_t)b * GG] = 1u << b;
    for (int t = 0; t < DD; t++) {
        int changed = 0;
        for (int u = 0; u < N; u++) {
            uint32_t x = cur[u];
            for (int l = 0; l < d; l++) x |= cur[nbr[(size_t)l * N + u]];
            nxt[u] = x;
            if (x != cur[u]) changed = 1;
        }
        uint32_t *tmp = cur; cur = nxt; nxt = tmp;
        if (!changed) break;
    }
    long cost = 0;
    for (int u = 0; u < N; u++) cost += 2 * k - pc32(cur[u]);
    long dup = 0;
    for (int l1 = 0; l1 < d; l1++)
        for (int l2 = l1 + 1; l2 < d; l2++)
            for (int i = 0; i < k; i++)
                if (perm[l1][i] == perm[l2][i] && vol[l1][i] == vol[l2][i]) dup++;
    lastR = cur;
    return cost + PEN * dup;
}

static void output_graph(void) {
    int kG = Kk * GG;
    printf("%d %d\n", NN, kG * Dd);
    for (int u = 0; u < kG; u++)
        for (int l = 0; l < Dd; l++)
            printf("%d %d\n", u, nbr[(size_t)l * NN + u]);
}

int main(int argc, char **argv) {
    if (argc < 10) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]), D = atoi(argv[2]);
    long seedl = atol(argv[3]);
    double budget = atof(argv[4]);
    int k = atoi(argv[5]), gtype = atoi(argv[6]);
    int p1 = atoi(argv[7]), p2 = atoi(argv[8]), p3 = atoi(argv[9]);
    long iters = argc > 10 ? atol(argv[10]) : 5000L;
    if (d < 1 || d > MAXD || D < 1 || k < 1 || k > MAXK || iters < 10) {
        printf("0 0\n");
        return 0;
    }
    if (!setup_group(gtype, p1, p2, p3)) { printf("0 0\n"); return 0; }

    Dd = d; DD = D; Kk = k; GG = GR.G; NN = 2 * k * GG;
    FULL = (1u << (2 * k)) - 1u;
    nbr = (int *)malloc(sizeof(int) * (size_t)d * (size_t)NN);
    bufA = (uint32_t *)malloc(sizeof(uint32_t) * (size_t)NN);
    bufB = (uint32_t *)malloc(sizeof(uint32_t) * (size_t)NN);
    accR = (uint32_t *)malloc(sizeof(uint32_t) * (size_t)NN);
    if (!nbr || !bufA || !bufB || !accR) { printf("0 0\n"); return 0; }

    rs = (uint64_t)seedl * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 10; w++) rnd64();

    clock_t c0 = clock();
    int found = 0;
    while (!found) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= budget) break;

        /* random restart */
        for (int l = 0; l < d; l++) {
            for (int i = 0; i < k; i++) perm[l][i] = i;
            for (int i = k - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = perm[l][i]; perm[l][i] = perm[l][j]; perm[l][j] = t;
            }
            for (int i = 0; i < k; i++) vol[l][i] = rndint(GG);
        }
        for (int l = 0; l < d; l++)
            for (int i = 0; i < k; i++) set_dart(l, i);
        long cost = eval_cost();
        memcpy(accR, lastR, sizeof(uint32_t) * (size_t)NN);

        double Thi = 2.0 + 0.05 * (double)cost;
        double Tlo = 0.2;
        int timeup = 0;
        for (long it = 0; it < iters; it++) {
            if (cost == 0) { found = 1; break; }
            if ((it & 63) == 0) {
                el = (double)(clock() - c0) / CLOCKS_PER_SEC;
                if (el >= budget) { timeup = 1; break; }
            }
            double temp = Thi * pow(Tlo / Thi, (double)it / (double)iters);

            /* choose a dart, biased toward an unreached pair */
            int bad = -1;
            if (rnd01() < 0.5) {
                for (int tr = 0; tr < 64; tr++) {
                    int u = rndint(NN);
                    if (accR[u] != FULL) { bad = u; break; }
                }
            }
            int l, i1;
            if (bad >= 0) {
                int b = bad / GG;
                l = rndint(d);
                if (b < k) {
                    i1 = b;
                } else {
                    int j = b - k;
                    i1 = -1;
                    for (int i = 0; i < k; i++)
                        if (perm[l][i] == j) { i1 = i; break; }
                    if (i1 < 0) continue;
                }
            } else {
                l = rndint(d);
                i1 = rndint(k);
            }

            int swapmove = (k >= 2 && rnd01() < 0.25);
            long newcost;
            if (swapmove) {
                int i2 = rndint(k - 1);
                if (i2 >= i1) i2++;
                int t = perm[l][i1]; perm[l][i1] = perm[l][i2]; perm[l][i2] = t;
                set_dart(l, i1); set_dart(l, i2);
                newcost = eval_cost();
                if (newcost <= cost || rnd01() < exp(-(double)(newcost - cost) / temp)) {
                    cost = newcost;
                    memcpy(accR, lastR, sizeof(uint32_t) * (size_t)NN);
                } else {
                    t = perm[l][i1]; perm[l][i1] = perm[l][i2]; perm[l][i2] = t;
                    set_dart(l, i1); set_dart(l, i2);
                }
            } else {
                int old = vol[l][i1];
                int nv = rndint(GG);
                if (nv == old) continue;
                vol[l][i1] = nv;
                set_dart(l, i1);
                newcost = eval_cost();
                if (newcost <= cost || rnd01() < exp(-(double)(newcost - cost) / temp)) {
                    cost = newcost;
                    memcpy(accR, lastR, sizeof(uint32_t) * (size_t)NN);
                } else {
                    vol[l][i1] = old;
                    set_dart(l, i1);
                }
            }
        }
        if (cost == 0) found = 1;
        if (found) { output_graph(); return 0; }
        if (timeup) break;
    }
    printf("0 0\n");
    return 0;
}
'''


_KS = (1, 2, 3, 4, 5, 6, 8)
_AFF = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73)
_K2S = (1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 16, 18, 20, 24, 30, 36)
_GMAX = 6000


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    import itertools
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _draw(target, rng):
    """Return (gtype, p1, p2, p3, order) for a group of order >= target, or None."""
    if rng.random() < 0.4:
        cands = [p for p in _AFF if target <= p * (p - 1) <= 1.2 * target + 40]
        if cands:
            p = rng.choice(cands)
            return 1, p, 0, 0, p * (p - 1)
    for _ in range(30):
        k2 = rng.choice(_K2S)
        m = max(2, -(-target // k2)) + rng.randrange(0, 4)
        if m * k2 > _GMAX:
            continue
        roots = []
        if rng.random() < 0.7:
            roots = [c for c in range(2, m)
                     if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
        r = rng.choice(roots) if roots else 1
        return 0, m, k2, r, m * k2
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    hard_end = t0 + max(1.0, min(0.9 * time_limit, time_limit - 6.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    if D <= 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    pg = None
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if D == 3 and pg is not None and lib.is_prime_power(d - 1):
            return best

    if D == 4 and time.monotonic() < hard_end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
        if d - 1 <= 9 and lib.is_prime_power(d - 1):
            return best

    # Main search: C annealing over bi-Cayley lifts, bandit over base sizes k.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    while True:
        remaining = hard_end - time.monotonic()
        if remaining < 1.0:
            break
        n_best = best[0]
        if rng.random() < 0.2:
            k = rng.choice(_KS)
        else:
            k = max(_KS, key=lambda kk: (wins[kk] + 1) / (trials[kk] + 2)
                    + 0.02 * rng.random())
        base = n_best // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 10 + 1)))
        g = _draw(target, rng)
        if g is None:
            continue
        gtype, p1, p2, p3, G = g
        if 2 * k * G <= n_best:
            continue
        trials[k] += 1
        slice_s = min(remaining, rng.uniform(1.5, 4.0))
        iters = 3000 + rng.randrange(3000)
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, rng.randrange(1, 1 << 30), round(slice_s, 3),
                 k, gtype, p1, p2, p3, iters],
                timeout=remaining + 4.0)
            n, e = lib.parse_graph_text(out)
        except (RuntimeError, ValueError):
            break
        if n > 0:
            wins[k] += 1
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
