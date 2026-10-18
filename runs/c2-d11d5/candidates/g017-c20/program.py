"""Bi-Cayley voltage-lift search in C, with an exact block-representative distance check.

Graphs are bi-Cayley over semidirect products Z_m x| Z_k2 with k base vertices per side.
Each of the d layers is a permutation of the k A-blocks onto the k B-blocks, with a voltage
per (layer, block). Left translations are automorphisms, so the diameter check only needs
2k bitmask BFS sources. The C engine runs simulated annealing over permutations and voltages,
ratchets the order upward, and returns the largest valid graph it found.

Python supplies exact constructions (projective planes, Araujo-Pardo-Lopez, generalized
quadrangles) and simple cycle/K_{d,d} fallbacks. Every returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib


C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 16384
#define MAXD 16
#define MAXK 8
#define MAXG 8192
#define MAXK2 16
#define DUP_W 30
#define STALL 8000
#define TEMP 0.8

static int d, D;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
static int powmod(int b, int e, int m) {
    long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* Group Z_m x| Z_k2; element (a,b) coded a*k2+b; (a,b)(c,e) = (a + r^b c, b+e). */
static int gm, gk2, gG, gr;
static int pw[MAXK2];
static int GA[MAXG], GB[MAXG];

static int gmul(int x, int y) {
    int a1 = GA[x], b1 = GB[x], a2 = GA[y], b2 = GB[y];
    int a = (int)((a1 + (long)pw[b1] * a2) % gm);
    return a * gk2 + (b1 + b2) % gk2;
}

static void set_group(int m, int k2, int r) {
    gm = m;
    gk2 = k2;
    gG = m * k2;
    gr = r;
    long p = 1 % m;
    for (int b = 0; b < k2; b++) {
        pw[b] = (int)p;
        p = p * r % m;
    }
    for (int x = 0; x < gG; x++) {
        GA[x] = x / k2;
        GB[x] = x % k2;
    }
}

/* Bi-Cayley state. A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h. Layer l: A_i ~ B_{sig[l][i]}
 * with A_{i,g} ~ B_{sig, g*VS}. */
static int K;
static int sig[MAXD][MAXK];
static int VS[MAXD][MAXK];
static int NB[MAXN * MAXD];

static void set_dart(int l, int i) {
    int G = gG, k = K, j = sig[l][i], s = VS[l][i];
    for (int g = 0; g < G; g++) {
        int h = gmul(g, s);
        int A = i * G + g;
        int B = (k + j) * G + h;
        NB[A * d + l] = B;
        NB[B * d + l] = A;
    }
}

static uint32_t RA[MAXN], RB[MAXN];

/* Sum over all vertices v of the number of block representatives at distance > D.
 * Exact, because left translations act regularly on each block. */
static long unreached(void) {
    int G = gG, k = K, N = 2 * K * G;
    uint32_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint32_t) * (size_t)N);
    for (int b = 0; b < 2 * k; b++) cur[b * G] |= 1u << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = cur[v];
            const int *q = NB + v * d;
            for (int l = 0; l < d; l++) x |= cur[q[l]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint32_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    long c = 0;
    for (int v = 0; v < N; v++) c += 2 * k - __builtin_popcount(cur[v]);
    return c;
}

static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = 0; l2 < l1; l2++)
                if (sig[l1][i] == sig[l2][i] && VS[l1][i] == VS[l2][i]) c++;
    return c;
}

static long full_cost(void) { return unreached() + DUP_W * dupcount(); }

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) sig[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = sig[l][i];
            sig[l][i] = sig[l][j];
            sig[l][j] = t;
        }
        for (int i = 0; i < K; i++) VS[l][i] = rndint(gG);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

/* Annealing for the current group and K. Returns 1 when cost 0 (valid graph) is reached. */
static int attempt(double until) {
    random_state();
    long cost = full_cost();
    long best = cost, last = 0;
    for (long it = 1; cost > 0; it++) {
        if ((it & 63) == 0 && now() > until) return 0;
        if (it - last > STALL) return 0;
        int mv = rndint(100);
        if (mv < 45) {
            int l = rndint(d), i = rndint(K);
            int old = VS[l][i], nw = rndint(gG);
            if (nw == old) continue;
            VS[l][i] = nw;
            set_dart(l, i);
            long nc = full_cost();
            if (nc <= cost || rnd01() < exp((double)(cost - nc) / TEMP)) cost = nc;
            else {
                VS[l][i] = old;
                set_dart(l, i);
            }
        } else if (mv < 75) {
            if (K < 2) continue;
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K);
            if (i1 == i2) continue;
            int t = sig[l][i1];
            sig[l][i1] = sig[l][i2];
            sig[l][i2] = t;
            set_dart(l, i1);
            set_dart(l, i2);
            long nc = full_cost();
            if (nc <= cost || rnd01() < exp((double)(cost - nc) / TEMP)) cost = nc;
            else {
                t = sig[l][i1];
                sig[l][i1] = sig[l][i2];
                sig[l][i2] = t;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            if (d < 2) continue;
            int l1 = rndint(d), l2 = rndint(d), i = rndint(K);
            if (l1 == l2) continue;
            int t = VS[l1][i];
            VS[l1][i] = VS[l2][i];
            VS[l2][i] = t;
            set_dart(l1, i);
            set_dart(l2, i);
            long nc = full_cost();
            if (nc <= cost || rnd01() < exp((double)(cost - nc) / TEMP)) cost = nc;
            else {
                t = VS[l1][i];
                VS[l1][i] = VS[l2][i];
                VS[l2][i] = t;
                set_dart(l1, i);
                set_dart(l2, i);
            }
        }
        if (cost < best) {
            best = cost;
            last = it;
        }
    }
    return 1;
}

static long best_half = 0;
static int bK, bm, bk2, br;
static int bsig[MAXD][MAXK], bVS[MAXD][MAXK];

static void save_best(void) {
    best_half = (long)K * gG;
    bK = K;
    bm = gm;
    bk2 = gk2;
    br = gr;
    memcpy(bsig, sig, sizeof(sig));
    memcpy(bVS, VS, sizeof(VS));
}

static void output_best(void) {
    if (best_half == 0) {
        printf("0 0\n");
        return;
    }
    K = bK;
    set_group(bm, bk2, br);
    memcpy(sig, bsig, sizeof(sig));
    memcpy(VS, bVS, sizeof(VS));
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
    int NA = K * gG;
    long m = (long)NA * d;
    printf("%d %ld\n", 2 * NA, m);
    for (int v = 0; v < NA; v++)
        for (int l = 0; l < d; l++) printf("%d %d\n", v, NB[v * d + l]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    double end = t0 + limit * 0.92 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || D < 3 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }

    static const int K2S[] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16};
    const int NK2S = 13;

    while (now() < end) {
        double left = end - now();
        int k = 1 + rndint(MAXK);
        long target = best_half + 1 + rndint(1 + (int)(best_half / 60));
        long Gt = (target + k - 1) / k;
        if (Gt < 2) Gt = 2;
        int k2 = K2S[rndint(NK2S)];
        long mm = (Gt + k2 - 1) / k2 + rndint(3);
        if (mm < 2) mm = 2;
        long G = mm * k2;
        if (G > MAXG || 2L * k * G > MAXN) continue;
        int m = (int)mm;

        int r = 1;
        if (k2 > 1 && m >= 3 && rndint(10) < 7) {
            for (int tries = 0; tries < 200; tries++) {
                int c = 2 + rndint(m - 2);
                if (gcd_i(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                    r = c;
                    break;
                }
            }
        }
        K = k;
        set_group(m, k2, r);
        double slice = left < 2.0 ? left : fmax(2.0, 0.12 * left);
        if (slice > left) slice = left;
        if (attempt(now() + slice)) save_best();
    }
    output_best();
    return 0;
}
'''


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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
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

    # Main search: C bi-Cayley annealing with an order ratchet.
    remaining = final - time.monotonic() - 1.0
    if D >= 3 and d >= 3 and remaining > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             timeout=remaining + 15)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
