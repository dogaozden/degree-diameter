"""Bold rewrite: a C simulated-annealing engine over bi-Cayley lifts (voltage lifts over
semidirect products Z_m x| Z_k2). Python chooses the base size k and the group, and grows the
target order as successes come in. Exact constructions (projective planes, Araujo-Pardo-Lopez,
W(q)) and K_{d,d} are fallbacks. Every returned graph is checked with lib.is_valid.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley lift annealer.
 * Usage: prog d D k m k2 r seed slice_seconds
 * Group G = Z_m x| Z_k2, element (a,b) coded as a*k2+b, with
 *   (a,b)*(c,e) = (a + r^b c mod m, b+e mod k2), requiring r^k2 = 1 mod m.
 * Vertices: A_{i,g} = i*G+g (i<k), B_{j,h} = (k+j)*G+h.
 * Layer l: A_{i,g} ~ B_{perm[l][i], g*sv[l][i]}. Every layer is a perfect matching, so the
 * lift is d-regular. Left multiplication is an automorphism, so diameter <= D holds iff every
 * vertex reaches every block representative (vertex b*G) within D steps. Cost = unreached
 * (vertex, block) pairs + PEN * duplicate darts.
 * stdout: "N M" and the edge list on success, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXK 16
#define PEN 1000L
#define PATIENCE 4000

static int d, D, k, m, k2, G, N;
static long long pw[64];
static int perm[MAXD][MAXK];
static int sv[MAXD][MAXK];
static int *nb;
static uint64_t *RA, *RB, *Rres;
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

static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int mulg(int x, int y) {
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long long t = (long long)a + pw[b] * (long long)c;
    return (int)((t % m) * k2 + (b + e) % k2);
}

/* Rebuild the neighbour slot for layer l on all vertices. */
static void build_layer(int l) {
    for (int i = 0; i < k; i++) {
        int j = perm[l][i], s = sv[l][i];
        for (int g = 0; g < G; g++) {
            int A = i * G + g;
            int B = (k + j) * G + mulg(g, s);
            nb[(size_t)A * d + l] = B;
            nb[(size_t)B * d + l] = A;
        }
    }
}

/* Cost of the current lift (0 means valid). Sets Rres to the reach masks. */
static long evaluate(void) {
    uint64_t *cur = RA, *nxt = RB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * k; b++) cur[(size_t)b * G] |= 1ULL << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            const int *p = nb + (size_t)v * d;
            for (int l = 0; l < d; l++) x |= cur[p[l]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    long unre = 0;
    int full = 2 * k;
    for (int v = 0; v < N; v++) unre += full - __builtin_popcountll(cur[v]);
    Rres = cur;
    long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1][i] == perm[l2][i] && sv[l1][i] == sv[l2][i]) dup++;
    return unre + PEN * dup;
}

static void random_init(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) perm[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = t;
        }
        for (int i = 0; i < k; i++) sv[l][i] = rndint(G);
        build_layer(l);
    }
}

static int accept_move(long c, long c2, double T) {
    if (c2 <= c) return 1;
    return rnd01() < exp(-(double)(c2 - c) / T);
}

static void output_graph(void) {
    long M = (long)k * G * d;
    printf("%d %ld\n", N, M);
    for (int v = 0; v < k * G; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nb[(size_t)v * d + l]);
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: %s d D k m k2 r seed slice\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    k = atoi(argv[3]);
    m = atoi(argv[4]);
    k2 = atoi(argv[5]);
    long long r = atoll(argv[6]);
    unsigned long long seed = strtoull(argv[7], NULL, 10);
    double slice = atof(argv[8]);
    if (d < 2 || d > MAXD || D < 2 || k < 1 || k > MAXK || m < 2 || k2 < 1 || k2 > 60) {
        printf("0 0\n");
        return 0;
    }
    G = m * k2;
    N = 2 * k * G;
    long long rr = ((r % m) + m) % m;
    pw[0] = 1 % m;
    for (int t = 1; t < k2; t++) pw[t] = pw[t - 1] * rr % m;
    if ((pw[k2 - 1] * rr) % m != 1 % m) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    nb = malloc(sizeof(int) * (size_t)N * d);
    RA = malloc(sizeof(uint64_t) * (size_t)N);
    RB = malloc(sizeof(uint64_t) * (size_t)N);
    if (!nb || !RA || !RB) {
        printf("0 0\n");
        return 0;
    }

    uint64_t fullmask = (2 * k >= 64) ? ~0ULL : ((1ULL << (2 * k)) - 1);
    double t_end = now() + slice;
    while (now() < t_end) {
        random_init();
        long c = evaluate();
        long best = c;
        double T0 = 1.0 + 0.02 * (double)c;
        long since = 0;
        long it = 0;
        while (c > 0) {
            if ((it & 31) == 0 && now() > t_end) break;
            if (since > PATIENCE) break;
            it++;
            double T = T0 * exp(-(double)it / 3000.0);
            if (T < 0.25) T = 0.25;

            if (k >= 2 && rnd01() < 0.2) {
                int l = rndint(d);
                int i1 = rndint(k);
                int i2 = rndint(k - 1);
                if (i2 >= i1) i2++;
                int tt = perm[l][i1];
                perm[l][i1] = perm[l][i2];
                perm[l][i2] = tt;
                build_layer(l);
                long c2 = evaluate();
                if (accept_move(c, c2, T)) {
                    c = c2;
                } else {
                    tt = perm[l][i1];
                    perm[l][i1] = perm[l][i2];
                    perm[l][i2] = tt;
                    build_layer(l);
                }
            } else {
                int l = rndint(d);
                int i = -1;
                if (rnd01() < 0.5) {
                    int v = -1;
                    for (int tr = 0; tr < 20; tr++) {
                        int u = rndint(N);
                        if (Rres[u] != fullmask) {
                            v = u;
                            break;
                        }
                    }
                    if (v >= 0 && v < k * G) {
                        i = v / G;
                    } else if (v >= 0) {
                        int j = v / G - k;
                        for (int q = 0; q < k; q++)
                            if (perm[l][q] == j) {
                                i = q;
                                break;
                            }
                    }
                }
                if (i < 0) i = rndint(k);
                int old = sv[l][i];
                sv[l][i] = rndint(G);
                build_layer(l);
                long c2 = evaluate();
                if (accept_move(c, c2, T)) {
                    c = c2;
                } else {
                    sv[l][i] = old;
                    build_layer(l);
                }
            }
            if (c < best) {
                best = c;
                since = 0;
            } else {
                since++;
            }
        }
        if (c == 0) {
            output_graph();
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions (fallbacks).
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
# Group sampling for the lift search.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target and r^k2 = 1 mod m."""
    k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 18, 20, 24])
    m = max(2, -(-target // k2))
    r = 1
    if k2 > 1 and m > 2 and rng.random() < 0.7:
        for _ in range(300):
            c = rng.randrange(2, m)
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                r = c
                break
    return m, k2, r


_KS = (1, 2, 3, 4, 6, 8)


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    final = t0 + max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
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

    # Main phase: C lift annealing. Each call tries one (k, group) pair with a target order
    # slightly above the best so far. The relative step eps adapts to successes and failures.
    if 2 <= d <= 32 and D >= 2:
        trials = {k: 0 for k in _KS}
        wins = {k: 0 for k in _KS}

        def pick_k():
            if rng.random() < 0.25:
                return rng.choice(_KS)
            return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.05 * rng.random())

        eps = 0.3
        errors = 0
        while True:
            remaining = final - time.monotonic() - 2.0
            if remaining < 1.5 or errors >= 5:
                break
            k = pick_k()
            target_N = int(best_n * (1.0 + eps)) + 2
            target_G = -(-target_N // (2 * k))
            m, k2, r = _sample_group(target_G, rng)
            slice_s = min(remaining, rng.uniform(3.0, 7.0))
            trials[k] += 1
            try:
                text = lib.run_c(C_SOURCE, [d, D, k, m, k2, r, rng.randrange(1 << 30), round(slice_s, 2)],
                                 timeout=slice_s + 10)
                n, edges = lib.parse_graph_text(text)
                errors = 0
            except Exception:
                errors += 1
                continue
            if n > best_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_n = n
                wins[k] += 1
                eps = min(0.5, eps * 1.5)
            else:
                eps = max(0.003, eps * 0.8)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
