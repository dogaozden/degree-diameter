"""Bi-Cayley voltage-lift search in C over semidirect groups Z_m x| Z_k2.

Python picks a block count k and a group, then C anneals the voltages and block
permutations. A lift over a group acts regularly on each block, so the diameter
check only needs BFS from the 2k block representatives. Those BFS runs are done
bit-parallel with one 64-bit mask per vertex. Every returned graph is checked
with lib.is_valid. K_{d,d} (or a known exact construction) is the fallback.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley lift annealer over G = Z_m x|_r Z_k2 with k base blocks per side.
 * Usage: prog d D seed time_limit k m k2 r
 * Vertices: A_{i,g} = i*G+g (i<k), B_{j,h} = (k+j)*G+h.
 * Layer l: A-block i joins B-block P[l][i] with voltage S[l][i]: A_{i,g} ~ B_{P,g*s}.
 * Each layer is a permutation of blocks, so the lift is d-regular and bipartite.
 * Diameter <= D iff BFS of depth D from each of the 2k block identities covers all vertices
 * (left multiplication by G is an automorphism).
 * Output: "n m" + edges of a valid lift, or "0 0" if none was found within the time.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 40000
#define MAXD 32
#define MAXK 32
#define MAXKP 256

static int d, D, k, m, k2, G, N;
static long long pw[MAXKP];
static int P[MAXD][MAXK];
static int S[MAXD][MAXK];
static int sinvv[MAXD][MAXK];
static int pinvv[MAXD][MAXK];
static int nbr[MAXN * MAXD];
static uint64_t bufA[MAXN], bufB[MAXN];
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

/* Group law (a,b)(c,e) = (a + r^b c, b + e), element x = a*k2 + b. */
static int gmul(int x, int y) {
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long long t = ((long long)a + pw[b] * (long long)c) % m;
    return (int)(t * k2 + (b + e) % k2);
}

/* Inverse: (a,b)^-1 = (-r^(-b) a, -b). */
static int ginv(int x) {
    int a = x / k2, b = x % k2;
    int nb = (k2 - b) % k2;
    long long t = pw[nb] * (long long)a % m;
    long long c = (m - t) % m;
    return (int)(c * k2 + nb);
}

static void build_nbr(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) {
            sinvv[l][i] = ginv(S[l][i]);
            pinvv[l][P[l][i]] = i;
        }
    for (int i = 0; i < k; i++)
        for (int g = 0; g < G; g++) {
            int u = i * G + g;
            int *row = nbr + (size_t)u * d;
            for (int l = 0; l < d; l++)
                row[l] = (k + P[l][i]) * G + gmul(g, S[l][i]);
        }
    for (int j = 0; j < k; j++)
        for (int h = 0; h < G; h++) {
            int v = (k + j) * G + h;
            int *row = nbr + (size_t)v * d;
            for (int l = 0; l < d; l++) {
                int i = pinvv[l][j];
                row[l] = i * G + gmul(h, sinvv[l][i]);
            }
        }
}

/* Number of repeated (block, voltage) pairs across layers, which would make multi-edges. */
static int dup_count(void) {
    int c = 0;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int q = 0; q < l; q++)
                if (P[l][i] == P[q][i] && S[l][i] == S[q][i]) c++;
    return c;
}

/* Cost = unreached (block identity, vertex) pairs within distance D, plus a duplicate penalty. */
static long long evaluate(void) {
    build_nbr();
    uint64_t *cur = bufA, *nxt = bufB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * k; b++) cur[(size_t)b * G] = 1ULL << b;
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < N; v++) {
            uint64_t r = cur[v];
            const int *row = nbr + (size_t)v * d;
            for (int l = 0; l < d; l++) r |= cur[row[l]];
            nxt[v] = r;
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long unr = 0;
    for (int v = 0; v < N; v++) unr += 2 * k - __builtin_popcountll(cur[v]);
    return unr + 50LL * dup_count();
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) P[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = P[l][i];
            P[l][i] = P[l][j];
            P[l][j] = t;
        }
        for (int i = 0; i < k; i++) S[l][i] = rndint(G);
    }
}

static int gcd_int(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: %s d D seed time k m k2 r\n", argv[0]);
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    k = atoi(argv[5]);
    m = atoi(argv[6]);
    k2 = atoi(argv[7]);
    int r = atoi(argv[8]);
    double t0 = now();
    double t_end = t0 + limit * 0.9 - 0.3;

    if (d < 1 || d > MAXD || D < 1 || k < 1 || k > MAXK || m < 2 || k2 < 1 || k2 > MAXKP) {
        printf("0 0\n");
        return 0;
    }
    G = m * k2;
    N = 2 * k * G;
    if (N > MAXN) {
        printf("0 0\n");
        return 0;
    }
    if (k2 == 1) {
        r = 1;
    } else {
        r %= m;
        if (r < 1 || gcd_int(r, m) != 1) {
            printf("0 0\n");
            return 0;
        }
    }
    pw[0] = 1 % m;
    for (int t = 1; t < k2; t++) pw[t] = pw[t - 1] * (long long)r % m;
    if (k2 > 1 && (pw[k2 - 1] * (long long)r) % m != 1 % m) {
        printf("0 0\n");
        return 0;
    }

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int t = 0; t < 10; t++) rnd();

    int found = 0;
    const long R = 15000;
    while (!found && now() < t_end) {
        random_state();
        long long cost = evaluate();
        long long best = cost;
        long since = 0;
        while (cost > 0 && since <= R && now() < t_end) {
            double T = 3.0 * (1.0 - (double)since / (double)R) + 0.1;
            int type, l, i1 = 0, i2 = 0, i = 0, oldS = 0;
            if (k >= 2 && rnd01() < 0.3) {
                type = 0;
                l = rndint(d);
                i1 = rndint(k);
                i2 = rndint(k - 1);
                if (i2 >= i1) i2++;
                int t = P[l][i1];
                P[l][i1] = P[l][i2];
                P[l][i2] = t;
            } else {
                type = 1;
                l = rndint(d);
                i = rndint(k);
                oldS = S[l][i];
                S[l][i] = rndint(G);
            }
            long long nc = evaluate();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
                if (cost < best) {
                    best = cost;
                    since = 0;
                } else {
                    since++;
                }
            } else {
                since++;
                if (type == 0) {
                    int t = P[l][i1];
                    P[l][i1] = P[l][i2];
                    P[l][i2] = t;
                } else {
                    S[l][i] = oldS;
                }
            }
        }
        if (cost == 0) found = 1;
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    build_nbr();
    long M = (long)k * G * d;
    printf("%d %ld\n", N, M);
    for (int u = 0; u < k * G; u++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", u, nbr[(size_t)u * d + l]);
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
# Group sampling for the C lift search.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4, 5, 6, 8)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, r^k2 = 1 mod m, gcd(r, m) = 1."""
    k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 8, 10])
    m = max(2, -(-target // k2))
    if k2 == 1 or m < 3:
        return max(2, target), 1, 1
    cands = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
    if not cands:
        return max(2, target), 1, 1
    return m, k2, rng.choice(cands)


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

    # Main phase: C bi-Cayley lift annealing over sampled semidirect groups.
    # The order goal ratchets up on success and eases down on failure.
    if d >= 3 and D >= 3:
        goal = float(best_n) * 1.02
        it = 0
        while True:
            remaining = final - time.monotonic()
            if remaining < 2.5:
                break
            slice_s = min(remaining - 1.0, max(2.0, min(12.0, 0.3 * remaining)))
            k = rng.choice(_KS)
            target = max(2, int(math.ceil(goal / (2 * k))))
            m, k2, r = _sample_group(target, rng)
            it += 1
            n, e = 0, []
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, seed * 7919 + it, round(slice_s, 2), k, m, k2, r],
                                 timeout=slice_s + 10)
                n, e = lib.parse_graph_text(text)
            except Exception:
                n, e = 0, []
            if n > 0 and lib.is_valid(n, e, d, D):
                consider(n, e)
                goal = max(goal, n * 1.03 + 2)
            else:
                goal = max(float(best_n) * 1.005, goal * 0.99)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
