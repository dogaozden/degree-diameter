import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Bold change for this island: bi-Cayley (Haar-type) graphs instead of voltage lifts.
#
# Vertices A_g and B_h for g, h in a group Gamma of order G (semidirect
# Z_m x| Z_k, element (a,b) coded as a*k+b). Connection set S = {s_1..s_d} of
# DISTINCT group elements. Edges A_g -- B_{g s} for s in S.
#   * Simple and bipartite by construction; every vertex has degree exactly d.
#   * Left multiplication is an automorphism, so the diameter is <= D iff BFS of
#     depth D from A_e and from B_e reaches everything.
#   * Order 2G, so beating the record 684 needs a group of order G >= 343.
#
# The C search is simulated annealing over connection sets: one element of S is
# replaced by an unused group element per move, and the cost is the number of
# uncovered ordered pairs from the two representatives. Groups are sampled
# fresh from a window just above the best order found so far.
#
# Safe fallbacks: K_{d,d} (valid for D >= 2) and the projective-plane incidence
# graph (diameter 3). Every returned graph is checked with lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define ITERS 60000
#define GMAX 3000
#define MAXDEG 16
#define MAXK 12

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int DEG, DIAM;
static int GO, KG, MG, RG;
static int Rpow[MAXK];
static int S[MAXDEG], Sinv[MAXDEG], bestS[MAXDEG];
static int *stampv = NULL, *queue = NULL;
static int curst = 0;
static int best_G = 0;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod(long long b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* (a,b)*(c,e) = (a + r^b c, b + e), element index a*KG + b. */
static inline int gmul(int x, int y) {
    int a = x / KG, b = x % KG;
    int c = y / KG, e = y % KG;
    long long ra = ((long long)a + (long long)Rpow[b] * c) % MG;
    int rb = (b + e) % KG;
    return (int)ra * KG + rb;
}

/* Inverse of (a,b) is (-r^{-b} a, -b), with r^{-b} = r^{(k-b) mod k}. */
static int ginv(int x) {
    int a = x / KG, b = x % KG;
    int nb = (KG - b) % KG;
    long long prod = ((long long)Rpow[nb] * a) % MG;
    long long ia = (MG - prod) % MG;
    return (int)ia * KG + nb;
}

static void setup_group(int G, int k, int m, int r) {
    GO = G; KG = k; MG = m; RG = r;
    Rpow[0] = 1 % MG;
    for (int b = 1; b < KG; b++)
        Rpow[b] = (int)(((long long)Rpow[b - 1] * RG) % MG);
}

/* Picks k | G (k <= 12, m = G/k >= 2) and r with gcd(r,m)=1, r^k = 1 mod m.
   Falls back to the cyclic group (k = 1, r = 1), which always exists. */
static void choose_group(int G, int *kout, int *mout, int *rout) {
    int opts[MAXK + 1], no = 0;
    for (int k = 1; k <= MAXK; k++)
        if (G % k == 0 && G / k >= 2) opts[no++] = k;
    int k = opts[rnd_int(no)];
    int m = G / k, r = 1;
    if (k > 1) {
        int found = 0;
        for (int tr = 0; tr < 300 && !found; tr++) {
            int cand = 1 + rnd_int(m - 1);
            if (gcd_i(cand, m) == 1 && powmod(cand, k, m) == 1 % m) {
                r = cand;
                found = 1;
            }
        }
        if (!found) { k = 1; m = G; r = 1; }
    }
    *kout = k; *mout = m; *rout = r;
}

/* Uncovered ordered pairs from A_e (index 0) and B_e (index GO). Zero iff diameter <= DIAM. */
static long long eval_cost(void) {
    int N = 2 * GO;
    long long total = 0;
    for (int src = 0; src < 2; src++) {
        int s0 = src ? GO : 0;
        if (curst >= 2000000000) {
            memset(stampv, 0, sizeof(int) * (size_t)(2 * GMAX + 4));
            curst = 0;
        }
        curst++;
        int head = 0, tail = 0;
        queue[tail++] = s0;
        stampv[s0] = curst;
        for (int lvl = 0; lvl < DIAM; lvl++) {
            int end = tail;
            if (head == end) break;
            for (int q = head; q < end; q++) {
                int v = queue[q];
                if (v < GO) {
                    for (int i = 0; i < DEG; i++) {
                        int w = GO + gmul(v, S[i]);
                        if (stampv[w] != curst) {
                            stampv[w] = curst;
                            queue[tail++] = w;
                        }
                    }
                } else {
                    int h = v - GO;
                    for (int i = 0; i < DEG; i++) {
                        int w = gmul(h, Sinv[i]);
                        if (stampv[w] != curst) {
                            stampv[w] = curst;
                            queue[tail++] = w;
                        }
                    }
                }
            }
            head = end;
        }
        total += N - tail;
    }
    return total;
}

static void random_S(void) {
    for (int i = 0; i < DEG; i++) {
        int x, ok;
        do {
            x = rnd_int(GO);
            ok = 1;
            for (int j = 0; j < i; j++)
                if (S[j] == x) { ok = 0; break; }
        } while (!ok);
        S[i] = x;
        Sinv[i] = ginv(x);
    }
}

/* Simulated annealing over connection sets. Returns the best (smallest) cost seen; bestS holds that set. */
static long long anneal(int iters) {
    long long cur = eval_cost();
    long long best = cur;
    memcpy(bestS, S, sizeof(int) * (size_t)DEG);
    if (best == 0) return 0;
    for (int it = 0; it < iters; it++) {
        if ((it & 255) == 0 && elapsed() > DEADLINE) break;
        double frac = (double)it / (double)iters;
        double temp = 2.0 * (1.0 - frac) + 0.05;
        int i = rnd_int(DEG);
        int x = rnd_int(GO);
        int dup = 0;
        for (int j = 0; j < DEG; j++)
            if (S[j] == x) { dup = 1; break; }
        if (dup) continue;
        int old = S[i], oldinv = Sinv[i];
        S[i] = x;
        Sinv[i] = ginv(x);
        long long nc = eval_cost();
        long long diff = nc - cur;
        if (diff <= 0 || rnd_unit() < exp(-(double)diff / temp)) {
            cur = nc;
            if (cur < best) {
                best = cur;
                memcpy(bestS, S, sizeof(int) * (size_t)DEG);
                if (best == 0) break;
            }
        } else {
            S[i] = old;
            Sinv[i] = oldinv;
        }
    }
    return best;
}

static void emit(void) {
    int m = DEG * GO;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int i = 0; i < DEG; i++)
        for (int g = 0; g < GO; g++) {
            best_e[idx++] = g;
            best_e[idx++] = GO + gmul(g, S[i]);
        }
    best_m = m;
    best_n = 2 * GO;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int start_n = argc > 5 ? atoi(argv[5]) : 0;
    if (DEG < 1 || DIAM < 1 || DEG > MAXDEG) {
        printf("0 0\n");
        return 0;
    }
    best_G = start_n / 2;
    stampv = calloc((size_t)(2 * GMAX + 4), sizeof(int));
    queue = malloc(sizeof(int) * (size_t)(2 * GMAX + 4));

    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        if (best_G >= GMAX) break;
        int lo = best_G + 1;
        if (lo < DEG + 1) lo = DEG + 1;
        if (lo < 4) lo = 4;
        int spread = 2 + lo / 60;
        int G = lo + rnd_int(spread);
        if (G > GMAX) G = GMAX;
        int k, m, r;
        choose_group(G, &k, &m, &r);
        setup_group(G, k, m, r);
        random_S();
        long long bc = anneal(ITERS);
        if (bc == 0) {
            memcpy(S, bestS, sizeof(int) * (size_t)DEG);
            for (int i = 0; i < DEG; i++) Sinv[i] = ginv(S[i]);
            emit();
            best_G = G;
        }
    }

    if (best_m > 0) {
        printf("%d %d\n", best_n, best_m);
        for (int i = 0; i < best_m; i++)
            printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families (Python side).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
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
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then the C bi-Cayley annealer.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() - start < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best_n >= lib.moore_bound(d, D):
        return best

    # Nearly all of the budget goes to the C search. The reserve covers
    # parsing and validation; the C program stops itself at its deadline.
    remaining = 0.9 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
