import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: Haar graphs of metacyclic groups Z_m x|_r Z_k2.
#
# Group G of order g = m*k2 with elements (a,b) coded as a*k2+b, product
# (a,b)(c,e) = (a + r^b c, b+e). A connection set S of DEG distinct group
# elements gives the bipartite Haar graph: A_x ~ B_{x s} for s in S.
# Left multiplication is an automorphism that is transitive on each side, so
# the graph has diameter <= D iff BFS of depth D from A_e and from B_e covers
# all 2g vertices. The cost is the number of uncovered (source, vertex) pairs,
# which is 0 exactly for a valid graph.
#
# Search: sample a group order g above (best order / 2), pick a random
# factorisation g = m*k2 and a random r with r^k2 = 1 mod m, then anneal the
# connection set S by replacing one element at a time. Groups are re-sampled
# after each annealing run. Each zero-cost run is emitted if it beats the best
# order so far. This family covers orders well above the metacyclic range
# that voltage lifts with a small base reached.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define ITERS 6000
#define GMAX 1500
#define TRIES_R 300

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

static int DEG, DIAM;
static int M, K2, R, G;
static int *Rpow, *mt, *invv;
static int *S, *Si, *bestS;
static int *stp, *qb;
static int stc = 0;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

/* (a,b)*(c,e) = (a + r^b c, b + e), element index a*K2 + b. */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    long long ra = ((long long)a + (long long)Rpow[b] * c) % M;
    int rb = (b + e) % K2;
    return (int)ra * K2 + rb;
}

static void build_group(int m, int k2, int r) {
    M = m; K2 = k2; R = r; G = m * k2;
    Rpow[0] = 1 % m;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * r % m);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            mt[x * G + y] = gmul(x, y);
    for (int x = 0; x < G; x++) invv[x] = -1;
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (mt[x * G + y] == 0) { invv[x] = y; break; }
}

/* Uncovered (source, vertex) pairs from A_e and B_e within DIAM steps. 0 iff valid. */
static long long eval_cost(void) {
    for (int t = 0; t < DEG; t++) Si[t] = invv[S[t]];
    long long total = 0;
    int N2 = 2 * G;
    for (int side = 0; side < 2; side++) {
        int src = side ? G : 0;
        stc++;
        if (stc >= 2000000000) {
            memset(stp, 0, sizeof(int) * (size_t)(2 * GMAX));
            stc = 1;
        }
        int head = 0, tail = 0;
        qb[tail++] = src;
        stp[src] = stc;
        for (int lvl = 0; lvl < DIAM; lvl++) {
            int end = tail;
            if (head == end) break;
            for (int i = head; i < end; i++) {
                int v = qb[i];
                if (v < G) {
                    const int base = v * G;
                    for (int t = 0; t < DEG; t++) {
                        int w = G + mt[base + S[t]];
                        if (stp[w] != stc) { stp[w] = stc; qb[tail++] = w; }
                    }
                } else {
                    const int base = (v - G) * G;
                    for (int t = 0; t < DEG; t++) {
                        int w = mt[base + Si[t]];
                        if (stp[w] != stc) { stp[w] = stc; qb[tail++] = w; }
                    }
                }
            }
            head = end;
        }
        total += N2 - tail;
    }
    return total;
}

static void random_init(void) {
    for (int t = 0; t < DEG; t++) {
        int v, ok;
        do {
            v = rnd_int(G);
            ok = 1;
            for (int j = 0; j < t; j++) if (S[j] == v) { ok = 0; break; }
        } while (!ok);
        S[t] = v;
    }
}

/* Simulated annealing on S. Returns the best cost; S ends at the best state. */
static long long anneal(int iters, double t0, double t1) {
    long long cur = eval_cost();
    long long best = cur;
    memcpy(bestS, S, sizeof(int) * (size_t)DEG);
    for (int it = 0; it < iters && best > 0; it++) {
        if ((it & 255) == 0 && elapsed() > DEADLINE) break;
        int t = rnd_int(DEG);
        int nw = rnd_int(G);
        int dup = 0;
        for (int j = 0; j < DEG; j++) if (S[j] == nw) { dup = 1; break; }
        if (dup) continue;
        int old = S[t];
        S[t] = nw;
        long long c = eval_cost();
        double temp = t0 * pow(t1 / t0, (double)it / iters);
        if (c <= cur || rnd_unit() < exp(-(double)(c - cur) / temp)) {
            cur = c;
            if (c < best) {
                best = c;
                memcpy(bestS, S, sizeof(int) * (size_t)DEG);
            }
        } else {
            S[t] = old;
        }
    }
    memcpy(S, bestS, sizeof(int) * (size_t)DEG);
    return best;
}

static void emit(void) {
    int m = DEG * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < DEG; t++)
        for (int x = 0; x < G; x++) {
            best_e[idx++] = x;
            best_e[idx++] = G + mt[x * G + S[t]];
        }
    best_m = m;
    best_n = 2 * G;
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
    best_n = start_n;
    best_m = 0;
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    Rpow = malloc(sizeof(int) * GMAX);
    mt = malloc(sizeof(int) * (size_t)GMAX * GMAX);
    invv = malloc(sizeof(int) * GMAX);
    S = malloc(sizeof(int) * DEG);
    Si = malloc(sizeof(int) * DEG);
    bestS = malloc(sizeof(int) * DEG);
    stp = calloc((size_t)(2 * GMAX), sizeof(int));
    qb = malloc(sizeof(int) * (size_t)(2 * GMAX));

    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    /* Bipartite Moore bound is 2*sum_{i<DIAM} (DEG-1)^i, so |G| <= sum. */
    long long sumv = 0, p = 1;
    for (int i = 0; i < DIAM; i++) {
        sumv += p;
        p *= (DEG - 1);
        if (sumv > 10000000LL) break;
    }
    int Ghi = (int)(sumv < GMAX ? sumv : GMAX);

    while (elapsed() < DEADLINE) {
        int lo = best_n / 2 + 1;
        if (lo < DEG) lo = DEG;
        if (lo < 2) lo = 2;
        if (lo > Ghi) break;
        int span = Ghi - lo;
        int g;
        if (rnd_unit() < 0.5) {
            int w = span < 40 ? span : 40;
            g = lo + rnd_int(w + 1);
        } else {
            g = lo + rnd_int(span + 1);
        }

        int divs[64], nd = 0;
        for (int d = 1; d <= g && nd < 64; d++)
            if (g % d == 0) divs[nd++] = d;
        int k2 = divs[rnd_int(nd)];
        int m = g / k2;
        int r = 1 % m;
        if (k2 > 1 && m > 2) {
            for (int tr = 0; tr < TRIES_R; tr++) {
                int cand = 2 + rnd_int(m - 2);
                if (gcd_i(cand, m) == 1 && powmod(cand, k2, m) == 1 % m) {
                    r = cand;
                    break;
                }
            }
        }
        if (g < DEG) continue;

        build_group(m, k2, r);
        random_init();
        long long bc = anneal(ITERS, 2.0, 0.05);
        if (bc == 0 && 2 * G > best_n) emit();
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
# Safe baseline families (valid fallbacks).
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


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then the C Haar-group search for a larger graph.
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

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Give the C search almost all of the budget. The reserve covers a cold
    # compile, parsing and validation.
    remaining = 0.94 * time_limit - (time.monotonic() - start) - 2.0
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 10.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
