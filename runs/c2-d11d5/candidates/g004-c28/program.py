"""Ratchet bi-Cayley lift search (C engine) with a safe algebraic fallback.

Change from the parent: the C engine no longer restarts from random orders near the
current best. It ratchets. Each successful lift raises the target order by a small
random step, and the base size k ranges up to 16 (bitmask reachability over 2k blocks),
so layer patterns over many base vertices can be explored. Groups are sampled from
Z_m x| Z_k2 with orders chosen so that 2*k*|G| is just above the current best.

Python glue: the exact constructions (projective plane; generalized quadrangle only
when D = 4) give the fallback. The C result is checked with lib.is_valid before it is
kept. Any C failure falls back to the best valid graph found so far. Slack extension
was dropped: in a regular lift every vertex has full degree, so it adds nothing and
costs many is_valid calls.
"""
import itertools
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

#define MAXD 64
#define MAXK 16
#define MAXG 8192
#define PENALTY 1000

typedef uint64_t u64;

static u64 rs;
static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int rndint(int n) { int v = (int)(rndu() * n); return v >= n ? n - 1 : v; }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long gcdll(long long a, long long b) {
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
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

typedef struct { int m, k2, G; long long r; int pw[64]; } Group;
static Group grp;

static void set_group(int m, int k2, long long r) {
    grp.m = m; grp.k2 = k2; grp.G = m * k2; grp.r = r;
    long long p = 1 % m;
    for (int b = 0; b < k2; b++) { grp.pw[b] = (int)p; p = (p * r) % m; }
}

/* element a*k2+b ; (a,b)(c,e) = (a + r^b c, b + e) */
static int gmul(int x, int y) {
    int k2 = grp.k2, m = grp.m;
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long long t = (a + (long long)grp.pw[b] * c) % m;
    return (int)(t * k2 + (b + e) % k2);
}

/* inverse of (a,b) is (-r^(-b) a, -b) */
static int ginv(int x) {
    int k2 = grp.k2, m = grp.m;
    int a = x / k2, b = x % k2;
    int nb = (k2 - b) % k2;
    long long t = ((long long)grp.pw[nb] * a) % m;
    long long na = (m - t) % m;
    return (int)(na * k2 + nb);
}

static int DEG, D_, K, G, N;
static int layers[MAXD][MAXK];
static int S[MAXD][MAXK];
static int *nbr = NULL;     /* nbr[l*N + v] */
static u64 *ra = NULL, *rb = NULL;
static u64 FULL;

static int best_n = 0, best_m = 0;
static int *best_e = NULL;

static void set_dart(int l, int i) {
    int p = layers[l][i], s = S[l][i];
    int sinv = ginv(s);
    int *nl = nbr + (size_t)l * N;
    int q = K + p;
    for (int g = 0; g < G; g++) nl[i * G + g] = q * G + gmul(g, s);
    for (int h = 0; h < G; h++) nl[q * G + h] = i * G + gmul(h, sinv);
}

/* The graph is invariant under left multiplication, so reachability from the identity
   of each of the 2K blocks decides the diameter. */
static int reach_eval(void) {
    for (int v = 0; v < N; v++) ra[v] = 0;
    for (int b = 0; b < 2 * K; b++) ra[b * G] |= (u64)1 << b;
    for (int round = 0; round < D_; round++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 u = ra[v];
            for (int l = 0; l < DEG; l++) u |= ra[nbr[(size_t)l * N + v]];
            rb[v] = u;
            if (u != ra[v]) changed = 1;
        }
        u64 *t = ra; ra = rb; rb = t;
        if (!changed) break;
    }
    int unr = 0;
    for (int v = 0; v < N; v++) unr += pc64(FULL & ~ra[v]);
    return unr;
}

static long long eval_cost(void) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < DEG; l++)
            for (int l2 = l + 1; l2 < DEG; l2++)
                if (layers[l][i] == layers[l2][i] && S[l][i] == S[l2][i]) dup++;
    int unr = reach_eval();
    return (long long)unr + (long long)PENALTY * dup;
}

static void record_solution(void) {
    int m = K * G * DEG;
    int *e = malloc(sizeof(int) * 2 * (size_t)m);
    if (!e) return;
    int idx = 0;
    for (int u = 0; u < K * G; u++)
        for (int l = 0; l < DEG; l++) {
            e[2 * idx] = u;
            e[2 * idx + 1] = nbr[(size_t)l * N + u];
            idx++;
        }
    free(best_e);
    best_e = e;
    best_m = m;
    best_n = N;
}

static int anneal(long iters, long patience, double deadline) {
    long long cost = eval_cost();
    double c0 = cost > 1 ? (double)cost : 1.0;
    long long bestc = cost;
    long last = 0;
    for (long t = 0; t < iters; t++) {
        if (cost == 0) return 1;
        if ((t & 15) == 0 && now() > deadline) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rndu() < 0.25) {
            int l = rndint(DEG);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = tmp;
            set_dart(l, i1); set_dart(l, i2);
            long long c2 = eval_cost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                tmp = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = tmp;
                set_dart(l, i1); set_dart(l, i2);
            }
            continue;
        }

        int l = -1, i = -1;
        if (rndu() < 0.4) {
            for (int tries = 0; tries < 30 && l < 0; tries++) {
                int v = rndint(N);
                if ((ra[v] & FULL) != FULL) {
                    int block = v / G;
                    if (block < K) {
                        i = block;
                        l = rndint(DEG);
                    } else {
                        l = rndint(DEG);
                        for (int j = 0; j < K; j++)
                            if (layers[l][j] == block - K) { i = j; break; }
                    }
                }
            }
        }
        if (l < 0) { l = rndint(DEG); i = rndint(K); }

        int old = S[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        S[l][i] = nw;
        set_dart(l, i);
        long long c2 = eval_cost();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < bestc) { bestc = cost; last = t; }
        } else {
            S[l][i] = old;
            set_dart(l, i);
        }
    }
    return cost == 0;
}

static const int K2LIST[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static int sample_group(int target, int *pm, int *pk2, long long *pr) {
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2LIST[rndint(20)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (m * k2 > MAXG) continue;
        long long r = -1;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rndu() < 0.3) {
            r = m - 1;
        } else {
            if (m > 2) {
                for (int t = 0; t < 60; t++) {
                    long long c = 2 + rndint(m - 2);
                    if (gcdll(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
                }
            } else {
                r = 1;
            }
            if (r < 0) continue;
        }
        *pm = m; *pk2 = k2; *pr = r;
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int n0 = argc > 5 ? atoi(argv[5]) : 0;
    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    DEG = d;
    D_ = D;
    rs = 0x9E3779B97F4A7C15ULL ^ (u64)(seed * 2654435761UL + 12345UL);
    if (rs == 0) rs = 1;
    for (int w = 0; w < 10; w++) rnd64();

    double start = now(), deadline = start + tl;
    best_n = n0;
    best_m = 0;
    best_e = NULL;
    int trials[MAXK + 1] = {0}, wins[MAXK + 1] = {0};

    while (now() < deadline) {
        int k;
        if (rndu() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bs = -1.0;
            k = 1;
            for (int kk = 1; kk <= MAXK; kk++) {
                double s = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rndu();
                if (s > bs) { bs = s; k = kk; }
            }
        }
        /* Ratchet: target order just above the current best. */
        int base = best_n / (2 * k);
        int spread = base / 16 + 2;
        int target = base + 1 + rndint(spread);
        if (target < 2) target = 2;

        int m, k2;
        long long r;
        if (!sample_group(target, &m, &k2, &r)) continue;
        set_group(m, k2, r);
        G = grp.G;
        K = k;
        N = 2 * K * G;
        if (N <= best_n) continue;

        FULL = (((u64)1) << (2 * K)) - 1;
        nbr = malloc(sizeof(int) * (size_t)DEG * N);
        ra = malloc(sizeof(u64) * (size_t)N);
        rb = malloc(sizeof(u64) * (size_t)N);
        if (!nbr || !ra || !rb) {
            free(nbr); free(ra); free(rb);
            nbr = NULL; ra = NULL; rb = NULL;
            break;
        }

        for (int l = 0; l < DEG; l++) {
            for (int i = 0; i < K; i++) layers[l][i] = i;
            for (int i = K - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int tmp = layers[l][i]; layers[l][i] = layers[l][j]; layers[l][j] = tmp;
            }
        }
        for (int l = 0; l < DEG; l++)
            for (int i = 0; i < K; i++) S[l][i] = rndint(G);
        for (int l = 0; l < DEG; l++)
            for (int i = 0; i < K; i++) set_dart(l, i);

        trials[K]++;
        int ok = anneal(8000, 1500, deadline);
        if (ok) {
            wins[K]++;
            record_solution();
        }
        free(nbr); free(ra); free(rb);
        nbr = NULL; ra = NULL; rb = NULL;
    }

    if (best_m == 0) {
        printf("0 0\n");
    } else {
        printf("%d %d\n", best_n, best_m);
        for (int j = 0; j < best_m; j++)
            printf("%d %d\n", best_e[2 * j], best_e[2 * j + 1]);
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Algebraic baselines.
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
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    # Leave margin for the C process shutdown and the final is_valid check.
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
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

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main engine: ratchet search over bi-Cayley lifts, seeded with the current best order.
    remaining = deadline - time.monotonic()
    if d >= 2 and remaining > 3.0:
        c_budget = max(1.0, 0.9 * remaining)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2), best_n],
                            stdin_graph=None, timeout=remaining + 2.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Final guard: the kept graph must be valid; otherwise fall back to K_{d,d}.
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
