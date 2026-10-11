import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New construction family: bipartite Cayley-type graphs (Haar graphs) over
# semidirect products G = Z_m x| Z_k, with r^k = 1 mod m.
#
# Vertices: A_g = g and B_h = N + h, with N = |G|. The connection set S has
# DEG distinct group elements s_j, and A_g ~ B_{g s_j}. Every vertex has
# degree DEG. Left multiplication is an automorphism of each side, so the
# diameter is at most DIAM iff BFS of depth DIAM from A_e and from B_e
# reaches all 2N vertices.
#
# Search: for each group order N (climbing upward from the best order found
# so far), simulated annealing over the connection set S. Each move replaces
# one element of S with a new element. The cost is the number of uncovered
# (source, target) pairs from the two representatives. A zero-cost state is
# a valid graph, so it is stored and the search moves to larger N.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define ITERS 20000
#define KMAX 12
#define RTRIES 300
#define SPREAD 4

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;
static int DEG, DIAM;
static int N, K, M;
static int *Rpow = NULL;
static int *S = NULL, *invS = NULL, *bestS = NULL;
static int *adj = NULL, *stamp = NULL, *bufA = NULL, *bufB = NULL;
static int stampc = 0;
static int *out_e = NULL;
static int out_m = 0, out_n = 0;

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

/* Element (a,b) is coded as a*K + b. (a,b)*(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / K, b = x % K;
    int c = y / K, e = y % K;
    long long ra = ((long long)a + (long long)Rpow[b] * c) % M;
    int rb = (b + e) % K;
    return (int)ra * K + rb;
}

/* Inverse of (a,b) is (-r^(-b) a, -b). */
static int ginv(int x) {
    int a = x / K, b = x % K;
    int nb = (K - b) % K;
    long long c = (M - ((long long)a * Rpow[nb]) % M) % M;
    return (int)c * K + nb;
}

static void free_group(void) {
    free(Rpow); free(S); free(invS); free(bestS);
    free(adj); free(stamp); free(bufA); free(bufB);
    Rpow = NULL; S = invS = bestS = NULL;
    adj = stamp = bufA = bufB = NULL;
}

static void setup(int n, int k, int m, int r) {
    free_group();
    N = n; K = k; M = m;
    Rpow = malloc(sizeof(int) * (size_t)K);
    Rpow[0] = 1 % M;
    for (int b = 1; b < K; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * r % M);
    S = malloc(sizeof(int) * (size_t)DEG);
    invS = malloc(sizeof(int) * (size_t)DEG);
    bestS = malloc(sizeof(int) * (size_t)DEG);
    adj = malloc(sizeof(int) * (size_t)2 * N * DEG);
    stamp = calloc((size_t)2 * N, sizeof(int));
    bufA = malloc(sizeof(int) * (size_t)2 * N);
    bufB = malloc(sizeof(int) * (size_t)2 * N);
    stampc = 0;
}

static void random_S(void) {
    for (int j = 0; j < DEG; j++) {
        int x, ok;
        do {
            x = rnd_int(N);
            ok = 1;
            for (int i = 0; i < j; i++)
                if (S[i] == x) { ok = 0; break; }
        } while (!ok);
        S[j] = x;
    }
}

/* Total uncovered (source, target) pairs from A_0 and B_0. Zero iff valid. */
static long long eval_S(void) {
    int twoN = 2 * N;
    for (int j = 0; j < DEG; j++) invS[j] = ginv(S[j]);
    for (int g = 0; g < N; g++)
        for (int j = 0; j < DEG; j++)
            adj[(size_t)g * DEG + j] = N + gmul(g, S[j]);
    for (int h = 0; h < N; h++)
        for (int j = 0; j < DEG; j++)
            adj[(size_t)(N + h) * DEG + j] = gmul(h, invS[j]);

    long long total = 0;
    for (int s = 0; s < 2; s++) {
        int src = s * N;
        if (stampc >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)twoN);
            stampc = 0;
        }
        stampc++;
        int *f = bufA, *h = bufB;
        int fsz = 1, cnt = 1;
        f[0] = src;
        stamp[src] = stampc;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                const int *au = adj + (size_t)f[q] * DEG;
                for (int j = 0; j < DEG; j++) {
                    int v = au[j];
                    if (stamp[v] != stampc) {
                        stamp[v] = stampc;
                        h[nsz++] = v;
                    }
                }
            }
            cnt += nsz;
            int *tmp = f; f = h; h = tmp;
            fsz = nsz;
        }
        total += twoN - cnt;
    }
    return total;
}

/* Store the current (valid) configuration as the output graph. */
static void emit_best(void) {
    free(out_e);
    out_n = 2 * N;
    out_m = N * DEG;
    out_e = malloc(sizeof(int) * 2 * (size_t)out_m);
    int idx = 0;
    for (int g = 0; g < N; g++)
        for (int j = 0; j < DEG; j++) {
            out_e[idx++] = g;
            out_e[idx++] = N + gmul(g, bestS[j]);
        }
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
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    /* Need 2N > start_n, so N >= start_n/2 + 1, and N >= DEG so S can hold DEG distinct elements. */
    int cur_lo = start_n / 2 + 1;
    if (cur_lo < DEG) cur_lo = DEG;
    if (cur_lo < 2) cur_lo = 2;

    while (elapsed() < DEADLINE) {
        int Nn = cur_lo + rnd_int(SPREAD);

        /* Choose a semidirect product Z_m x| Z_k with m*k = Nn. */
        int ks[KMAX + 1], nk = 0;
        for (int k = 1; k <= KMAX && k <= Nn; k++)
            if (Nn % k == 0 && Nn / k >= 2) ks[nk++] = k;
        int k = ks[rnd_int(nk)];
        int m = Nn / k, r = 1;
        if (k > 1) {
            int found = 0;
            for (int tr = 0; tr < RTRIES && !found; tr++) {
                int cand = 1 + rnd_int(m - 1);
                if (gcd_i(cand, m) == 1 && powmod(cand, k, m) == 1 % m) {
                    r = cand;
                    found = 1;
                }
            }
            if (!found) { k = 1; m = Nn; r = 1; }
        }

        setup(Nn, k, m, r);
        random_S();
        long long cur = eval_S();
        for (int it = 0; it < ITERS && cur > 0; it++) {
            if ((it & 127) == 0 && elapsed() > DEADLINE) break;
            double temp = 2.0 * (1.0 - (double)it / ITERS) + 0.05;
            int j = rnd_int(DEG);
            int x = rnd_int(N);
            int dup = 0;
            for (int i = 0; i < DEG; i++)
                if (S[i] == x) { dup = 1; break; }
            if (dup) continue;
            int old = S[j];
            S[j] = x;
            long long c = eval_S();
            if (c <= cur || rnd_unit() < exp(-(double)(c - cur) / temp)) {
                cur = c;
            } else {
                S[j] = old;
            }
        }
        if (cur == 0) {
            memcpy(bestS, S, sizeof(int) * (size_t)DEG);
            emit_best();
            cur_lo = Nn + 1;
        }
    }

    if (out_m > 0) {
        printf("%d %d\n", out_n, out_m);
        for (int i = 0; i < out_m; i++)
            printf("%d %d\n", out_e[2 * i], out_e[2 * i + 1]);
    } else {
        printf("0 0\n");
    }
    free_group();
    free(out_e);
    return 0;
}
"""


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


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then the C Cayley-type annealer.
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

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    remaining = 0.85 * time_limit - (time.monotonic() - start) - 1.0
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 5.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
