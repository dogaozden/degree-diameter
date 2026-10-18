import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lifts over Z_m x| Z_k2, searched with simulated annealing.
#
# Each trial samples a group and a base size k, builds a random layered base
# (d perfect matchings between k A-blocks and k B-blocks, each dart carrying a
# voltage in the group), and anneals until every vertex reaches every block
# representative within D steps. Left multiplication is an automorphism, so
# the 2k representatives cover all distances. The best valid graph found is
# printed as "n m" plus edges. Bandit over k, group sampling and time control
# all live in C.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define KMAX 5
#define PEN 1000L

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static long rndint(long n) { return (long)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_sec(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

typedef struct {
    int d, D, k, k2, m;
    long G, N;
    long *pw;     /* pw[b] = r^b mod m */
    int *nbr;     /* nbr[l*N + v] */
    int *lay;     /* lay[l*k + i] = B-block paired with A-block i in layer l */
    long *vol;    /* vol[l*k + i] = voltage of that dart */
} St;

static long best_n = 0;
static int *best_e = NULL;
static long best_m = 0;

/* Element (a,b) is coded as a*k2 + b; (a,b)(c,e) = (a + r^b c, b + e). */
static long gmul(const St *s, long x, long y) {
    long K = s->k2, M = s->m;
    long a = x / K, b = x % K, c = y / K, e = y % K;
    long na = (a + s->pw[b] * c) % M;
    long nb = (b + e) % K;
    return na * K + nb;
}

static long ginv(const St *s, long x) {
    long K = s->k2, M = s->m;
    long a = x / K, b = x % K;
    long nb = (K - b) % K;
    long na = (M - (s->pw[nb] * a) % M) % M;
    return na * K + nb;
}

/* Layer l: A-block i joined to B-block j with voltage sv: A_{i,g} ~ B_{j,g*sv}. */
static void set_dart(St *s, int l, int i, int j, long sv) {
    long G = s->G, N = s->N, kk = s->k;
    long si = ginv(s, sv);
    int *row = s->nbr + (long)l * N;
    for (long g = 0; g < G; g++) {
        row[(long)i * G + g] = (int)((kk + j) * G + gmul(s, g, sv));
        row[(kk + j) * G + g] = (int)((long)i * G + gmul(s, g, si));
    }
}

static long popc64(uint64_t x) {
    long c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

/* ra receives reach masks (bit b: block-representative b within D of v).
   Returns the number of unreached (vertex, representative) pairs. */
static long eval_reach(const St *s, uint64_t *ra, uint64_t *rb) {
    long N = s->N, G = s->G;
    int k = s->k, d = s->d, nb2 = 2 * k;
    size_t bytes = sizeof(uint64_t) * (size_t)N;
    memset(ra, 0, bytes);
    for (int b = 0; b < nb2; b++) ra[(long)b * G] = 1ULL << b;
    for (int t = 0; t < s->D; t++) {
        int changed = 0;
        for (long v = 0; v < N; v++) {
            uint64_t x = ra[v];
            for (int l = 0; l < d; l++) x |= ra[s->nbr[(long)l * N + v]];
            rb[v] = x;
            if (x != ra[v]) changed = 1;
        }
        if (!changed) break;
        memcpy(ra, rb, bytes);
    }
    uint64_t full = (1ULL << nb2) - 1;
    long un = 0;
    for (long v = 0; v < N; v++) un += nb2 - popc64(ra[v] & full);
    return un;
}

/* Number of duplicate darts: same A-block, same B-block, same voltage. */
static long dupcount(const St *s) {
    long total = (long)s->d * s->k, dup = 0;
    long k = s->k;
    for (long a = 0; a < total; a++) {
        long ia = a % k;
        for (long b = a + 1; b < total; b++) {
            if (ia == b % k && s->lay[a] == s->lay[b] && s->vol[a] == s->vol[b]) dup++;
        }
    }
    return dup;
}

static int anneal(St *s, long iters, long patience, double deadline,
                  uint64_t *cur, uint64_t *ra, uint64_t *rb) {
    int d = s->d, k = s->k;
    long N = s->N, G = s->G;
    uint64_t full = (1ULL << (2 * k)) - 1;
    size_t bytes = sizeof(uint64_t) * (size_t)N;

    long cost = eval_reach(s, cur, rb) + PEN * dupcount(s);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best = cost, last = 0;

    for (long t = 0; t < iters; t++) {
        if (cost == 0) return 1;
        if (t - last > patience) break;
        if ((t & 31) == 0 && now_sec() > deadline) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (k >= 2 && rnd01() < 0.25) {
            /* Layer-swap move: exchange B-targets of two A-blocks in one layer. */
            int l = (int)rndint(d);
            int i1 = (int)rndint(k);
            int i2 = (int)rndint(k - 1);
            if (i2 >= i1) i2++;
            int *L = s->lay + (long)l * k;
            long *V = s->vol + (long)l * k;
            int tmp = L[i1]; L[i1] = L[i2]; L[i2] = tmp;
            set_dart(s, l, i1, L[i1], V[i1]);
            set_dart(s, l, i2, L[i2], V[i2]);
            long c2 = eval_reach(s, ra, rb) + PEN * dupcount(s);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(cur, ra, bytes);
                if (cost < best) { best = cost; last = t; }
            } else {
                tmp = L[i1]; L[i1] = L[i2]; L[i2] = tmp;
                set_dart(s, l, i1, L[i1], V[i1]);
                set_dart(s, l, i2, L[i2], V[i2]);
            }
            continue;
        }

        /* Voltage move, defect-targeted with probability 0.4. */
        int l = (int)rndint(d);
        int i = (int)rndint(k);
        if (rnd01() < 0.4) {
            long v = -1;
            for (int tr = 0; tr < 50; tr++) {
                long cand = rndint(N);
                if (cur[cand] != full) { v = cand; break; }
            }
            if (v >= 0) {
                long blk = v / G;
                if (blk < k) {
                    i = (int)blk;
                } else {
                    int jb = (int)(blk - k);
                    for (int ii = 0; ii < k; ii++) {
                        if (s->lay[(long)l * k + ii] == jb) { i = ii; break; }
                    }
                }
            }
        }
        long *V = s->vol + (long)l * k;
        long old = V[i];
        long nw = rndint(G);
        if (nw == old) continue;
        V[i] = nw;
        set_dart(s, l, i, s->lay[(long)l * k + i], nw);
        long c2 = eval_reach(s, ra, rb) + PEN * dupcount(s);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(cur, ra, bytes);
            if (cost < best) { best = cost; last = t; }
        } else {
            V[i] = old;
            set_dart(s, l, i, s->lay[(long)l * k + i], old);
        }
    }
    return cost == 0;
}

static long gcdl(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static const int K2_CH[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

/* Sample Z_m x| Z_k2 with m*k2 >= target, returns 1 on success. */
static int sample_group(long target, int *mo, int *ko, int *ro) {
    for (int at = 0; at < 200; at++) {
        int k2 = K2_CH[rndint(20)];
        long m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        long r;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rnd01() < 0.3) {
            r = m - 1;
        } else if (m <= 2) {
            r = 1;
        } else {
            r = -1;
            for (int tr = 0; tr < 60; tr++) {
                long c = 2 + rndint(m - 2);
                if (gcdl(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
            }
            if (r < 0) continue;
        }
        *mo = (int)m;
        *ko = k2;
        *ro = (int)r;
        return 1;
    }
    return 0;
}

static int pick_k(const long *trials, const long *wins) {
    if (rnd01() < 0.2) return 1 + (int)rndint(KMAX);
    int bk = 1;
    double bs = -1.0;
    for (int k = 1; k <= KMAX; k++) {
        double sc = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (sc > bs) { bs = sc; bk = k; }
    }
    return bk;
}

static void store_best(const St *s) {
    long kG = (long)s->k * s->G;
    long m = kG * s->d;
    int *e = malloc(sizeof(int) * 2 * (size_t)m);
    if (!e) return;
    long c = 0;
    for (long u = 0; u < kG; u++) {
        for (int l = 0; l < s->d; l++) {
            e[2 * c] = (int)u;
            e[2 * c + 1] = s->nbr[(long)l * s->N + u];
            c++;
        }
    }
    free(best_e);
    best_e = e;
    best_m = m;
    best_n = s->N;
}

static int run_one(St *s, int d, int D, int k, int m, int k2, int r, double deadline) {
    long G = (long)m * k2;
    long N = 2L * k * G;
    s->d = d; s->D = D; s->k = k; s->k2 = k2; s->m = m;
    s->G = G; s->N = N;
    s->pw = malloc(sizeof(long) * (size_t)k2);
    s->pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) s->pw[b] = s->pw[b - 1] * r % m;
    s->nbr = malloc(sizeof(int) * (size_t)d * (size_t)N);
    s->lay = malloc(sizeof(int) * (size_t)d * (size_t)k);
    s->vol = malloc(sizeof(long) * (size_t)d * (size_t)k);
    uint64_t *cur = malloc(sizeof(uint64_t) * (size_t)N);
    uint64_t *ra = malloc(sizeof(uint64_t) * (size_t)N);
    uint64_t *rb = malloc(sizeof(uint64_t) * (size_t)N);
    if (!s->pw || !s->nbr || !s->lay || !s->vol || !cur || !ra || !rb) {
        free(s->pw); free(s->nbr); free(s->lay); free(s->vol);
        free(cur); free(ra); free(rb);
        return 0;
    }
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) s->lay[l * k + i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = (int)rndint(i + 1);
            int tmp = s->lay[l * k + i];
            s->lay[l * k + i] = s->lay[l * k + j];
            s->lay[l * k + j] = tmp;
        }
        for (int i = 0; i < k; i++) s->vol[l * k + i] = rndint(G);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++)
            set_dart(s, l, i, s->lay[l * k + i], s->vol[l * k + i]);

    int ok = anneal(s, 12000, 2000, deadline, cur, ra, rb);
    if (ok && N > best_n) store_best(s);

    free(s->pw); free(s->nbr); free(s->lay); free(s->vol);
    free(cur); free(ra); free(rb);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    long start_n = argc > 5 ? atol(argv[5]) : 0;

    char drain[4096];
    while (fread(drain, 1, sizeof drain, stdin) > 0) {}

    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();

    best_n = start_n;
    if (d < 3 || d > 60 || D < 2) {
        printf("0 0\n");
        return 0;
    }

    double deadline = now_sec() + budget;
    long trials[KMAX + 1], wins[KMAX + 1];
    memset(trials, 0, sizeof trials);
    memset(wins, 0, sizeof wins);

    while (now_sec() < deadline) {
        int k = pick_k(trials, wins);
        long base = best_n / (2L * k);
        long spread = base / 8 + 1;
        if (spread < 2) spread = 2;
        long target = base + 1 + rndint(spread);
        if (target < 2) target = 2;
        int m, k2, r;
        if (!sample_group(target, &m, &k2, &r)) continue;
        long G = (long)m * k2;
        if (2L * k * G <= best_n) continue;
        trials[k]++;
        St s;
        memset(&s, 0, sizeof s);
        if (run_one(&s, d, D, k, m, k2, r, deadline)) wins[k]++;
    }

    if (best_e == NULL) {
        printf("0 0\n");
        return 0;
    }
    printf("%ld %ld\n", best_n, best_m);
    for (long i = 0; i < best_m; i++) printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: exact constructions, the C search, and a safe fallback.
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

    # Exact constructions return immediately (calibration-style cases).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() - start < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search in C: budget leaves room for compile, parsing and validation.
    elapsed = time.monotonic() - start
    budget = min(0.8 * time_limit, time_limit - 8.0, time_limit - elapsed - 6.0)
    if budget >= 1.0 and d >= 3:
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, seed & 0xFFFFFFFF, f"{budget:.2f}", best_n],
                stdin_graph=None,
                timeout=budget + 5.0,
            )
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
