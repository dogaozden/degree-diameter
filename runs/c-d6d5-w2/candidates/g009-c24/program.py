import itertools
import math
import time

import lib


# ----------------------------------------------------------------------------
# New construction family: Bi-Cayley graphs over finite groups.
#
# Vertices A_g = g and B_h = G + h for g, h in a group G of order N.
# Connection set S = {s_1..s_d} (distinct) gives edges A_g -- B_{g*s} for s in S.
# Every vertex has degree d and the graph is bipartite by construction.
# Left multiplication is an automorphism that preserves the A and B sides, so
# diameter <= D iff BFS of depth D from A_e and from B_e reaches all 2N vertices.
#
# Groups used: Heisenberg groups over Z_p (order p^3, nonabelian), semidirect
# products Z_m x| Z_k (nonabelian for r != 1), and cyclic groups. Nonabelian
# groups of order just above the record half-order are the main target.
#
# C search: simulated annealing over S, moving one element at a time, with the
# cost = number of unreached vertices from the two base points.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs[2];

static double nowsec(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

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

/* Group: type 0 = Z_A; type 1 = Heisenberg over Z_A (order A^3);
   type 2 = Z_A x| Z_B with r = GR (need r^B = 1 mod A). */
static int GT, GA, GB, GR, G, DEG, DIAM;
static int *tab = NULL;      /* tab[x*G+y] = x*y */
static int *inv_ = NULL;     /* inverses */
static int *Rp = NULL;       /* powers of r for type 2 */
static int *stamp = NULL, *fr = NULL, *nx = NULL;
static int curstamp = 0;
static int S[64], invS[64];

static int elem_mul(int x, int y) {
    if (GT == 0) {
        int s = x + y;
        return s >= GA ? s - GA : s;
    }
    if (GT == 1) {
        int p = GA;
        int a = x / (p * p), b = (x / p) % p, c = x % p;
        int a2 = y / (p * p), b2 = (y / p) % p, c2 = y % p;
        int na = (a + a2) % p, nb = (b + b2) % p;
        int nc = (c + c2 + a * b2) % p;
        return (na * p + nb) * p + nc;
    }
    int m = GA, k = GB;
    int a = x / k, b = x % k, c = y / k, e = y % k;
    int ra = (int)(((long long)a + (long long)Rp[b] * c) % m);
    int rb = (b + e) % k;
    return ra * k + rb;
}

static int setup_group(void) {
    if (GT == 0) {
        if (GA < 2) return 0;
        G = GA;
    } else if (GT == 1) {
        if (GA < 2) return 0;
        G = GA * GA * GA;
    } else if (GT == 2) {
        if (GA < 2 || GB < 2) return 0;
        G = GA * GB;
    } else {
        return 0;
    }
    if (G < 2 || G > 3000) return 0;
    if (GT == 2) {
        Rp = malloc(sizeof(int) * (size_t)GB);
        Rp[0] = 1 % GA;
        for (int b = 1; b < GB; b++) Rp[b] = (int)((long long)Rp[b - 1] * GR % GA);
    }
    tab = malloc(sizeof(int) * (size_t)G * G);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            tab[(size_t)x * G + y] = elem_mul(x, y);
    inv_ = malloc(sizeof(int) * (size_t)G);
    for (int x = 0; x < G; x++) {
        inv_[x] = -1;
        for (int y = 0; y < G; y++)
            if (tab[(size_t)x * G + y] == 0) { inv_[x] = y; break; }
        if (inv_[x] < 0) return 0;
    }
    stamp = calloc((size_t)2 * G, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)2 * G);
    nx = malloc(sizeof(int) * (size_t)2 * G);
    return 1;
}

static int inset_upto(int x, int lim) {
    for (int i = 0; i < lim; i++)
        if (S[i] == x) return 1;
    return 0;
}

/* Number of unreached (source, vertex) pairs from A_e and from B_e within DIAM. */
static long long evalS(void) {
    long long tot = 0;
    int N = 2 * G;
    for (int i = 0; i < DEG; i++) invS[i] = inv_[S[i]];
    for (int src = 0; src < 2; src++) {
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        int s0 = (src == 0) ? 0 : G;
        f[0] = s0;
        stamp[s0] = curstamp;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                int v = f[q];
                if (v < G) {
                    const int *row = tab + (size_t)v * G;
                    for (int j = 0; j < DEG; j++) {
                        int w = G + row[S[j]];
                        if (stamp[w] != curstamp) {
                            stamp[w] = curstamp;
                            h[nsz++] = w;
                        }
                    }
                } else {
                    const int *row = tab + (size_t)(v - G) * G;
                    for (int j = 0; j < DEG; j++) {
                        int w = row[invS[j]];
                        if (stamp[w] != curstamp) {
                            stamp[w] = curstamp;
                            h[nsz++] = w;
                        }
                    }
                }
            }
            count += nsz;
            int *tmp = f; f = h; h = tmp;
            fsz = nsz;
        }
        tot += N - count;
    }
    return tot;
}

static void emit(void) {
    long long m = (long long)G * DEG;
    printf("%d %lld\n", 2 * G, m);
    for (int g = 0; g < G; g++) {
        const int *row = tab + (size_t)g * G;
        for (int j = 0; j < DEG; j++)
            printf("%d %d\n", g, G + row[S[j]]);
    }
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 1;
    }
    double T0 = nowsec();
    GT = atoi(argv[1]);
    GA = atoi(argv[2]);
    GB = atoi(argv[3]);
    GR = atoi(argv[4]);
    DEG = atoi(argv[5]);
    DIAM = atoi(argv[6]);
    uint64_t sd = strtoull(argv[7], NULL, 10);
    double tlim = atof(argv[8]);
    double deadline = T0 + tlim;

    uint64_t sm = sd * 2654435761ULL + 99991ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    if (DEG < 1 || DIAM < 1 || DEG > 60 || !setup_group() || DEG > G) {
        printf("0 0\n");
        return 0;
    }

    const int ITERS = 30000;
    while (nowsec() < deadline) {
        for (int j = 0; j < DEG; j++) {
            int x;
            do { x = rnd_int(G); } while (inset_upto(x, j));
            S[j] = x;
        }
        long long cur = evalS();
        for (int it = 0; it < ITERS && cur > 0; it++) {
            if ((it & 255) == 0 && nowsec() > deadline) break;
            double temp = 1.5 * (1.0 - (double)it / ITERS) + 0.05;
            int j = rnd_int(DEG);
            int x;
            do { x = rnd_int(G); } while (inset_upto(x, DEG));
            int old = S[j];
            S[j] = x;
            long long c2 = evalS();
            if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / temp)) {
                cur = c2;
            } else {
                S[j] = old;
            }
        }
        if (cur == 0) {
            emit();
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: group enumeration and baselines.
# ----------------------------------------------------------------------------

def _primes_upto(n):
    return [p for p in range(2, n + 1) if all(p % q for q in range(2, int(p ** 0.5) + 1))]


def _group_specs(lo, hi):
    """Group specs (order, type, a, b, r) with lo <= order <= hi, smallest order first."""
    specs = []
    cube_root = int(round(hi ** (1.0 / 3.0))) + 1
    for p in _primes_upto(cube_root):
        g = p ** 3
        if lo <= g <= hi:
            specs.append((g, 1, p, 0, 0))
    for k in range(2, 11):
        m_lo = max(2, -(-lo // k))
        for m in range(m_lo, hi // k + 1):
            found = 0
            for r in range(2, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    specs.append((m * k, 2, m, k, r))
                    found += 1
                    if found == 2:
                        break
    specs.sort(key=lambda s: (s[0], s[1]))
    return specs[:60]


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
# Driver: safe baselines first, then Bi-Cayley group searches in C.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
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

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    # Bi-Cayley search: a group of order G gives n = 2G vertices.
    deadline = start + 0.88 * time_limit - 1.5
    lo = best_n // 2 + 1
    hi = min(moore // 2, 1500)
    if d >= 2 and hi >= lo:
        specs = _group_specs(lo, hi)
        for idx, (g, typ, a, b, r) in enumerate(specs):
            if 2 * g <= best_n:
                continue
            rem = deadline - time.monotonic()
            if rem < 0.8:
                break
            left = len(specs) - idx
            sl = min(4.0, max(0.8, rem / left))
            sl = min(sl, rem)
            try:
                out = lib.run_c(C_SOURCE, [typ, a, b, r, d, D, seed + idx, f"{sl:.2f}"],
                                timeout=sl + 8.0)
                n, e = lib.parse_graph_text(out)
            except Exception:
                continue
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
