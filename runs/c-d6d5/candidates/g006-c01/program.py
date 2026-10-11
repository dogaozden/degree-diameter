import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New construction family: bipartite Haar (Cayley-type) graphs over
# non-abelian metacyclic groups Z_m x|_r Z_k.
#
# Vertices A_x and B_y for x, y in G (|G| = N). Each A_x is joined to B_{x*s}
# for s in S, where S is a set of DEG distinct group elements. Left
# multiplication is an automorphism, so only two BFS runs (from A_e and B_e,
# to depth DIAM) are needed to test diameter. The search is simulated annealing
# over S, with the number of unreached vertex pairs as cost. Groups are chosen
# among those of order just above half the best known vertex count, with a bias
# toward non-abelian actions (r != 1), since abelian groups repeat words too often.
#
# This differs from the voltage-lift family (K base vertices per side with
# permutation layers): here every layer is a single right translation, and the
# group is searched over all metacyclic orders near the target.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXDEG 16
#define GCAP 512
#define ANNEAL_ITERS 4000
#define ANNEAL_T0 2.0

typedef struct { int m, k, r; } Grp;

static struct timespec T0;
static double DEADLINE;
static uint64_t rs[2];

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
static int N, GM, GK, GR;
static int *mul = NULL, *inv = NULL, *Rp = NULL;
static int S[MAXDEG], Sinv[MAXDEG], bestS[MAXDEG];
static int *stamp = NULL, *fr = NULL, *nx = NULL;
static int curstamp = 0;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;
static Grp grp[GCAP];

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

/* Group Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
static void setup_group(int m, int k, int r) {
    GM = m; GK = k; GR = r; N = m * k;
    free(mul); free(inv); free(Rp); free(stamp); free(fr); free(nx);
    mul = malloc(sizeof(int) * (size_t)N * (size_t)N);
    inv = malloc(sizeof(int) * (size_t)N);
    Rp = malloc(sizeof(int) * (size_t)k);
    stamp = calloc((size_t)2 * N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)2 * N);
    nx = malloc(sizeof(int) * (size_t)2 * N);
    curstamp = 0;
    Rp[0] = 1 % m;
    for (int b = 1; b < k; b++) Rp[b] = (int)((long long)Rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int ax = x / k, bx = x % k;
        for (int y = 0; y < N; y++) {
            int cy = y / k, ey = y % k;
            int ra = (int)(((long long)ax + (long long)Rp[bx] * cy) % m);
            int rb = (bx + ey) % k;
            mul[(size_t)x * N + y] = ra * k + rb;
        }
    }
    for (int x = 0; x < N; x++) {
        inv[x] = -1;
        for (int y = 0; y < N; y++) {
            if (mul[(size_t)x * N + y] == 0) { inv[x] = y; break; }
        }
    }
}

static int enum_groups(int n, Grp *out, int cap) {
    int cnt = 0;
    for (int k = 1; k <= n; k++) {
        if (n % k) continue;
        int m = n / k;
        if (m == 1) {
            if (cnt < cap) { out[cnt].m = 1; out[cnt].k = k; out[cnt].r = 0; cnt++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (cnt < cap) { out[cnt].m = m; out[cnt].k = k; out[cnt].r = r; cnt++; }
        }
    }
    return cnt;
}

/* Unreached (vertex, source) pairs within DIAM from A_e and from B_e. Zero means valid. */
static long long eval_cost(void) {
    long long total = 0;
    const int V = 2 * N;
    for (int rep = 0; rep < 2; rep++) {
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)V);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        int src = (rep == 0) ? 0 : N;
        f[0] = src;
        stamp[src] = curstamp;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                int v = f[q];
                if (v < N) {
                    const int *row = mul + (size_t)v * N;
                    for (int i = 0; i < DEG; i++) {
                        int w = N + row[S[i]];
                        if (stamp[w] != curstamp) { stamp[w] = curstamp; h[nsz++] = w; }
                    }
                } else {
                    const int *row = mul + (size_t)(v - N) * N;
                    for (int i = 0; i < DEG; i++) {
                        int w = row[Sinv[i]];
                        if (stamp[w] != curstamp) { stamp[w] = curstamp; h[nsz++] = w; }
                    }
                }
            }
            count += nsz;
            int *tmp = f; f = h; h = tmp;
            fsz = nsz;
        }
        total += V - count;
    }
    return total;
}

static void random_S(void) {
    for (int i = 0; i < DEG; i++) {
        int c, ok;
        do {
            c = rnd_int(N);
            ok = 1;
            for (int j = 0; j < i; j++) if (S[j] == c) { ok = 0; break; }
        } while (!ok);
        S[i] = c;
        Sinv[i] = inv[c];
    }
}

static long long anneal(int iters, double t0) {
    long long cost = eval_cost();
    long long bestc = cost;
    memcpy(bestS, S, sizeof(int) * (size_t)DEG);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 31) == 0 && elapsed() > DEADLINE) break;
        double temp = t0 * (1.0 - (double)it / iters) + 0.05;
        int i = rnd_int(DEG);
        int c, ok;
        do {
            c = rnd_int(N);
            ok = 1;
            for (int j = 0; j < DEG; j++) if (S[j] == c) { ok = 0; break; }
        } while (!ok);
        int old = S[i], oldinv = Sinv[i];
        S[i] = c;
        Sinv[i] = inv[c];
        long long c2 = eval_cost();
        if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < bestc) {
                bestc = cost;
                memcpy(bestS, S, sizeof(int) * (size_t)DEG);
            }
        } else {
            S[i] = old;
            Sinv[i] = oldinv;
        }
    }
    return bestc;
}

/* Emit the Haar graph for the connection set bestS: A_x = x, B_y = N + y, A_x ~ B_{x*s}. */
static void emit(void) {
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)N * DEG);
    int idx = 0;
    for (int x = 0; x < N; x++) {
        for (int i = 0; i < DEG; i++) {
            best_e[idx++] = x;
            best_e[idx++] = N + mul[(size_t)x * N + bestS[i]];
        }
    }
    best_m = N * DEG;
    best_n = 2 * N;
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
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        int half = best_n / 2;
        int target = half + 1 + rnd_int(6);
        if (target <= DEG) target = DEG + 1;

        int ng = enum_groups(target, grp, GCAP);
        if (ng == 0) continue;
        int pick = rnd_int(ng);
        if (rnd_unit() < 0.75) {
            for (int t = 0; t < 8; t++) {
                int c = rnd_int(ng);
                if (grp[c].r != 1 % grp[c].m) { pick = c; break; }
            }
        }

        setup_group(grp[pick].m, grp[pick].k, grp[pick].r);
        random_S();
        long long bc = anneal(ANNEAL_ITERS, ANNEAL_T0);
        if (bc == 0 && 2 * N > best_n) {
            emit();
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q <= 5 for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then the C Haar-graph search over metacyclic groups.
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

    # Wall-clock deadline inside C; leave room for compile, parsing and validation.
    remaining = 0.85 * time_limit - (time.monotonic() - start) - 1.0
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
