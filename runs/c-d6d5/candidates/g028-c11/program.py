import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bipartite Haar (bi-Cayley) graphs H(G, S).
#
# For a finite group G of order N and a connection set S of size d, the graph
# has parts A_x and B_y (x, y in G) with A_x adjacent to B_{x s} for s in S.
# Every vertex has degree d, and left multiplication is an automorphism that
# is regular on each part. So the diameter is at most D iff BFS of depth D from
# A_1 and from B_1 reaches everything. The identity can be assumed to lie in S
# (right translation of S gives an isomorphic graph), so S[0] is fixed to 0.
#
# Groups: all semidirect products Z_m x|_r Z_k with m >= 2, m*k = N, r^k = 1
# mod m, gcd(r, m) = 1 (r = 1 gives the abelian case). The group is chosen
# uniformly among these for each attempted order.
#
# Search: for a target order N slightly above the current best (2N > best
# vertex count), try a random group and anneal over S (one element swapped at
# a time). The cost is the number of uncovered (source, vertex) pairs. A zero
# cost gives a valid graph on 2N vertices. Target orders are biased toward the
# current best so that easy improvements are found first.
#
# Input argv: d D seed time_limit start_n max_order. Output is "n m" plus edges,
# or "0 0" if nothing beats start_n.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXDEG 64
#define ITERS 20000

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;
static int DEG, DIAM;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

static int N;
static int *mt = NULL, *ginv = NULL, *Rpow = NULL;
static int S[MAXDEG], Sinv[MAXDEG];
static char *mark = NULL;
static int *stampv = NULL, *qu = NULL;
static int curst = 0;

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

static int powmod_i(long long b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static int valid_group(int m, int k, int r) {
    if (r < 1 || r >= m) return 0;
    if (gcd_i(r, m) != 1) return 0;
    return powmod_i(r, k, m) == 1 % m;
}

/* Count valid (m,k,r) with m*k = n, m >= 2 (idx < 0), or fill the idx-th one. */
static int group_pick(int n, int idx, int *om, int *ok, int *orr) {
    int cnt = 0;
    for (int k = 1; k <= n; k++) {
        if (n % k) continue;
        int m = n / k;
        if (m < 2) continue;
        for (int r = 1; r < m; r++) {
            if (!valid_group(m, k, r)) continue;
            if (idx >= 0 && cnt == idx) {
                *om = m; *ok = k; *orr = r;
                return 1;
            }
            cnt++;
        }
    }
    return cnt;
}

/* Multiplication table of Z_m x|_r Z_k, element (a,b) coded as a*k+b. */
static int build_group(int m, int k, int r) {
    N = m * k;
    free(mt); free(ginv); free(Rpow);
    mt = malloc(sizeof(int) * (size_t)N * (size_t)N);
    ginv = malloc(sizeof(int) * (size_t)N);
    Rpow = malloc(sizeof(int) * (size_t)k);
    Rpow[0] = 1 % m;
    for (int b = 1; b < k; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            long long ra = ((long long)a + (long long)Rpow[b] * c) % m;
            int rb = (b + e) % k;
            mt[(size_t)x * N + y] = (int)ra * k + rb;
        }
    }
    for (int x = 0; x < N; x++) {
        ginv[x] = -1;
        for (int y = 0; y < N; y++)
            if (mt[(size_t)x * N + y] == 0) { ginv[x] = y; break; }
        if (ginv[x] < 0) return 0;
    }
    return 1;
}

static void alloc_work(void) {
    free(mark); free(stampv); free(qu);
    mark = calloc((size_t)N, 1);
    stampv = calloc((size_t)(2 * N), sizeof(int));
    qu = malloc(sizeof(int) * (size_t)(2 * N));
    curst = 0;
}

/* BFS to depth DIAM from src (A nodes 0..N-1, B nodes N..2N-1). Returns #visited. */
static int bfs_cov(int src) {
    if (curst >= 2000000000) {
        memset(stampv, 0, sizeof(int) * (size_t)(2 * N));
        curst = 0;
    }
    curst++;
    int head = 0, tail = 1;
    qu[0] = src;
    stampv[src] = curst;
    for (int lvl = 0; lvl < DIAM && head < tail; lvl++) {
        int end = tail;
        for (int h = head; h < end; h++) {
            int v = qu[h];
            if (v < N) {
                for (int i = 0; i < DEG; i++) {
                    int w = N + mt[(size_t)v * N + S[i]];
                    if (stampv[w] != curst) { stampv[w] = curst; qu[tail++] = w; }
                }
            } else {
                int y = v - N;
                for (int i = 0; i < DEG; i++) {
                    int w = mt[(size_t)y * N + Sinv[i]];
                    if (stampv[w] != curst) { stampv[w] = curst; qu[tail++] = w; }
                }
            }
        }
        head = end;
    }
    return tail;
}

static long long eval_cost(void) {
    long long c1 = 2LL * N - bfs_cov(0);
    long long c2 = 2LL * N - bfs_cov(N);
    return c1 + c2;
}

static void recompute_inv(void) {
    for (int i = 0; i < DEG; i++) Sinv[i] = ginv[S[i]];
}

static void init_S(void) {
    memset(mark, 0, (size_t)N);
    S[0] = 0;
    mark[0] = 1;
    for (int i = 1; i < DEG; i++) {
        int g;
        do { g = rnd_int(N); } while (mark[g]);
        S[i] = g;
        mark[g] = 1;
    }
    recompute_inv();
}

/* Annealing over S with identity fixed in position 0. Returns best cost; S left at best state. */
static long long run_sa(long long cost, int iters) {
    long long bestc = cost;
    int bestS[MAXDEG];
    memcpy(bestS, S, sizeof(int) * (size_t)DEG);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 255) == 0 && elapsed() > DEADLINE) break;
        double frac = (double)it / (double)iters;
        double temp = 1.5 * (1.0 - frac) + 0.05;
        int i = 1 + rnd_int(DEG - 1);
        int old = S[i];
        int g;
        do { g = rnd_int(N); } while (mark[g]);
        mark[old] = 0; mark[g] = 1;
        S[i] = g; Sinv[i] = ginv[g];
        long long c2 = eval_cost();
        if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < bestc) {
                bestc = cost;
                memcpy(bestS, S, sizeof(int) * (size_t)DEG);
            }
        } else {
            mark[g] = 0; mark[old] = 1;
            S[i] = old; Sinv[i] = ginv[old];
        }
    }
    memcpy(S, bestS, sizeof(int) * (size_t)DEG);
    recompute_inv();
    memset(mark, 0, (size_t)N);
    for (int i = 0; i < DEG; i++) mark[S[i]] = 1;
    return bestc;
}

static void emit_best(void) {
    int m = DEG * N;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int x = 0; x < N; x++) {
        for (int i = 0; i < DEG; i++) {
            best_e[idx++] = x;
            best_e[idx++] = N + mt[(size_t)x * N + S[i]];
        }
    }
    best_m = m;
    best_n = 2 * N;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n [max_order]]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    best_n = argc > 5 ? atoi(argv[5]) : 0;
    int maxN = argc > 6 ? atoi(argv[6]) : 0;
    if (DEG < 2 || DEG > MAXDEG || DIAM < 2 || maxN <= DEG) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        int lo = best_n / 2 + 1;
        if (lo < DEG + 1) lo = DEG + 1;
        if (lo > maxN) break;
        /* Bias toward the low end so that easy improvements come first. */
        double u = rnd_unit();
        int Nt = lo + (int)((double)(maxN - lo + 1) * u * u);
        if (Nt > maxN) Nt = maxN;
        int om = 0, ok = 0, orr = 0;
        int cnt = group_pick(Nt, -1, &om, &ok, &orr);
        if (cnt <= 0) continue;
        group_pick(Nt, rnd_int(cnt), &om, &ok, &orr);
        if (!build_group(om, ok, orr)) continue;
        alloc_work();
        init_S();
        long long c = eval_cost();
        long long bc = run_sa(c, ITERS);
        if (bc == 0 && 2 * N > best_n) emit_best();
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
# Python baselines (unchanged from the parent): PG(2,q) and W(q).
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
# Driver: baselines in Python, then the C Haar-group search.
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

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    remaining = 0.85 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 2.0 and d >= 2 and D >= 2:
        max_n = moore // 2  # a Haar graph on 2N vertices needs 2N <= Moore bound
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n, max_n],
                            timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
