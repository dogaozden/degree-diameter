"""Tabu search over bi-Cayley graphs (Haar-type lifts) for bipartite graphs with max degree d
and diameter D.

Construction: take a group G = Z_M x|_R Z_K2 of order N (element a*K2+b, (a,b)(c,e) = (a+R^b c, b+e)).
Vertices A_g and B_h (g, h in G). Each A_g is joined to B_{g s} for s in S, a set of d distinct
group elements. Left multiplication is an automorphism that preserves both sides, so the diameter
is at most D iff every vertex is within distance D of A_e and of B_e. Each evaluation is therefore
two BFS runs.

Search: tabu search on S. A move replaces one element of S by a new group element. The cost is
the number of vertices beyond distance D from A_e plus from B_e. Tabu tenure forbids re-adding a
recently removed element. Restarts are random after a long stall. The order N is raised each time
a zero-cost configuration is found.

Python: the K_{d,d} fallback, projective-plane and Araujo-Pardo-Lopez constructions for D = 3,
and the W(q) generalized quadrangle for D >= 4. The C result is accepted only if lib.is_valid
confirms it.
"""
import itertools
import time

import lib

C_SOURCE = r"""
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define CAND 48
#define TENURE 7
#define STALL 3000
#define SLICE 4.0
#define MAXDEG 64

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;
static int DEG, DIAM;

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
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

/* ---------------------------------------------------------------- group state */

static int N, M, K2, R;
static int *Rpow, *inv_el, *S, *inS, *tabu_until, *stamp, *fr, *nx;
static int cur_stamp;

static inline int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
    return ra * K2 + (b + e) % K2;
}

static void setup_group(int n, int m, int k2, int r) {
    N = n; M = m; K2 = k2; R = r;
    Rpow = malloc(sizeof(int) * (size_t)K2);
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
    inv_el = malloc(sizeof(int) * (size_t)N);
    for (int x = 0; x < N; x++) {
        inv_el[x] = 0;
        for (int y = 0; y < N; y++)
            if (gmul(x, y) == 0) { inv_el[x] = y; break; }
    }
    S = malloc(sizeof(int) * (size_t)DEG);
    inS = calloc((size_t)N, sizeof(int));
    tabu_until = calloc((size_t)N, sizeof(int));
    stamp = calloc((size_t)2 * N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)2 * N);
    nx = malloc(sizeof(int) * (size_t)2 * N);
    cur_stamp = 0;
}

static void free_group(void) {
    free(Rpow); free(inv_el); free(S); free(inS); free(tabu_until);
    free(stamp); free(fr); free(nx);
    Rpow = inv_el = S = NULL;
    inS = tabu_until = stamp = fr = nx = NULL;
}

/* Number of vertices within DIAM of src (vertices 0..N-1 are A, N..2N-1 are B). */
static int bfs_count(int src) {
    int *f = fr, *h = nx;
    if (++cur_stamp >= 2000000000) {
        memset(stamp, 0, sizeof(int) * (size_t)2 * N);
        cur_stamp = 1;
    }
    int fsz = 1, cnt = 1;
    f[0] = src;
    stamp[src] = cur_stamp;
    for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
        int nsz = 0;
        for (int q = 0; q < fsz; q++) {
            int v = f[q];
            if (v < N) {
                for (int i = 0; i < DEG; i++) {
                    int w = N + gmul(v, S[i]);
                    if (stamp[w] != cur_stamp) { stamp[w] = cur_stamp; h[nsz++] = w; }
                }
            } else {
                int hh = v - N;
                for (int i = 0; i < DEG; i++) {
                    int w = gmul(hh, inv_el[S[i]]);
                    if (stamp[w] != cur_stamp) { stamp[w] = cur_stamp; h[nsz++] = w; }
                }
            }
        }
        cnt += nsz;
        int *t = f; f = h; h = t;
        fsz = nsz;
    }
    return cnt;
}

/* Unreached vertices from A_e plus from B_e; zero iff the graph has diameter <= DIAM. */
static long cost_of(void) {
    int c1 = bfs_count(0);
    int c2 = bfs_count(N);
    return (long)(2 * N - c1) + (long)(2 * N - c2);
}

static void random_S(void) {
    for (int g = 0; g < N; g++) inS[g] = 0;
    for (int i = 0; i < DEG; i++) {
        int g;
        do { g = rnd_int(N); } while (inS[g]);
        S[i] = g;
        inS[g] = 1;
    }
}

static int tabu_run(double until) {
    random_S();
    memset(tabu_until, 0, sizeof(int) * (size_t)N);
    long cur = cost_of();
    long bestc = cur;
    int stall = 0;
    for (int it = 1;; it++) {
        if (cur == 0) return 1;
        if (elapsed() > until) return 0;
        long bc = -1;
        int bi = -1, bg = -1;
        for (int c = 0; c < CAND; c++) {
            int i = rnd_int(DEG), g = rnd_int(N);
            if (inS[g]) continue;
            int old = S[i];
            S[i] = g;
            long v = cost_of();
            S[i] = old;
            if (tabu_until[g] > it && v >= bestc) continue;
            if (bi < 0 || v < bc || (v == bc && rnd_int(2))) {
                bc = v; bi = i; bg = g;
            }
        }
        if (bi < 0) continue;
        int removed = S[bi];
        tabu_until[removed] = it + TENURE;
        inS[removed] = 0;
        S[bi] = bg;
        inS[bg] = 1;
        cur = bc;
        if (cur < bestc) { bestc = cur; stall = 0; }
        else stall++;
        if (stall > STALL) {
            random_S();
            cur = cost_of();
            bestc = cur;
            stall = 0;
            memset(tabu_until, 0, sizeof(int) * (size_t)N);
        }
    }
}

/* ---------------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed time_limit n0\n");
        return 2;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int n0 = atoi(argv[5]);
    if (DEG < 1 || DEG > MAXDEG || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int target = n0 < DEG ? DEG : n0;
    int bestN = 0, bm = 0;
    int *bu = NULL, *bv = NULL;

    while (elapsed() < DEADLINE - 0.1) {
        int Nt = target + rnd_int(6);
        if (Nt < DEG) Nt = DEG;

        int divs[256], nd = 0;
        for (int k = 1; k <= Nt && nd < 256; k++)
            if (Nt % k == 0) divs[nd++] = k;
        int k2 = divs[rnd_int(nd)];
        int m = Nt / k2;

        int rr = 1;
        if (k2 > 1 && m > 1) {
            for (int tr = 0; tr < 200; tr++) {
                int cand = 1 + rnd_int(m - 1);
                if (gcd_i(cand, m) == 1 && powmod_i(cand, k2, m) == 1 % m) {
                    rr = cand;
                    break;
                }
            }
        }

        setup_group(Nt, m, k2, rr);
        double until = elapsed() + SLICE;
        if (until > DEADLINE) until = DEADLINE;
        int ok = tabu_run(until);
        if (ok) {
            free(bu); free(bv);
            bm = Nt * DEG;
            bu = malloc(sizeof(int) * (size_t)bm);
            bv = malloc(sizeof(int) * (size_t)bm);
            int e = 0;
            for (int g = 0; g < Nt; g++)
                for (int i = 0; i < DEG; i++) {
                    bu[e] = g;
                    bv[e] = Nt + gmul(g, S[i]);
                    e++;
                }
            bestN = Nt;
            target = Nt + 1;
        }
        free_group();
    }

    if (bestN > 0) {
        printf("%d %d\n", 2 * bestN, bm);
        for (int e = 0; e < bm; e++) printf("%d %d\n", bu[e], bv[e]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: known constructions and fallbacks.
# ----------------------------------------------------------------------------

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
    """W(q) for the largest prime power q <= min(d - 1, 9)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _known_start(d, D):
    """Best construction Python builds directly for D = 3, or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    known = _known_start(d, D)
    if known is not None and known[0] > best[0] and lib.is_valid(known[0], known[1], d, D):
        best = known

    # D >= 4: generalized quadrangle baseline (cheap, guarded by time).
    if D >= 4 and time.monotonic() - t0 < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None and gq[0] > best[0] and lib.is_valid(gq[0], gq[1], d, D):
            best = gq

    if best[0] >= lib.moore_bound(d, D):
        return best

    remaining = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if remaining >= 3.0 and D >= 2:
        n0 = best[0] // 2 + 1
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", n0],
                            timeout=remaining + 10.0)
            n, e = lib.parse_graph_text(out)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass   # keep the valid fallback

    return best
