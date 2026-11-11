"""Metacyclic Haar lifts for the bipartite degree-diameter problem.

Idea: the parent searches only the affine family F_q x| C_c (q prime power). This
version searches the wider metacyclic family Z_m x| Z_k, where element (a, b) is
coded a*k + b and (a, b)(c, e) = (a + r^b c, b + e) mod (m, k). Here r^k = 1 mod m
and gcd(r, m) = 1. The case r = 1 gives the abelian group Z_m x Z_k, so cyclic
groups are included too. The affine groups F_p x| C_c with p prime are the special
case m = p, k = c, and are still in the candidate list. Every (m, k) with m*k in
[lo, hi] gets an abelian candidate and one random nontrivial r when one exists.

The C engine sorts all candidates by order and binary-searches for the largest
feasible order. Each probe is a simulated-annealing search over a d-element
connection set S. The Haar graph on G has L_g ~ R_{g s}. Left translations act
transitively on each side, so diameter <= D reduces to two BFS runs, from L_e and
R_e. Each probe gets an equal share of the remaining time over the probes still
needed. Phase 2 then tries the next orders above the best.

Python keeps the projective-plane, Araujo-Lopez, W(q) and K_{d,d} baselines. Every
returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Metacyclic Haar lift search.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4800
#define MAXD 32
#define MAXCAND 90000

typedef struct { int m, k, r, N, tie; } Cand;

static int d, D;
static double t_end;
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
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

/* ------------------------------------------------------------ metacyclic group
 * G = Z_GM x| Z_GK, element (a, b) coded a*GK + b, product
 * (a, b)(c, e) = (a + r^b c, b + e), with r^GK = 1 mod GM. */

static int GM, GK, GN;
static int pw[MAXN];   /* pw[b] = r^b mod GM */

static void setup_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GN = m * k;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x - a * GK;
    int c = y / GK, e = y - c * GK;
    int na = (int)(((long)a + (long)pw[b] * c) % GM);
    int nb = b + e;
    if (nb >= GK) nb -= GK;
    return na * GK + nb;
}

/* Inverse of (a, b) is (-r^(-b) a, -b). */
static int ginv(int x) {
    int a = x / GK, b = x - a * GK;
    int nb = (GK - b) % GK;
    int t = (int)((long)pw[nb] * a % GM);
    int na = (GM - t) % GM;
    return na * GK + nb;
}

/* ------------------------------------------------------------ Haar graph state
 * Vertices: L_g = g (0..N-1), R_h = N + h. L_g ~ R_{g s}, so R_h ~ L_{h s^-1}. */

static int S[MAXD], Sinv[MAXD], bestS[MAXD];
static int fwd[MAXD][MAXN], bwd[MAXD][MAXN];
static int vis[2 * MAXN], que[2 * MAXN];
static int stamp_ = 0;

static void set_s(int i, int x) {
    S[i] = x;
    Sinv[i] = ginv(x);
    for (int g = 0; g < GN; g++) {
        fwd[i][g] = gmul(g, x);
        bwd[i][g] = gmul(g, Sinv[i]);
    }
}

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int N = GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int u = N + fwd[i][v];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int h = v - N;
                for (int i = 0; i < d; i++) {
                    int u = bwd[i][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left translations are transitive on each side, so BFS from L_e and R_e suffices. */
static long cover_cost(void) {
    int V = 2 * GN;
    return (long)(V - bfs_count(0)) + (long)(V - bfs_count(GN));
}

static int in_S(int x, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == x) return 1;
    return 0;
}

/* Simulated annealing over the d-element set S in the current group.
 * Returns 1 when cost 0 is reached (diameter <= D), 0 on timeout. */
static int search_group(double until) {
    int N = GN;
    const int iters = 6000;
    while (now() < until) {
        for (int i = 0; i < d; i++) {
            int x;
            do { x = rndint(N); } while (in_S(x, i));
            set_s(i, x);
        }
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(d);
            int x;
            do { x = rndint(N); } while (in_S(x, d));
            int old = S[i];
            set_s(i, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_s(i, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void print_result(void) {
    int N = GN;
    printf("%d %d\n", 2 * N, N * d);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + fwd[i][g]);
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    if (x->N != y->N) return x->N < y->N ? -1 : 1;
    if (x->tie != y->tie) return x->tie < y->tie ? -1 : 1;
    return 0;
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (hi > MAXN) hi = MAXN;
    if (lo < 2 * d) lo = 2 * d;
    if (lo > hi) { printf("0 0\n"); return 0; }

    /* Candidate groups: every (m, k) with lo <= m*k <= hi, with the abelian
     * case r = 1 and one random nontrivial r satisfying r^k = 1 mod m. */
    Cand *cand = (Cand *)malloc(sizeof(Cand) * MAXCAND);
    if (!cand) { printf("0 0\n"); return 0; }
    int nc = 0;
    for (int m = 1; m <= hi && nc < MAXCAND - 2; m++) {
        int kmin = (lo + m - 1) / m;
        if (kmin < 1) kmin = 1;
        for (int k = kmin; (long)m * k <= hi && nc < MAXCAND - 2; k++) {
            int N = m * k;
            cand[nc].m = m;
            cand[nc].k = k;
            cand[nc].r = 1;
            cand[nc].N = N;
            cand[nc].tie = rndint(1 << 30);
            nc++;
            if (m >= 3) {
                int start = rndint(m - 2);
                for (int t = 0; t < m - 2; t++) {
                    int r = 2 + (start + t) % (m - 2);
                    if (gcdl(r, m) != 1) continue;
                    if (powmod(r, k, m) == 1 % m) {
                        cand[nc].m = m;
                        cand[nc].k = k;
                        cand[nc].r = r;
                        cand[nc].N = N;
                        cand[nc].tie = rndint(1 << 30);
                        nc++;
                        break;
                    }
                }
            }
        }
    }
    if (nc == 0) { printf("0 0\n"); return 0; }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    Cand bestC;
    int bestN = 0;
    memset(&bestC, 0, sizeof(bestC));

    /* Phase 1: binary search over the sorted candidates. The remaining time is
     * split evenly over the probes still needed. */
    int a = 0, b = nc - 1;
    while (a <= b && now() < t_end) {
        int mid = (a + b) / 2;
        int span = b - a + 1;
        int probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = t_end - now();
        double slice = rem / (probes + 1);
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_group(cand[mid].m, cand[mid].k, cand[mid].r);
        if (search_group(now() + slice)) {
            if (cand[mid].N > bestN) {
                bestN = cand[mid].N;
                bestC = cand[mid];
                memcpy(bestS, S, sizeof(int) * (size_t)d);
            }
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }

    /* Phase 2: spend leftover time on the next candidates above the best. */
    int fails = 0;
    int idx = 0;
    if (bestN > 0) {
        while (idx < nc && cand[idx].N <= bestN) idx++;
    }
    while (idx < nc && now() < t_end && fails < 4) {
        if (cand[idx].N <= bestN) { idx++; continue; }
        double rem = t_end - now();
        double slice = rem * 0.5;
        if (slice > rem) slice = rem;
        setup_group(cand[idx].m, cand[idx].k, cand[idx].r);
        if (search_group(now() + slice)) {
            bestN = cand[idx].N;
            bestC = cand[idx];
            memcpy(bestS, S, sizeof(int) * (size_t)d);
            fails = 0;
        } else {
            fails++;
        }
        idx++;
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(bestC.m, bestC.k, bestC.r);
    for (int i = 0; i < d; i++) set_s(i, bestS[i]);
    print_result();
    return 0;
}
'''


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
    """W(q) for the largest prime power q with q + 1 <= d (kept small for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2 and is the safe fallback.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
        # Exact Moore graph: nothing can beat it.
        if D == 3 and lib.is_prime_power(d - 1) and best[0] > 2 * d:
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    # Metacyclic Haar graphs. A graph on 2N vertices needs N <= moore_bound / 2.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] // 2 + 1, mb // 8)
        hi = mb // 2
        if budget > 2.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
