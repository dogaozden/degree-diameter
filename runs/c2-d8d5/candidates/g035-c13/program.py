"""Bold change: bipartite voltage lifts over cyclic and semidirect groups, searched in C.

A candidate is a lift of a K+K base multigraph (d layers, each a perfect matching
between the two base classes, K <= 4) by a group G = Z_m x| Z_k2. Left multiplication
by G is an automorphism of every lift, so each base class is vertex-transitive and
validity is decided exactly by BFS from one identity vertex per class. Simulated
annealing repairs voltages and matchings until the diameter bound holds, and each
success raises the target order. Exact constructions (projective planes, Araujo-Lopez,
generalized quadrangles) are kept as a fallback.
"""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions (calibration cases return immediately).
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
# C engine: simulated annealing over group voltage lifts.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bipartite voltage-lift search over groups Z_m x|_r Z_k2.
 * Usage:  prog d D seed time_limit   (stdin is ignored)
 * Base: K vertices per side, d layers. Layer l sends A_i to B_{sg[l][i]} with voltage vg[l][i].
 * Lift: A_{i,x} ~ B_{j, x*g}. Left multiplication is an automorphism, so BFS from the
 * identity of each of the 2K classes gives the exact diameter test.
 * stdout: "n m" then m edge lines of the best valid graph found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 2048
#define MAXK 4
#define MAXDG 16
#define MAXV (2 * MAXK * MAXG)
#define MAXE (MAXV * MAXDG / 2)

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
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

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* ---------------- group Z_m x|_r Z_k2, element a*k2+b ---------------- */
static int GM, GK, GN;
static int rp[MAXG];
static int MT[MAXG * MAXG];   /* MT[x*GN+y] = x*y */
static int IV[MAXG];         /* inverses */

static int gmul_raw(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    long t = (long)a + (long)rp[b] * c;
    return (int)(t % GM) * GK + (b + e) % GK;
}

static void build_table(void) {
    int n = GN;
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            MT[x * n + y] = gmul_raw(x, y);
    for (int x = 0; x < n; x++) IV[x] = 0;
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (MT[x * n + y] == 0) IV[x] = y;
}

/* Pick a random semidirect group of the given order (cyclic when r = 1, k2 arbitrary). */
static void choose_group(int order) {
    long cnt = 0;
    int bm = 1, bk = order, br = 0;
    for (int m = 1; m <= order; m++) {
        if (order % m) continue;
        int k2 = order / m;
        if (m == 1) {
            cnt++;
            if (rndint((int)cnt) == 0) { bm = 1; bk = k2; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k2, m) != 1) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { bm = m; bk = k2; br = r; }
        }
    }
    GM = bm;
    GK = bk;
    GN = order;
    rp[0] = 1 % GM;
    for (int b = 1; b < GK; b++) rp[b] = (int)((long)rp[b - 1] * br % GM);
    build_table();
}

/* ---------------- lift state ---------------- */
static int K;
static int sg[MAXDG][MAXK];   /* target B index of A_i in layer l */
static int vg[MAXDG][MAXK];   /* voltage of that dart */
static int isg[MAXDG][MAXK];  /* isg[l][j] = i with sg[l][i] = j */
static int bestsg[MAXDG][MAXK], bestvg[MAXDG][MAXK];

static int stampv[MAXV];
static int stampc = 0;
static int qv[MAXV];

static int EU[MAXE], EV[MAXE];

/* Neighbour of vertex v in layer l. */
static inline int nb_of(int v, int l) {
    int q = v / GN;
    if (q < K) {
        int x = v - q * GN;
        int j = sg[l][q];
        return (K + j) * GN + MT[x * GN + vg[l][q]];
    } else {
        int y = v - q * GN;
        int i = isg[l][q - K];
        return i * GN + MT[y * GN + IV[vg[l][i]]];
    }
}

/* Number of vertices at distance > D from s. */
static int bfs_unreached(int s, int nv) {
    stampc++;
    int head = 0, tail = 0, depth = 0;
    qv[tail++] = s;
    stampv[s] = stampc;
    while (head < tail && depth < D && tail < nv) {
        int end = tail;
        while (head < end) {
            int v = qv[head++];
            for (int l = 0; l < d; l++) {
                int u = nb_of(v, l);
                if (stampv[u] != stampc) {
                    stampv[u] = stampc;
                    qv[tail++] = u;
                }
            }
        }
        depth++;
    }
    return nv - tail;
}

/* Cost 0 iff the lift is simple, d-regular and has diameter <= D. */
static long evaluate(void) {
    int nv = 2 * K * GN;
    long dups = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (sg[l1][i] == sg[l2][i] && vg[l1][i] == vg[l2][i]) dups++;
    long unr = 0;
    for (int s = 0; s < 2 * K; s++) unr += bfs_unreached(s * GN, nv);
    return unr + (long)nv * dups;
}

static void random_lift(void) {
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            sg[l][i] = perm[i];
            vg[l][i] = rndint(GN);
        }
        for (int i = 0; i < K; i++) isg[l][sg[l][i]] = i;
    }
}

static void swap_targets(int l, int a, int b) {
    int t = sg[l][a];
    sg[l][a] = sg[l][b];
    sg[l][b] = t;
    isg[l][sg[l][a]] = a;
    isg[l][sg[l][b]] = b;
}

static void save_state(void) {
    memcpy(bestsg, sg, sizeof sg);
    memcpy(bestvg, vg, sizeof vg);
}

static void load_state(void) {
    memcpy(sg, bestsg, sizeof sg);
    memcpy(vg, bestvg, sizeof vg);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) isg[l][sg[l][i]] = i;
}

/* Simulated annealing on the current group and K. Leaves the best state loaded. */
static long sa_run(long max_it, long patience, double deadline) {
    long cur = evaluate();
    long best = cur;
    long last = 0;
    save_state();
    double nv = 2.0 * K * GN;
    double T0 = 1.0 + 0.002 * nv;
    for (long it = 0; it < max_it && cur > 0; it++) {
        if (it - last > patience) break;
        if ((it & 31) == 0 && now() > deadline) break;
        double T = T0 * (1.0 - (double)it / (double)max_it) + 0.2;
        int l = rndint(d);
        int i1 = rndint(K), i2 = -1, oldg = 0;
        int swapmv = (K >= 2) && (rndint(2) == 0);
        if (swapmv) {
            i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            swap_targets(l, i1, i2);
        } else {
            oldg = vg[l][i1];
            vg[l][i1] = rndint(GN);
        }
        long nc = evaluate();
        if (nc <= cur || rnd01() < exp((double)(cur - nc) / T)) {
            cur = nc;
            if (cur < best) {
                best = cur;
                last = it;
                save_state();
            }
        } else {
            if (swapmv) swap_targets(l, i1, i2);
            else vg[l][i1] = oldg;
        }
    }
    load_state();
    return best;
}

/* Write the current (valid) lift as an edge list. */
static void emit(int *bn, int *bm) {
    int m = 0;
    for (int i = 0; i < K; i++)
        for (int x = 0; x < GN; x++)
            for (int l = 0; l < d; l++) {
                EU[m] = i * GN + x;
                EV[m] = (K + sg[l][i]) * GN + MT[x * GN + vg[l][i]];
                m++;
            }
    *bn = 2 * K * GN;
    *bm = m;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXDG) {
        printf("0 0\n");
        return 0;
    }

    long moore = moore_bound();
    int best_n = 0, best_m = 0, fails = 0;

    while (now() < t_end && fails < 500) {
        K = 1 + rndint(MAXK);
        long Nhi = moore / (2L * K);
        if (Nhi > MAXG) Nhi = MAXG;
        long Nlo = best_n / (2 * K) + 1;
        long N = Nlo + rndint(3);
        if (N < d) N = d;
        if (N > Nhi || N < 1) {
            fails++;
            continue;
        }
        fails = 0;
        choose_group((int)N);
        random_lift();
        double dl = now() + 8.0;
        if (dl > t_end) dl = t_end;
        long c = sa_run(60000, 6000, dl);
        if (c == 0) emit(&best_n, &best_m);
    }

    if (best_n == 0) {
        if (D == 1) {
            best_n = 2;
            best_m = 1;
            EU[0] = 0;
            EV[0] = 1;
        } else {
            best_n = 2 * d;
            best_m = 0;
            for (int a = 0; a < d; a++)
                for (int b = 0; b < d; b++) {
                    EU[best_m] = a;
                    EV[best_m] = d + b;
                    best_m++;
                }
        }
    }
    printf("%d %d\n", best_n, best_m);
    for (int e = 0; e < best_m; e++) printf("%d %d\n", EU[e], EV[e]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is d-regular.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Replace the best graph if (n, e) is larger and valid."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: voltage lifts over groups, annealed in C.
    if D >= 2:
        budget = end - time.monotonic() - 2.0
        if budget > 2.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, int(seed), round(budget, 2)],
                                 stdin_graph=None, timeout=budget + 8)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
