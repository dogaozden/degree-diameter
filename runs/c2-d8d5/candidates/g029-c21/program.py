"""Bi-Cayley lift search: a group-invariant C search over semidirect products Z_m x| Z_k.

Exact constructions (projective planes, Araujo-Lopez, generalized quadrangles) are kept for
the calibration cases. The main search is a new C engine. It picks a random group of order
about best/(2*kb), gives a base of kb vertices per side, and anneals the voltages. Left
multiplication is an automorphism, so only the 2*kb block representatives need BFS.
"""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact and small constructions (calibration cases return immediately).
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
# C engine: group-invariant (bi-Cayley) annealing over Z_m x| Z_k.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bi-Cayley lift search over semidirect products Z_m x| Z_k (group-invariant search).
 * Usage:  prog d D seed time_limit threshold
 * Vertices: A_{i,g} = i*G+g (i < KB), B_{j,h} = (KB+j)*G+h, identity g = 0.
 * Layer l joins A_i to B_{lay[l][i]} with voltage S[l][i]: A_{i,x} ~ B_{j, x*s}.
 * Left multiplication is an automorphism, so the graph has diameter <= D iff the
 * 2*KB block representatives reach every vertex within D.
 * stdout: "n m" + edges of the best valid graph with n > threshold, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 8192
#define MAXD 32
#define MAXKB 5
#define MAXG 4096

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
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

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
    long s = 0, p = 1;
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* ---------------- group Z_gm x| Z_gk, element (a,b) = a*gk+b ---------------- */
static int gm, gk, gr;
static int rp[MAXG];

static int gmul(int x, int y) {
    int a = x / gk, b = x % gk, c = y / gk, e = y % gk;
    return (int)(((long)a + (long)rp[b] * c) % gm) * gk + (b + e) % gk;
}

static int ginv(int x) {
    int a = x / gk, b = x % gk;
    int nb = (gk - b) % gk;
    long t = (long)rp[nb] * a % gm;
    int na = (int)((gm - t) % gm);
    return na * gk + nb;
}

/* Pick a uniformly random semidirect product of order N (m >= 2). */
static int random_group(int N) {
    long cnt = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 2; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (cnt == 0) return 0;
    gm = bm;
    gk = bk;
    gr = br;
    rp[0] = 1 % gm;
    for (int b = 1; b < gk; b++) rp[b] = (int)((long)rp[b - 1] * gr % gm);
    return 1;
}

/* ---------------- bi-Cayley state ---------------- */
static int KB, G, V;
static int lay[MAXD][MAXKB];
static int S[MAXD][MAXKB];
static int nbr[MAXV][MAXD];
static int stamp_of[MAXV], dist_of[MAXV], queue_of[MAXV];
static int stamp_now = 0;

static void build_nbr(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < KB; i++) {
            int j = lay[l][i], s = S[l][i], si = ginv(s);
            for (int g = 0; g < G; g++) {
                nbr[i * G + g][l] = (KB + j) * G + gmul(g, s);
                nbr[(KB + j) * G + g][l] = i * G + gmul(g, si);
            }
        }
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < KB; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (lay[l1][i] == lay[l2][i] && S[l1][i] == S[l2][i]) c++;
    return c;
}

/* Number of vertices within distance D of src. */
static int count_reached(int src) {
    int head = 0, tail = 0;
    stamp_now++;
    queue_of[tail++] = src;
    stamp_of[src] = stamp_now;
    dist_of[src] = 0;
    while (head < tail) {
        int v = queue_of[head++];
        if (dist_of[v] >= D) continue;
        for (int l = 0; l < d; l++) {
            int u = nbr[v][l];
            if (stamp_of[u] != stamp_now) {
                stamp_of[u] = stamp_now;
                dist_of[u] = dist_of[v] + 1;
                queue_of[tail++] = u;
            }
        }
    }
    return tail;
}

static long eval_cost(void) {
    long c = 0;
    for (int s = 0; s < 2 * KB; s++) c += V - count_reached(s * G);
    c += (long)dupcount() * V;
    return c;
}

static int full_check(void) {
    int A = KB * G;
    for (int v = 0; v < V; v++)
        for (int l = 0; l < d; l++) {
            int u = nbr[v][l];
            if (u < 0 || u >= V) return 0;
            if ((v < A) == (u < A)) return 0;
            for (int l2 = 0; l2 < l; l2++)
                if (nbr[v][l2] == u) return 0;
        }
    for (int v = 0; v < V; v++)
        if (count_reached(v) != V) return 0;
    return 1;
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < KB; i++) lay[l][i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        for (int i = 0; i < KB; i++) S[l][i] = rndint(G);
    }
}

/* Simulated annealing on the current group. Returns 1 when cost reaches 0. */
static int anneal(long iters) {
    random_state();
    build_nbr();
    long cost = eval_cost();
    if (cost == 0) return 1;
    double T0 = (double)cost * 0.02 + 1.0;
    const double Tend = 0.2;
    long best_cost = cost, last_imp = 0;
    for (long t = 0; t < iters; t++) {
        if ((t & 31) == 0 && now() > t_end) return 0;
        if (t - last_imp > iters / 3) break;
        double T = T0 * pow(Tend / T0, (double)t / (double)iters);
        int l = rndint(d);
        int i = rndint(KB);
        long c2;
        if (KB >= 2 && rndint(4) == 0) {
            int i2 = rndint(KB - 1);
            if (i2 >= i) i2++;
            int a = lay[l][i], b = lay[l][i2];
            lay[l][i] = b;
            lay[l][i2] = a;
            build_nbr();
            c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                lay[l][i] = a;
                lay[l][i2] = b;
                build_nbr();
                continue;
            }
        } else {
            int old = S[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            S[l][i] = nw;
            build_nbr();
            c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                S[l][i] = old;
                build_nbr();
                continue;
            }
        }
        if (cost < best_cost) { best_cost = cost; last_imp = t; }
        if (cost == 0) return 1;
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit threshold\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long threshold = atol(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.93;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    static int best_nbr[MAXV][MAXD];
    int have = 0;
    int best_n = (int)threshold;
    int best_A = 0;

    if (d >= 2 && d <= MAXD && D >= 2) {
        long moore = moore_bound();
        long cap = moore < MAXV ? moore : MAXV;
        int fails = 0;
        while (now() < t_end && best_n + 2 <= cap && fails < 100000) {
            int r = rndint(10);
            int kb = r < 1 ? 1 : r < 4 ? 2 : r < 7 ? 3 : r < 9 ? 4 : 5;
            long gmax = cap / (2L * kb);
            long gt = best_n / (2L * kb) + 1 + rndint(3);
            if (gt > gmax) gt = gmax;
            if (gt > MAXG) gt = MAXG;
            if (gt < 2 || 2L * kb * gt <= best_n) { fails++; continue; }
            if (!random_group((int)gt)) { fails++; continue; }
            KB = kb;
            G = (int)gt;
            V = 2 * KB * G;
            if (anneal(12000)) {
                if (V > best_n && full_check()) {
                    best_n = V;
                    best_A = KB * G;
                    have = 1;
                    memcpy(best_nbr, nbr, sizeof(nbr));
                }
            }
        }
    }

    if (have) {
        printf("%d %d\n", best_n, best_A * d);
        for (int u = 0; u < best_A; u++)
            for (int l = 0; l < d; l++)
                printf("%d %d\n", u, best_nbr[u][l]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.8 * time_limit - 3.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Cycle of length 2D: bipartite, degree 2, diameter D (Moore-optimal).
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2 (Moore-optimal for D = 2).
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        """Replace best with (n, e) if it is larger and valid."""
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
    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search (C): group-invariant bi-Cayley annealing. Returns only graphs larger
    # than the current best, so the Python result is never worsened.
    if D >= 3 and d <= 30:
        remaining = t0 + usable - time.monotonic() - 0.5
        if remaining > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), best[0]],
                                 stdin_graph=None, timeout=remaining + 5)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
