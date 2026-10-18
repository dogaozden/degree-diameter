"""Bi-circulant lift search: K orbits of Z_m with d permutation layers, annealed in C.

Validity: every vertex lies in a Z_m orbit, and the rotation x -> x + c is an automorphism,
so the diameter is at most D iff BFS from each orbit representative reaches everything within D.
"""
import itertools
import time

import lib


C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXL 32
#define MAXK 4

static int d, D, K, M, NV;
static double t_end;
static int pi_[MAXL][MAXK], sh[MAXL][MAXK];
static int bpi[MAXL][MAXK], bsh[MAXL][MAXK];
static int bK, bM, bestn;
static int nb[MAXN][MAXL];
static int dist[MAXN], qu[MAXN];
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

static long moore(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    double s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1e9) break;
    }
    return (long)(2 * s);
}

/* Vertex A_{i,x} = i*M + x (i < K), vertex B_{j,y} = (K+j)*M + y.
 * Layer l joins A_{i,x} to B_{pi[l][i], x + sh[l][i]}; pi[l] is a permutation. */
static void rebuild(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            int j = pi_[l][i], s = sh[l][i];
            for (int x = 0; x < M; x++) {
                int a = i * M + x;
                int b = (K + j) * M + (x + s) % M;
                nb[a][l] = b;
                nb[b][l] = a;
            }
        }
}

static long evalcost(void) {
    rebuild();
    long unreached = 0;
    for (int src = 0; src < 2 * K; src++) {
        int s0 = src * M;
        for (int v = 0; v < NV; v++) dist[v] = -1;
        int head = 0, tail = 0;
        dist[s0] = 0;
        qu[tail++] = s0;
        while (head < tail) {
            int v = qu[head++];
            if (dist[v] >= D) continue;
            for (int l = 0; l < d; l++) {
                int u = nb[v][l];
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    qu[tail++] = u;
                }
            }
        }
        unreached += NV - tail;
    }
    long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (pi_[l1][i] == pi_[l2][i] && sh[l1][i] == sh[l2][i]) dup++;
    return unreached + (long)NV * dup;
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) pi_[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = pi_[l][i];
            pi_[l][i] = pi_[l][j];
            pi_[l][j] = t;
        }
        for (int i = 0; i < K; i++) sh[l][i] = rndint(M);
    }
}

static long anneal(long iters) {
    random_state();
    long cur = evalcost();
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 255) == 0 && now() > t_end) break;
        double T = 0.2 + 3.0 * (1.0 - (double)it / (double)iters);
        int l = rndint(d);
        if (K >= 2 && rnd01() < 0.3) {
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int t = pi_[l][i1];
            pi_[l][i1] = pi_[l][i2];
            pi_[l][i2] = t;
            long c = evalcost();
            if (c <= cur || rnd01() < exp((double)(cur - c) / T)) {
                cur = c;
            } else {
                t = pi_[l][i1];
                pi_[l][i1] = pi_[l][i2];
                pi_[l][i2] = t;
            }
        } else {
            int i = rndint(K);
            int old = sh[l][i];
            sh[l][i] = rndint(M);
            long c = evalcost();
            if (c <= cur || rnd01() < exp((double)(cur - c) / T)) {
                cur = c;
            } else {
                sh[l][i] = old;
            }
        }
    }
    return cur;
}

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static void print_best(void) {
    if (bestn == 0) {
        print_complete();
        return;
    }
    K = bK;
    M = bM;
    NV = 2 * K * M;
    memcpy(pi_, bpi, sizeof(pi_));
    memcpy(sh, bsh, sizeof(sh));
    rebuild();
    printf("%d %d\n", NV, K * M * d);
    for (int a = 0; a < K * M; a++)
        for (int l = 0; l < d; l++) printf("%d %d\n", a, nb[a][l]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.2;

    if (d < 1 || d > MAXL || D < 2) {
        print_complete();
        return 0;
    }
    long cap = moore();
    if (cap > MAXN) cap = MAXN;
    bestn = 0;
    double step = 4.0;

    while (now() < t_end) {
        if (bestn + 2 > cap) break;
        int Kc = 1 + rndint(3);
        long Mt = bestn / (2L * Kc) + 1 + (long)step + rndint(2);
        if (2L * Kc * Mt > cap) {
            Kc = 1;
            Mt = cap / 2;
            if (2 * Mt <= bestn) break;
        }
        K = Kc;
        M = (int)Mt;
        NV = 2 * K * M;
        long c = anneal(12000);
        if (c == 0) {
            if (NV > bestn) {
                bestn = NV;
                bK = K;
                bM = M;
                memcpy(bpi, pi_, sizeof(pi_));
                memcpy(bsh, sh, sizeof(sh));
            }
            if (step < 256) step *= 2;
        } else {
            step /= 2;
            if (step < 1) step = 1;
        }
    }
    print_best();
    return 0;
}
'''


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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Store (n, e) if it is a larger valid graph."""
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

    # Bold new family: bi-circulant lifts with K orbits of Z_m and d permutation layers,
    # annealed in C against BFS from orbit representatives.
    if D >= 2 and 2 <= d <= 30:
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=None, timeout=c_budget + 8)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
