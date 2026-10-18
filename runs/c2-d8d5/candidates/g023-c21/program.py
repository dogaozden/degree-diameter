"""Bold variant: orbit-level annealing over bi-Cayley lifts on semidirect products Z_M x| Z_K.

The left action of the group is a graph automorphism, so validity only needs
the balls of the 2P block representatives. The C engine anneals voltages and
base permutations at that orbit level, then emits the largest lift it finds.
Exact constructions and a K_{d,d} fallback keep every case valid.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Orbit-level annealing for bipartite lifts over Z_M x|_R Z_K.
 * Usage: prog d D seed time_limit base_n
 * Outputs a valid graph with more than base_n vertices, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 16
#define MAXP 8
#define MAXNV 40000
#define MAXG 4000

static int d, D;
static double t_end;
static long base_n;

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

static long gcdl(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

/* ---- group Z_GM x|_GR Z_GK, order N = GM*GK; element (a,b) = a*GK+b ---- */
static int GM, GK, GR, N;
static long rp[MAXG];

static void set_rp(void) {
    rp[0] = 1 % GM;
    for (int b = 1; b < GK; b++) rp[b] = rp[b - 1] * GR % GM;
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    long am = (a + rp[b] * c) % GM;
    return (int)(am * GK + (b + e) % GK);
}

static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    long na = (GM - rp[nb] * a % GM) % GM;
    return (int)(na * GK + nb);
}

static void set_group(int order) {
    int divs[64], nd = 0;
    for (int k = 1; k <= order && nd < 64; k++)
        if (order % k == 0) divs[nd++] = k;
    int k = divs[rndint(nd)];
    int m = order / k;
    int r = 1 % m;
    if (m > 2 && k > 1) {
        for (int t = 0; t < 300; t++) {
            long c = 1 + rndint(m - 1);
            if (gcdl(c, m) == 1 && powmod(c, k, m) == 1 % m) { r = (int)c; break; }
        }
    }
    GM = m; GK = k; GR = r;
    set_rp();
}

/* ---- lift state: P base vertices per side, d layers of permutations + voltages ---- */
static int P;
static int perm[MAXD][MAXP];
static int sv[MAXD][MAXP];
static int sinv[MAXD][MAXP];
static int nbr[MAXNV][MAXD];
static int NV;
static int vis[MAXNV];
static int vstamp = 0;
static int queue_[MAXNV];

static void build_nbr(void) {
    NV = 2 * P * N;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < P; i++) sinv[l][i] = ginv(sv[l][i]);
    for (int i = 0; i < P; i++)
        for (int g = 0; g < N; g++)
            for (int l = 0; l < d; l++)
                nbr[i * N + g][l] = (P + perm[l][i]) * N + gmul(g, sv[l][i]);
    for (int l = 0; l < d; l++) {
        int pinv[MAXP];
        for (int i = 0; i < P; i++) pinv[perm[l][i]] = i;
        for (int j = 0; j < P; j++) {
            int i = pinv[j];
            for (int h = 0; h < N; h++)
                nbr[(P + j) * N + h][l] = i * N + gmul(h, sinv[l][i]);
        }
    }
}

/* Size of the ball of radius D around src. */
static int ball_size(int src) {
    vstamp++;
    int head = 0, tail = 1;
    queue_[0] = src;
    vis[src] = vstamp;
    for (int depth = 0; depth < D; depth++) {
        int end = tail;
        if (head == end) break;
        while (head < end) {
            int v = queue_[head++];
            for (int l = 0; l < d; l++) {
                int u = nbr[v][l];
                if (vis[u] != vstamp) { vis[u] = vstamp; queue_[tail++] = u; }
            }
        }
    }
    return tail;
}

/* Cost 0 iff the lift is simple and has diameter <= D.
 * The left group action is an automorphism with 2P orbits, so block
 * representatives suffice. */
static long eval_cost(void) {
    build_nbr();
    long bad = 0;
    for (int b = 0; b < 2 * P; b++) bad += NV - ball_size(b * N);
    long dup = 0;
    for (int i = 0; i < P; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1][i] == perm[l2][i] && sv[l1][i] == sv[l2][i]) dup++;
    return bad + dup * 2L * NV;
}

static int anneal(long iters) {
    long cur = eval_cost();
    if (cur == 0) return 1;
    double T0 = 1.0 + 0.05 * (double)cur, Tend = 0.2;
    for (long t = 0; t < iters; t++) {
        if ((t & 31) == 0 && now() > t_end) break;
        double T = T0 * pow(Tend / T0, (double)t / (double)iters);
        int l = rndint(d), i = rndint(P);
        if (rndint(2) == 0) {
            int old = sv[l][i];
            int ns = rndint(N);
            if (ns == old) continue;
            sv[l][i] = ns;
            long c2 = eval_cost();
            if (c2 <= cur || rnd01() < exp((double)(cur - c2) / T)) cur = c2;
            else sv[l][i] = old;
        } else {
            int i2 = rndint(P);
            if (i2 == i) continue;
            int tmp = perm[l][i];
            perm[l][i] = perm[l][i2];
            perm[l][i2] = tmp;
            long c2 = eval_cost();
            if (c2 <= cur || rnd01() < exp((double)(cur - c2) / T)) cur = c2;
            else {
                tmp = perm[l][i];
                perm[l][i] = perm[l][i2];
                perm[l][i2] = tmp;
            }
        }
        if (cur == 0) return 1;
    }
    return cur == 0;
}

static int bP, bN, bM, bK, bR;
static int bperm[MAXD][MAXP], bsv[MAXD][MAXP];
static long best_n;

static void save_best(void) {
    bP = P; bN = N; bM = GM; bK = GK; bR = GR;
    memcpy(bperm, perm, sizeof perm);
    memcpy(bsv, sv, sizeof sv);
}

static void emit(void) {
    P = bP; N = bN; GM = bM; GK = bK; GR = bR;
    set_rp();
    memcpy(perm, bperm, sizeof perm);
    memcpy(sv, bsv, sizeof sv);
    build_nbr();
    printf("%d %ld\n", NV, (long)P * N * d);
    for (int v = 0; v < P * N; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nbr[v][l]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit base_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    base_n = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    if (d < 2 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }

    long moore = 0, pw = 1;
    for (int i = 0; i < D; i++) { moore += pw; pw *= (d - 1); }
    moore *= 2;

    best_n = base_n;
    int fails = 0;
    while (now() < t_end && fails < 200000) {
        int p = 2 + rndint(5);  /* P in 2..6 */
        long Nl = best_n / (2L * p) + 1 + rndint(3);
        if (Nl < 2 || Nl > MAXG || 2L * p * Nl > MAXNV || 2L * p * Nl > moore) {
            fails++;
            continue;
        }
        P = p;
        N = (int)Nl;
        set_group(N);
        for (int l = 0; l < d; l++) {
            for (int i = 0; i < P; i++) perm[l][i] = i;
            for (int i = P - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = perm[l][i];
                perm[l][i] = perm[l][j];
                perm[l][j] = t;
            }
            for (int i = 0; i < P; i++) sv[l][i] = rndint(N);
        }
        if (anneal(20000)) {
            best_n = 2L * P * N;
            save_best();
        }
    }
    if (best_n > base_n) emit();
    else printf("0 0\n");
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.9 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Replace the best graph if (n, e) is a larger valid graph."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    try:
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
    except Exception:
        pass

    if D >= 2 and d >= 2:
        c_budget = end - time.monotonic() - 1.0
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2), best[0]],
                                 timeout=c_budget + 8)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
