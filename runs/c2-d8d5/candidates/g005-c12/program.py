"""Bipartite bi-Cayley search: voltage lifts over semidirect products Z_m x| Z_k2, with
base sizes k = 1..4 per side. A C annealer tests each lift by BFS from the 2k block
representatives only, since left translation is an automorphism. It searches for a lift
of order 2kG beating the best so far, and the result is validated in Python before return."""
import itertools
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley lift search.
 * Usage: prog d D seed time_limit   (stdin ignored)
 * Graph: sides A_i (i < P) and B_j, blocks of size G over group Z_m x|_r Z_k2.
 * Layer l joins A_{i,g} to B_{sig[l][i], g*sv[l][i]} (sig a permutation per layer), so
 * every vertex has degree d. Simple iff no two layers share (i, sig, sv).
 * Left multiplication is an automorphism, so distances from the 2P block identities
 * determine the diameter exactly.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXK 8
#define MAXG 2100
#define MAXV 8192

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

static int gcd(int a, int b) {
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

/* ---- group Z_m x|_r Z_k2: element a*k2+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k2) ---- */
static int G, GK, GM, GR;
static int rpw[MAXG];
static int ginv[MAXG];
static int mtab[MAXG * MAXG];

static int gmul_raw(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    return (int)(((long)a + (long)rpw[b] * c) % GM) * GK + (b + e) % GK;
}

static void build_group(int m, int k2, int r) {
    GM = m; GK = k2; GR = r; G = m * k2;
    rpw[0] = 1 % m;
    for (int b = 1; b < k2; b++) rpw[b] = (int)((long)rpw[b - 1] * r % m);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++) mtab[x * G + y] = gmul_raw(x, y);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (mtab[x * G + y] == 0) { ginv[x] = y; break; }
}

static void sample_group(int Gt) {
    int divs[MAXG], nd = 0;
    for (int t = 1; t <= Gt; t++) if (Gt % t == 0) divs[nd++] = t;
    for (int at = 0; at < 60; at++) {
        int k2 = divs[rndint(nd)];
        int m = Gt / k2;
        if (m == 1) { build_group(1, k2, 0); return; }
        int r = 1 + rndint(m - 1);
        if (gcd(r, m) != 1 || powmod(r, k2, m) != 1 % m) continue;
        build_group(m, k2, r);
        return;
    }
    build_group(Gt, 1, Gt > 1 ? 1 : 0);
}

/* ---- lift state ---- */
static int P;                  /* base size per side */
static int sig[MAXD][MAXK];    /* layer l: A_i -> B_{sig[l][i]} */
static int sinv[MAXD][MAXK];   /* layer l: B_j <- A_{sinv[l][j]} */
static int sv[MAXD][MAXK];     /* voltage of A_i in layer l */

static void swap_sig(int l, int i1, int i2) {
    int t = sig[l][i1]; sig[l][i1] = sig[l][i2]; sig[l][i2] = t;
    sinv[l][sig[l][i1]] = i1;
    sinv[l][sig[l][i2]] = i2;
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < P; i++) sig[l][i] = i;
        for (int i = P - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = sig[l][i]; sig[l][i] = sig[l][j]; sig[l][j] = t;
        }
        for (int i = 0; i < P; i++) sinv[l][sig[l][i]] = i;
        for (int i = 0; i < P; i++) sv[l][i] = rndint(G);
    }
}

/* Neighbour of vertex v in layer l. A block: v < P*G. B block: v >= P*G. */
static int nb_of(int v, int l) {
    if (v < P * G) {
        int i = v / G, g = v % G;
        return (P + sig[l][i]) * G + mtab[g * G + sv[l][i]];
    } else {
        int j = v / G - P, h = v % G;
        int i = sinv[l][j];
        return i * G + mtab[h * G + ginv[sv[l][i]]];
    }
}

static int dist_[MAXV], q_[MAXV];

/* Cost = (ordered pairs of block representatives with distance > D) + N * duplicates. */
static long eval_cost(void) {
    int N = 2 * P * G;
    long bad = 0;
    for (int s = 0; s < 2 * P; s++) {
        int src = s * G;
        for (int v = 0; v < N; v++) dist_[v] = -1;
        int head = 0, tail = 0;
        dist_[src] = 0;
        q_[tail++] = src;
        while (head < tail) {
            int v = q_[head++];
            if (dist_[v] >= D) continue;
            for (int l = 0; l < d; l++) {
                int u = nb_of(v, l);
                if (dist_[u] < 0) {
                    dist_[u] = dist_[v] + 1;
                    q_[tail++] = u;
                }
            }
        }
        bad += N - tail;
    }
    long dup = 0;
    for (int l = 0; l < d; l++)
        for (int l2 = l + 1; l2 < d; l2++)
            for (int i = 0; i < P; i++)
                if (sig[l][i] == sig[l2][i] && sv[l][i] == sv[l2][i]) dup++;
    return bad + dup * (long)N;
}

static long anneal(long iters) {
    long cur = eval_cost();
    const double T0 = 3.0, T1 = 0.05;
    for (long t = 0; t < iters && cur > 0; t++) {
        if ((t & 63) == 0 && now() > t_end) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        int l = rndint(d);
        if (P >= 2 && rnd01() < 0.4) {
            int i1 = rndint(P), i2 = rndint(P);
            if (i1 == i2) continue;
            swap_sig(l, i1, i2);
            long c = eval_cost();
            if (c <= cur || rnd01() < exp((double)(cur - c) / T)) cur = c;
            else swap_sig(l, i1, i2);
        } else {
            int i = rndint(P);
            int old = sv[l][i];
            int nv = rndint(G);
            if (nv == old) continue;
            sv[l][i] = nv;
            long c = eval_cost();
            if (c <= cur || rnd01() < exp((double)(cur - c) / T)) cur = c;
            else sv[l][i] = old;
        }
    }
    return cur;
}

/* ---- best so far ---- */
static int best_n = 0, bP, bM, bK2, bR;
static int bsig[MAXD][MAXK], bsv[MAXD][MAXK];

static void save_best(int n) {
    best_n = n;
    bP = P; bM = GM; bK2 = GK; bR = GR;
    memcpy(bsig, sig, sizeof sig);
    memcpy(bsv, sv, sizeof sv);
}

static void print_best(void) {
    if (best_n == 0) {
        printf("%d %d\n", 2 * d, d * d);
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
        return;
    }
    P = bP;
    build_group(bM, bK2, bR);
    memcpy(sig, bsig, sizeof sig);
    memcpy(sv, bsv, sizeof sv);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < P; i++) sinv[l][sig[l][i]] = i;
    int NA = P * G;
    printf("%d %d\n", 2 * NA, NA * d);
    for (int v = 0; v < NA; v++)
        for (int l = 0; l < d; l++) printf("%d %d\n", v, nb_of(v, l));
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
    t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        best_n = 0;
        print_best();
        return 0;
    }

    while (now() < t_end) {
        int k = 1 + rndint(4);
        int need = best_n / (2 * k) + 1;
        int Gt = need;
        if (rndint(3) == 0) Gt += rndint(need / 10 + 2);
        if (Gt < d) Gt = d;
        if (Gt > MAXG || 2 * k * Gt > MAXV) continue;
        P = k;
        sample_group(Gt);
        random_state();
        long c = anneal(6000);
        if (c == 0) {
            int n = 2 * P * G;
            if (n > best_n) save_best(n);
        }
    }
    print_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions for calibration cases (kept from the parent).
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

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Replace the best graph if the candidate is larger and valid."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions (calibration cases return immediately).
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

    # Bi-Cayley lift search in C (no start graph needed; the C side returns its best).
    if D >= 2 and d <= 32:
        c_budget = end - time.monotonic() - 1.0
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=None, timeout=c_budget + 6.0)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
