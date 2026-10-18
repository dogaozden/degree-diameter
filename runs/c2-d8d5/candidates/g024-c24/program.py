"""Bi-Cayley symmetric search: a C engine anneals voltage lifts over semidirect groups Z_m x| Z_k.

Because left multiplication by the group is an automorphism of each lift, a graph is
diameter-D iff every block representative reaches all vertices within D steps. Each
cost evaluation therefore needs only 2K BFS runs, not N. Exact constructions are
kept as the fallback, so every case returns a valid graph.
"""
import itertools
import random
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
# C engine: symmetric bi-Cayley lift annealing.
# Vertices: A_{i,x} = i*G + x (i < K), B_{j,x} = (K+j)*G + x.
# Layer l (for each of d layers): A_{i,x} ~ B_{P[l][i], x*S[l][i]}, with P[l] a permutation.
# The group is Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b+e).
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 16
#define MAXK 4
#define MAXG 4096
#define ITERS 15000

typedef struct {
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
    int IS[MAXD][MAXK];
} State;

static int d, D, K, G, GM, GK, GR;
static int rp[MAXG];
static int Q[MAXD][MAXK];
static State st;
static double t_end;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

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

static void set_group(int m, int k, int r) {
    GM = m; GK = k; GR = r;
    rp[0] = 1 % GM;
    for (int b = 1; b < GK; b++) rp[b] = (int)((long)rp[b - 1] * GR % GM);
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    return (int)(((long)a + (long)rp[b] * c) % GM) * GK + (b + e) % GK;
}

static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    long na = (GM - ((long)rp[nb] * a) % GM) % GM;
    return (int)na * GK + nb;
}

/* Group chosen uniformly among all semidirect Z_m x| Z_k with m*k = Gt. */
static int sample_group(int Gt) {
    int cnt = 0, bm = 1, bk = Gt, br = 0;
    for (int m = 1; m <= Gt; m++) {
        if (Gt % m) continue;
        int k = Gt / m;
        if (m == 1) {
            cnt++;
            if (rndint(cnt) == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint(cnt) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (!cnt) return 0;
    set_group(bm, bk, br);
    return 1;
}

static void refresh(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            st.IS[l][i] = ginv(st.S[l][i]);
            Q[l][st.P[l][i]] = i;
        }
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) st.P[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = st.P[l][i]; st.P[l][i] = st.P[l][j]; st.P[l][j] = t;
        }
        for (int i = 0; i < K; i++) st.S[l][i] = rndint(G);
    }
    refresh();
}

static inline int nbr(int v, int l) {
    int b = v / G, x = v % G;
    if (b < K) {
        int j = st.P[l][b];
        return (K + j) * G + gmul(x, st.S[l][b]);
    }
    int i = Q[l][b - K];
    return i * G + gmul(x, st.IS[l][i]);
}

static int stamp = 0;
static int vis[MAXN];
static int qu[MAXN];

/* Vertices not within distance D of src. */
static long bfs_unre(int src) {
    int N = 2 * K * G;
    if (++stamp == 0x7fffffff) {
        memset(vis, 0, sizeof vis);
        stamp = 1;
    }
    int head = 0, tail = 0;
    qu[tail++] = src;
    vis[src] = stamp;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            int v = qu[head++];
            for (int l = 0; l < d; l++) {
                int u = nbr(v, l);
                if (vis[u] != stamp) { vis[u] = stamp; qu[tail++] = u; }
            }
        }
    }
    return N - tail;
}

/* Duplicate edges: two layers with the same target block and the same voltage at block i. */
static long dups(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int a = 0; a < d; a++)
            for (int b = a + 1; b < d; b++)
                if (st.P[a][i] == st.P[b][i] && st.S[a][i] == st.S[b][i]) c++;
    return c;
}

/* Block representatives suffice: left multiplication is an automorphism. */
static long total_cost(void) {
    long c = 0;
    for (int b = 0; b < 2 * K; b++) c += bfs_unre(b * G);
    return c + 20L * dups();
}

static long anneal(long iters) {
    long cost = total_cost();
    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 31) == 0 && now() > t_end) return -1;
        State old = st;
        double T = 3.0 * (1.0 - (double)t / (double)iters) + 0.05;
        if (K >= 2 && rnd01() < 0.4) {
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K);
            if (i1 == i2) continue;
            int tmp = st.P[l][i1]; st.P[l][i1] = st.P[l][i2]; st.P[l][i2] = tmp;
        } else {
            int l = rndint(d), i = rndint(K);
            st.S[l][i] = rndint(G);
        }
        refresh();
        long nc = total_cost();
        if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
            cost = nc;
        } else {
            st = old;
            refresh();
        }
    }
    return cost;
}

static int best_n = 0;
static int bestK, bestG, bestGM, bestGK, bestGR;
static State bestst;

static void save_best(void) {
    best_n = 2 * K * G;
    bestK = K; bestG = G;
    bestGM = GM; bestGK = GK; bestGR = GR;
    bestst = st;
}

static void print_best(void) {
    if (best_n == 0) { printf("0 0\n"); return; }
    K = bestK; G = bestG;
    set_group(bestGM, bestGK, bestGR);
    st = bestst;
    refresh();
    long m = (long)K * G * d;
    printf("%d %ld\n", 2 * K * G, m);
    for (int v = 0; v < K * G; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nbr(v, l));
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    long moore = moore_bound();
    long cap = moore < MAXN ? moore : MAXN;
    int fails = 0;
    while (now() < t_end) {
        int k = 1 + rndint(MAXK);
        long need = best_n / (2 * k) + 1;
        if (2L * k * need > cap) {
            if (++fails > 500) break;
            continue;
        }
        long Gt = need + rndint(2);
        if (2L * k * Gt > cap) Gt = need;
        if (!sample_group((int)Gt)) continue;
        K = k;
        G = (int)Gt;
        random_state();
        long c = anneal(ITERS);
        if (c < 0) break;
        if (c == 0) save_best();
    }
    print_best();
    return 0;
}
'''


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
        """Return the new graph if it is a larger valid graph, else None."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return best
        return None

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

    # Symmetric bi-Cayley annealing in C.
    if D >= 2 and d >= 3:
        budget = end - time.monotonic() - 1.0
        if budget > 2.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                 stdin_graph=None, timeout=budget + 8)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
