"""Bi-Cayley annealing search: C engine searches for large bipartite graphs with k base vertices per side over groups Z_m x| Z_k2."""
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
# C engine: bi-Cayley lifts over Z_m x| Z_k2 with k base vertices per side.
# Exact diameter check via BFS from one representative per block (the group
# acts regularly on each block by left multiplication, which is an automorphism).
# Simulated annealing over voltages and layer permutations.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 2000
#define MAXK 4
#define MAXDEG 32
#define MAXV (2 * MAXK * MAXG)
#define MAXE 270000
#define MAXCAND 16384

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
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

/* ---------------- group ---------------- */
static int G_, K2, GM, GR;
static int MTbuf[MAXG * MAXG];
static int Ginv[MAXG];

static void set_group(int m, int k2, int r) {
    GM = m; K2 = k2; GR = r; G_ = m * k2;
    int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k2; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < G_; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G_; y++) {
            int c = y / k2, e = y % k2;
            MTbuf[x * G_ + y] = (int)(((a + (long)rp[b] * c) % m) * k2 + (b + e) % k2);
        }
    }
    for (int x = 0; x < G_; x++)
        for (int y = 0; y < G_; y++)
            if (MTbuf[x * G_ + y] == 0) { Ginv[x] = y; break; }
}

static int cand_m[MAXCAND], cand_k[MAXCAND], cand_r[MAXCAND];

static int enum_groups(int G) {
    int nc = 0;
    for (int m = 1; m <= G; m++) {
        if (G % m) continue;
        int k2 = G / m;
        if (m == 1) {
            if (nc < MAXCAND) { cand_m[nc] = 1; cand_k[nc] = k2; cand_r[nc] = 0; nc++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k2, m) != 1 % m) continue;
            if (nc < MAXCAND) { cand_m[nc] = m; cand_k[nc] = k2; cand_r[nc] = r; nc++; }
        }
    }
    return nc;
}

/* ---------------- bi-Cayley state ---------------- */
/* A vertex i*G+g (i<K), B vertex K*G + j*G + h.
 * Layer l: A_{i,g} ~ B_{P[l][i], g*Sh[l][i]}.  Qi[l][j] is the inverse of P[l][.]. */
static int K;
static int P[MAXDEG][MAXK];
static int Qi[MAXDEG][MAXK];
static int Sh[MAXDEG][MAXK];

static inline int nbr(int v, int l) {
    int kG = K * G_;
    if (v < kG) {
        int i = v / G_, g = v % G_;
        int j = P[l][i];
        return kG + j * G_ + MTbuf[g * G_ + Sh[l][i]];
    }
    int u = v - kG;
    int j = u / G_, h = u % G_;
    int i = Qi[l][j];
    return i * G_ + MTbuf[h * G_ + Ginv[Sh[l][i]]];
}

static int vis[MAXV];
static int vstamp = 0;
static int bq[MAXV];

/* Number of vertices NOT within distance D of src. */
static int unreached(int src) {
    int N = 2 * K * G_;
    vstamp++;
    int head = 0, tail = 0;
    bq[tail++] = src;
    vis[src] = vstamp;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int lvl_end = tail;
        while (head < lvl_end) {
            int v = bq[head++];
            for (int l = 0; l < d; l++) {
                int u = nbr(v, l);
                if (vis[u] != vstamp) {
                    vis[u] = vstamp;
                    bq[tail++] = u;
                }
            }
        }
    }
    return N - tail;
}

static int dups(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (P[l1][i] == P[l2][i] && Sh[l1][i] == Sh[l2][i]) c++;
    return c;
}

static long full_cost(void) {
    long c = 0;
    for (int a = 0; a < K; a++) {
        c += unreached(a * G_);
        c += unreached((K + a) * G_);
    }
    c += 1000L * dups();
    return c;
}

static int anneal(double until) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) P[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = P[l][i]; P[l][i] = P[l][j]; P[l][j] = t;
        }
        for (int i = 0; i < K; i++) {
            Qi[l][P[l][i]] = i;
            Sh[l][i] = rndint(G_);
        }
    }
    long cur = full_cost();
    double ts = now();
    double span = until - ts;
    if (span < 0.05) span = 0.05;
    double T = 1.5;
    long it = 0;
    while (cur > 0) {
        if ((it & 255) == 0) {
            double nw = now();
            if (nw > until) break;
            double frac = (nw - ts) / span;
            if (frac > 1.0) frac = 1.0;
            T = 1.5 * (1.0 - frac) + 0.1;
        }
        it++;
        int l = rndint(d);
        if (K > 1 && rnd01() < 0.25) {
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int j1 = P[l][i1], j2 = P[l][i2];
            P[l][i1] = j2; P[l][i2] = j1;
            Qi[l][j2] = i1; Qi[l][j1] = i2;
            long nc = full_cost();
            if (nc <= cur || rnd01() < exp((double)(cur - nc) / T)) {
                cur = nc;
            } else {
                P[l][i1] = j1; P[l][i2] = j2;
                Qi[l][j1] = i1; Qi[l][j2] = i2;
            }
        } else {
            int i = rndint(K);
            int old = Sh[l][i];
            int nw = rndint(G_);
            if (nw == old) continue;
            Sh[l][i] = nw;
            long nc = full_cost();
            if (nc <= cur || rnd01() < exp((double)(cur - nc) / T)) {
                cur = nc;
            } else {
                Sh[l][i] = old;
            }
        }
    }
    return cur == 0;
}

/* ---------------- best graph storage ---------------- */
static int eu[MAXE], ev[MAXE];
static int ne = 0, nv = 0;
static int bestN = 0;

static void store_best(void) {
    int kG = K * G_;
    int cnt = 0;
    for (int a = 0; a < kG; a++)
        for (int l = 0; l < d; l++) {
            if (cnt >= MAXE) return;
            eu[cnt] = a;
            ev[cnt] = nbr(a, l);
            cnt++;
        }
    ne = cnt;
    nv = 2 * kG;
    bestN = nv;
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
    for (int i = 0; i < 10; i++) rnd();

    /* Default answer: K_{d,d}. */
    nv = 2 * d;
    ne = 0;
    if (d >= 1 && d <= MAXDEG) {
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++) {
                eu[ne] = a;
                ev[ne] = d + b;
                ne++;
            }
    } else {
        nv = 0;
    }
    bestN = nv;

    if (d >= 2 && d <= MAXDEG && D >= 2) {
        long moore = moore_bound();
        while (now() < t_end) {
            if (bestN >= moore) break;
            double rem = t_end - now();
            int r = rndint(10);
            int k = r < 5 ? 1 : r < 8 ? 2 : r < 9 ? 3 : 4;
            int Gmin = bestN / (2 * k) + 1;
            int G = Gmin + rndint(Gmin / 30 + 2);
            if (G > MAXG || 2L * k * G > moore) continue;
            int nc = enum_groups(G);
            if (nc == 0) continue;
            int idx = rndint(nc);
            set_group(cand_m[idx], cand_k[idx], cand_r[idx]);
            K = k;
            double slice = rem / 5.0;
            if (slice < 2.0) slice = 2.0;
            if (slice > rem) slice = rem;
            if (anneal(now() + slice)) store_best();
        }
    }

    printf("%d %d\n", nv, ne);
    for (int i = 0; i < ne; i++) printf("%d %d\n", eu[i], ev[i]);
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
        """Replace the current best if (n, e) is a larger valid graph."""
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

    # Generic search: bi-Cayley annealing in C.
    if D >= 2 and time.monotonic() < end - 4.0:
        budget = end - time.monotonic() - 3.0
        if budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                 stdin_graph=None, timeout=budget + 3)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
