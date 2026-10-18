"""Bi-Cayley voltage-lift annealing with a cheap representative-BFS cost.

Exact constructions handle D=3 and D=4 where they exist. The C engine searches lifts
over semidirect products Z_m x| Z_k with p base vertices per side. Each base vertex has
d darts, one per layer of a perfect matching, with a group voltage on each dart. The
group acts regularly on each side, so the diameter test needs only 2p BFS runs from
block representatives. Moves change voltages and swap matching targets. The engine
grows the order by raising the group-order target. K_{d,d} is the fallback.
"""
import itertools
import time

import lib


C_SOURCE = r'''
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 2048
#define MAXP 4
#define MAXD 16
#define MAXV (2 * MAXP * MAXG)

static int d, D, p, G;
static int gm, gk, gr;
static int rp[MAXG];
static int INV[MAXG];
static int MUL[MAXG * MAXG];
static int P[MAXD][MAXP], Pinv[MAXD][MAXP], S[MAXD][MAXP];
static int bestE[2 * MAXP * MAXG * MAXD];
static long bestEdges = 0;
static int best_n = 0;
static double t_end;
static uint64_t rs = 88172645463325252ULL;
static int stampv[MAXV];
static int curstamp = 0;
static int qbuf[MAXV];

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

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, q = 1;
    for (int i = 0; i < D; i++) {
        s += q;
        q *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* Random semidirect product Z_m x| Z_k of order G, element (a,b) = a*k+b. */
static int build_group(int order) {
    int cnt = 0, cm = 1, ck = order, cr = 0;
    G = order;
    for (int m = 1; m <= order; m++) {
        if (order % m) continue;
        int k = order / m;
        if (m == 1) {
            cnt++;
            if (rndint(cnt) == 0) { cm = 1; ck = k; cr = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            cnt++;
            if (rndint(cnt) == 0) { cm = m; ck = k; cr = r; }
        }
    }
    gm = cm; gk = ck; gr = cr;
    rp[0] = 1 % gm;
    for (int b = 1; b < gk; b++) rp[b] = (int)((long)rp[b - 1] * gr % gm);
    for (int x = 0; x < G; x++) {
        int a = x / gk, b = x % gk;
        for (int y = 0; y < G; y++) {
            int c = y / gk, e = y % gk;
            MUL[x * G + y] = (int)(((long)a + (long)rp[b] * c) % gm) * gk + (b + e) % gk;
        }
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (MUL[x * G + y] == 0) { INV[x] = y; break; }
    return 1;
}

static void refresh_inv(void) {
    for (int t = 0; t < d; t++)
        for (int i = 0; i < p; i++)
            Pinv[t][P[t][i]] = i;
}

static void random_layers(void) {
    for (int t = 0; t < d; t++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < p; i++) {
            P[t][i] = perm[i];
            S[t][i] = rndint(G);
        }
    }
    refresh_inv();
}

/* Neighbours of lift vertex v. A(i,x) = i*G + x, B(j,y) = p*G + j*G + y.
 * Layer t joins A(i,x) to B(P[t][i], x*S[t][i]). */
static int neighbors(int v, int *out) {
    int pg = p * G;
    int cnt = 0;
    if (v < pg) {
        int i = v / G, x = v % G;
        for (int t = 0; t < d; t++) {
            int j = P[t][i], s = S[t][i];
            out[cnt++] = pg + j * G + MUL[x * G + s];
        }
    } else {
        int idx = v - pg;
        int j = idx / G, y = idx % G;
        for (int t = 0; t < d; t++) {
            int i = Pinv[t][j], s = S[t][i];
            out[cnt++] = i * G + MUL[y * G + INV[s]];
        }
    }
    return cnt;
}

/* Unreached pairs summed over block representatives. Zero iff the lift has diameter <= D. */
static long total_cost(void) {
    int N = 2 * p * G;
    int pg = p * G;
    long total = 0;
    int nb[MAXD];
    for (int rep = 0; rep < 2 * p; rep++) {
        int src = rep < p ? rep * G : pg + (rep - p) * G;
        curstamp++;
        int head = 0, tail = 0;
        stampv[src] = curstamp;
        qbuf[tail++] = src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int lend = tail;
            while (head < lend) {
                int v = qbuf[head++];
                int c = neighbors(v, nb);
                for (int k = 0; k < c; k++) {
                    int u = nb[k];
                    if (stampv[u] != curstamp) {
                        stampv[u] = curstamp;
                        qbuf[tail++] = u;
                    }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static long build_edges(int *E) {
    long c = 0;
    int pg = p * G;
    for (int i = 0; i < p; i++)
        for (int x = 0; x < G; x++)
            for (int t = 0; t < d; t++) {
                int j = P[t][i], s = S[t][i];
                E[2 * c] = i * G + x;
                E[2 * c + 1] = pg + j * G + MUL[x * G + s];
                c++;
            }
    return c;
}

/* Annealing over voltages and matchings for a fixed group. Returns 1 on success. */
static int anneal(double until, long patience) {
    random_layers();
    long cur = total_cost();
    long best_c = cur, last = 0, it = 0;
    while (cur > 0) {
        it++;
        if ((it & 15) == 0 && now() > until) break;
        if (it - last > patience) break;
        double temp = 0.3 + 0.03 * (double)cur;
        int t = rndint(d);
        int sp[MAXP], ss[MAXP], spi[MAXP];
        memcpy(sp, P[t], sizeof sp);
        memcpy(ss, S[t], sizeof ss);
        memcpy(spi, Pinv[t], sizeof spi);
        if (p > 1 && rndint(4) == 0) {
            int a = rndint(p), b = rndint(p);
            if (a == b) continue;
            int tmp = P[t][a]; P[t][a] = P[t][b]; P[t][b] = tmp;
            for (int i = 0; i < p; i++) Pinv[t][P[t][i]] = i;
        } else {
            int i = rndint(p);
            int g = rndint(G);
            if (g == S[t][i]) continue;
            S[t][i] = g;
        }
        long nc = total_cost();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / temp)) {
            cur = nc;
            if (cur < best_c) { best_c = cur; last = it; }
        } else {
            memcpy(P[t], sp, sizeof sp);
            memcpy(S[t], ss, sizeof ss);
            memcpy(Pinv[t], spi, sizeof spi);
        }
    }
    return cur == 0;
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
    t_end = t0 + limit * 0.95;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    long moore = moore_bound();
    while (now() < t_end) {
        if (best_n >= moore) break;
        int pp = 1 + rndint(MAXP);
        long base = best_n / (2 * pp);
        long target;
        if (best_n == 0) {
            target = d + rndint(2 * d + 1);
        } else {
            static const double fr[3] = {0.01, 0.03, 0.08};
            double f = fr[rndint(3)];
            target = base + 1 + rndint((int)(base * f) + 2);
        }
        if (target < 1 || target > MAXG || 2L * pp * target > moore) continue;

        p = pp;
        double remaining = t_end - now();
        double slice = remaining * 0.1;
        if (slice < 1.0) slice = 1.0;
        if (slice > 8.0) slice = 8.0;
        double until = now() + slice;
        if (until > t_end) until = t_end;

        build_group((int)target);
        if (anneal(until, 3000)) {
            long n2 = 2L * p * G;
            if (n2 > best_n) {
                best_n = (int)n2;
                bestEdges = build_edges(bestE);
            }
        }
    }
    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %ld\n", best_n, bestEdges);
    for (long e = 0; e < bestEdges; e++)
        printf("%d %d\n", bestE[2 * e], bestE[2 * e + 1]);
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

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    if D <= 2:
        return best

    def consider(n, e):
        """Replace the best graph if (n, e) is larger and valid."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

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

    # Bold change: one C engine doing bi-Cayley lift annealing from scratch.
    c_budget = end - time.monotonic() - 0.5
    if c_budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                             stdin_graph=None, timeout=c_budget + 10)
            n, edges = lib.parse_graph_text(text)
            norm = sorted({(min(u, v), max(u, v)) for u, v in edges if u != v})
            consider(n, norm)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
