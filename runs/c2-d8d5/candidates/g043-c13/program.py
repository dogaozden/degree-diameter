"""Cayley double-cover search: bipartite Haar graphs over semidirect products Z_m x| Z_k,
found by simulated annealing on the connection set in C, with vertex-transitivity reducing
the diameter check to two BFS runs."""
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
# C engine. A bipartite graph on A = {a_g}, B = {b_x}, g,x in G, with
# a_g ~ b_{g s} for s in S (|S| = d). Left multiplication is an automorphism,
# so the diameter is at most D iff BFS from a_e and from b_e reaches everything
# within D steps. Search: simulated annealing over S for each group order N,
# climbing N as long as a solution is found.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 2048
#define MAXD 16
#define MAXT 20000

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

/* Semidirect product Z_m x| Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int GM, GK, GR;
static int N;
static int rp[MAXG];
static int MUL[MAXG * MAXG];
static int INV[MAXG];

static void build_group(int m, int k, int r) {
    GM = m; GK = k; GR = r;
    N = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            MUL[x * N + y] = (int)(((long)a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MUL[x * N + y] == 0) { INV[x] = y; break; }
}

static int TM[MAXT], TK[MAXT], TR[MAXT];
static int ntr;

static void add_triple(int m, int k, int r) {
    if (ntr < MAXT) { TM[ntr] = m; TK[ntr] = k; TR[ntr] = r; ntr++; }
}

static void enumerate_groups(int ord) {
    ntr = 0;
    for (int m = 1; m <= ord; m++) {
        if (ord % m) continue;
        int k = ord / m;
        if (m == 1) { add_triple(1, k, 0); continue; }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            add_triple(m, k, r);
        }
    }
}

static int S[MAXD];
static int vis[2 * MAXG];
static int stamp = 0;
static int qu[2 * MAXG];

static int reach_count(int src) {
    int head = 0, tail = 0;
    stamp++;
    qu[tail++] = src;
    vis[src] = stamp;
    for (int lev = 0; lev < D && head < tail; lev++) {
        int end = tail;
        while (head < end) {
            int v = qu[head++];
            if (v < N) {
                const int *row = MUL + v * N;
                for (int t = 0; t < d; t++) {
                    int u = N + row[S[t]];
                    if (vis[u] != stamp) { vis[u] = stamp; qu[tail++] = u; }
                }
            } else {
                int x = v - N;
                const int *row = MUL + x * N;
                for (int t = 0; t < d; t++) {
                    int u = row[INV[S[t]]];
                    if (vis[u] != stamp) { vis[u] = stamp; qu[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

static int cost_of(void) {
    return (2 * N - reach_count(0)) + (2 * N - reach_count(N));
}

static int in_prefix(int x, int t) {
    for (int s = 0; s < t; s++) if (S[s] == x) return 1;
    return 0;
}

static void random_S(void) {
    for (int t = 0; t < d; t++) {
        int x;
        do { x = rndint(N); } while (in_prefix(x, t));
        S[t] = x;
    }
}

static int sa_attempt(void) {
    random_S();
    int cost = cost_of();
    int best = cost;
    long last = 0;
    for (long it = 0;; it++) {
        if (cost == 0) return 1;
        if ((it & 255) == 0 && now() > t_end) return 0;
        if (it - last > 6000) return 0;
        double T = 0.2 + 4.0 * exp(-0.0006 * (double)it);
        int t = rndint(d);
        int x;
        do { x = rndint(N); } while (in_prefix(x, d));
        int old = S[t];
        S[t] = x;
        int nc = cost_of();
        if (nc <= cost || rnd01() < exp((double)(cost - nc) / T)) {
            cost = nc;
            if (cost < best) { best = cost; last = it; }
        } else {
            S[t] = old;
        }
    }
}

static int bestN = 0, bM, bK, bR;
static int bS[MAXD];

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [nstart] < /dev/null\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long nstart = argc > 5 ? atol(argv[5]) : d + 1;
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    long moore = moore_bound();
    long Nt_l = nstart > d + 1 ? nstart : d + 1;
    int Nt = (int)(Nt_l > MAXG ? MAXG + 1 : Nt_l);

    while (now() < t_end) {
        if (2L * Nt > moore || Nt > MAXG) break;
        enumerate_groups(Nt);
        int ok = 0;
        while (!ok && now() < t_end) {
            int idx = 0;
            for (int tries = 0; tries < 30; tries++) {
                idx = rndint(ntr);
                if (TM[idx] > 1 && TK[idx] > 1 && TR[idx] != 1) break;
            }
            build_group(TM[idx], TK[idx], TR[idx]);
            ok = sa_attempt();
        }
        if (!ok) break;
        bestN = N;
        bM = GM; bK = GK; bR = GR;
        for (int t = 0; t < d; t++) bS[t] = S[t];
        Nt = N + 1;
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    build_group(bM, bK, bR);
    for (int t = 0; t < d; t++) S[t] = bS[t];
    if (cost_of() != 0) { printf("0 0\n"); return 0; }
    long m = (long)N * d;
    printf("%d %ld\n", 2 * N, m);
    for (int g = 0; g < N; g++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", g, N + MUL[g * N + S[t]]);
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
        """Adopt (n, e) if it is a larger valid graph."""
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

    # Cayley double-cover search in C, climbing the group order from the current best.
    if D >= 2 and d >= 2:
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 1.0:
            nstart = max(d + 1, best[0] // 2 + 1)
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2), nstart],
                                 stdin_graph=None, timeout=c_budget + 8)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
