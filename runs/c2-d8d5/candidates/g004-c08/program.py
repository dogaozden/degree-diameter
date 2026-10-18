"""Lift-annealing search for bipartite degree-diameter graphs.

Main idea: a bipartite graph with a base of P vertices per side and a group G of order N
is a voltage lift (left (i,x) ~ right (sigma_t(i), x*g) for each layer t). G acts by left
multiplication, so the diameter check needs BFS from only the 2P fibre representatives.
C simulated annealing searches over layer permutations and voltages in semidirect products
Z_m x| Z_k, with early-abort evaluation. Exact constructions remain as the fallback.
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
# C engine: voltage-lift annealing over semidirect groups.
# Vertices: left (i,x) = i*N + x, right (j,y) = (P+j)*N + y.
# Layer t joins left i to right SIG[t][i] with voltage VOL[t][i]:
#   (i,x) ~ (P+SIG[t][i], x*VOL[t][i]).
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Voltage-lift annealing for bipartite degree-diameter graphs.
 * Usage:  prog d D seed time_limit [start_n]
 * Only lifts with more than start_n vertices are emitted; otherwise prints "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1024
#define MAXP 6
#define MAXD 16
#define MAXV (2 * MAXP * MAXG)

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
static int gcdi(int a, int b) {
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
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000L) break;
    }
    return 2 * s;
}

/* Current group: element index a*gk+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k). */
static int N, P;
static int gm, gk, gr;
static int MUL[MAXG][MAXG];
static int INV[MAXG];

static int build_group(int m, int k, int r) {
    int n = m * k;
    if (n < 1 || n > MAXG) return 0;
    gm = m; gk = k; gr = r; N = n;
    int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < n; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < n; y++) {
            int c = y / k, e = y % k;
            MUL[x][y] = (int)((((long)a + (long)rp[b] * c) % m) * k + (b + e) % k);
        }
    }
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (MUL[x][y] == 0) { INV[x] = y; break; }
    return 1;
}

/* Uniform random semidirect group of order Nn (r = 1 always qualifies, so never empty). */
static int random_group(int Nn) {
    long cnt = 0;
    int bm = 1, bk = Nn, br = 0;
    for (int k = 1; k <= Nn; k++) {
        if (Nn % k) continue;
        int m = Nn / k;
        if (m == 1) {
            cnt++;
            if (rndint((int)cnt) == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcdi(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { bm = m; bk = k; br = r; }
        }
    }
    return build_group(bm, bk, br);
}

static int SIG[MAXD][MAXP], ISIG[MAXD][MAXP], VOL[MAXD][MAXP];
static int sSIG[MAXD][MAXP], sISIG[MAXD][MAXP], sVOL[MAXD][MAXP];
static int qbuf[MAXV];
static int mark[MAXV];
static int stampc = 0;

/* BFS from each of the 2P fibre representatives; returns total unreached count.
 * Aborts early and returns a value > limit once the partial sum exceeds limit. */
static long eval_limit(double limit) {
    long cost = 0;
    int PN = P * N;
    int S = 2 * P;
    for (int s = 0; s < S; s++) {
        stampc++;
        int qh = 0, qt = 0;
        int src = s * N;
        mark[src] = stampc;
        qbuf[qt++] = src;
        for (int lev = 0; lev < D && qh < qt; lev++) {
            int end = qt;
            while (qh < end) {
                int v = qbuf[qh++];
                if (v < PN) {
                    int i = v / N, x = v - i * N;
                    for (int t = 0; t < d; t++) {
                        int y = MUL[x][VOL[t][i]];
                        int w = (P + SIG[t][i]) * N + y;
                        if (mark[w] != stampc) { mark[w] = stampc; qbuf[qt++] = w; }
                    }
                } else {
                    int jj = v / N - P, y = v - (v / N) * N;
                    for (int t = 0; t < d; t++) {
                        int i = ISIG[t][jj];
                        int x = MUL[y][INV[VOL[t][i]]];
                        int w = i * N + x;
                        if (mark[w] != stampc) { mark[w] = stampc; qbuf[qt++] = w; }
                    }
                }
            }
        }
        cost += (long)(2 * PN - qt);
        if ((double)cost > limit) return cost;
    }
    return cost;
}

static void random_base(void) {
    for (int t = 0; t < d; t++) {
        int perm[MAXP];
        for (int i = 0; i < P; i++) perm[i] = i;
        for (int i = P - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < P; i++) {
            SIG[t][i] = perm[i];
            ISIG[t][perm[i]] = i;
            VOL[t][i] = rndint(N);
        }
    }
}

static void save_state(void) {
    memcpy(sSIG, SIG, sizeof SIG);
    memcpy(sISIG, ISIG, sizeof ISIG);
    memcpy(sVOL, VOL, sizeof VOL);
}
static void restore_state(void) {
    memcpy(SIG, sSIG, sizeof SIG);
    memcpy(ISIG, sISIG, sizeof ISIG);
    memcpy(VOL, sVOL, sizeof VOL);
}

/* Move: swap the right partners of two left vertices in one layer (voltages stay with
 * their left vertex), or resample one voltage. */
static void move(void) {
    int t = rndint(d), i = rndint(P);
    if (P >= 2 && rnd01() < 0.4) {
        int i2 = rndint(P - 1);
        if (i2 >= i) i2++;
        int j1 = SIG[t][i], j2 = SIG[t][i2];
        SIG[t][i] = j2;
        SIG[t][i2] = j1;
        ISIG[t][j2] = i;
        ISIG[t][j1] = i2;
    } else {
        VOL[t][i] = rndint(N);
    }
}

/* Anneal the current group/base until cost 0 (success) or time runs out. */
static int anneal(double until) {
    double start = now(), slice = until - start;
    if (slice <= 0) return 0;
    random_base();
    long cost = eval_limit(1e18);
    double T0 = 1.0 + 0.02 * (double)cost, T = T0;
    long it = 0;
    while (cost > 0) {
        if ((++it & 31) == 0) {
            double tn = now();
            if (tn >= until) break;
            T = T0 * pow(0.02, (tn - start) / slice);
            if (T < 0.05) T = 0.05;
        }
        save_state();
        move();
        double u = rnd01();
        if (u < 1e-12) u = 1e-12;
        double thr = (double)cost - T * log(u);
        long nc = eval_limit(thr);
        if ((double)nc <= thr) cost = nc;
        else restore_state();
    }
    return cost == 0;
}

/* Best solution found so far. */
static int bestN_set = 0;
static int bP, bN, bgm, bgk, bgr;
static int bSIG[MAXD][MAXP], bVOL[MAXD][MAXP];

static void emit_best(void) {
    if (!bestN_set) { printf("0 0\n"); return; }
    build_group(bgm, bgk, bgr);
    P = bP;
    int PN = P * N;
    static int eu[MAXV * MAXD], ev[MAXV * MAXD];
    long m = 0;
    for (int i = 0; i < P; i++)
        for (int x = 0; x < N; x++) {
            int u = i * N + x;
            for (int t = 0; t < d; t++) {
                int j = bSIG[t][i];
                int y = MUL[x][bVOL[t][i]];
                int dup = 0;
                for (int t2 = 0; t2 < t; t2++)
                    if (bSIG[t2][i] == j && MUL[x][bVOL[t2][i]] == y) { dup = 1; break; }
                if (!dup) {
                    eu[m] = u;
                    ev[m] = (P + j) * N + y;
                    m++;
                }
            }
        }
    printf("%d %ld\n", 2 * PN, m);
    for (long e = 0; e < m; e++) printf("%d %d\n", eu[e], ev[e]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [start_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long start_n = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    long moore = moore_bound();
    long bestV = start_n;

    while (now() < t_end) {
        if (bestV + 1 > moore) break;
        int r = rndint(12);
        int Pp = r < 1 ? 1 : r < 3 ? 2 : r < 6 ? 3 : r < 9 ? 4 : r < 11 ? 5 : 6;
        long target = bestV + 1;
        long Nmin = (target + 2L * Pp - 1) / (2L * Pp);
        long Nt = Nmin + rndint(3);
        if (Nt < 1) Nt = 1;
        if (Nt > MAXG || 2L * Pp * Nt > MAXV || 2L * Pp * Nt > moore) continue;
        if (!random_group((int)Nt)) continue;
        P = Pp;
        double rem = t_end - now();
        if (rem <= 0) break;
        double slice = rem / 6.0;
        if (slice > 8.0) slice = 8.0;
        if (slice < 1.5) slice = 1.5;
        if (slice > rem) slice = rem;
        if (anneal(now() + slice)) {
            bestV = 2L * P * N;
            bestN_set = 1;
            bP = P; bN = N; bgm = gm; bgk = gk; bgr = gr;
            memcpy(bSIG, SIG, sizeof SIG);
            memcpy(bVOL, VOL, sizeof VOL);
        }
    }
    emit_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.9 * time_limit - 3.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is larger and valid."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))

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

    # Main search: voltage-lift annealing in C, seeded with the current best order.
    if D >= 2 and d <= 16:
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2), best[0]],
                                 stdin_graph=None, timeout=c_budget + 8)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
