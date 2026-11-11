"""Two-base-vertex bi-Cayley lift search for the weakest case (d = 5, D = 7 is the target).

Construction: for a group G = Z_m x|_r Z_k of order N and a base multigraph on P + P vertices
(P = 1 or 2), take vertices A_{i,x} and B_{j,y} (x, y in G). Each dart (i, j, g) joins
A_{i,x} to B_{j, x*g}. Darts from A_i and into B_j each number d, so the lift is d-regular and
bipartite. Left multiplication by G is an automorphism whose orbits are the base vertices, so the
diameter check needs only BFS from A_{i,e} and B_{j,e}.

The 2-base case uses a count matrix [[a, d-a], [d-a, a]], which is a genuinely different base
from the single-vertex bi-Cayley graphs used before. The C engine hill-climbs the voltages with
annealing and searches group orders above the current best. The best valid algebraic start
(hexagon, generalized quadrangle, or projective plane) is the fallback. Every returned graph is
checked with lib.is_valid.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-base lift search over semidirect groups Z_m x|_r Z_k.
 * Usage:  prog d D seed time_limit threshold
 * stdout: "n m" and edges of the best lift with n > threshold, or "0 0" if none was found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1600
#define MAXD 16
#define MAXP 2
#define MAXDART (MAXP * MAXD)
#define MAXV (2 * MAXP * MAXN)
#define MAXCAND 4096
#define STEPS 20000
#define SPAN 24

typedef struct { int m, k, r; } Grp;

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long moore_bound_l(void) {
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

static int enum_groups(int N, Grp *out) {
    int cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (cnt < MAXCAND) { out[cnt].m = 1; out[cnt].k = k; out[cnt].r = 0; cnt++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1 % m) continue;
            if (cnt < MAXCAND) { out[cnt].m = m; out[cnt].k = k; out[cnt].r = r; cnt++; }
        }
    }
    return cnt;
}

static Grp pick_group(const Grp *c, int cnt) {
    if (rnd01() < 0.6) {
        for (int tries = 0; tries < 16; tries++) {
            Grp g = c[rndint(cnt)];
            if (g.m > 1 && g.r != 1) return g;
        }
    }
    return c[rndint(cnt)];
}

/* Group multiplication table. Element 0 is the identity. */
static int MTAB[MAXN * MAXN];
static int INVT[MAXN];
static int RP[MAXN];
static int NN;

static void setup_group(int N, Grp G) {
    NN = N;
    int m = G.m, k = G.k;
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * G.r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            row[y] = (int)((((long)a + (long)RP[b] * c) % m) * k + (b + e) % k);
        }
    }
    for (int x = 0; x < N; x++) {
        for (int y = 0; y < N; y++)
            if (MTAB[(size_t)x * N + y] == 0) { INVT[x] = y; break; }
    }
}

/* Base graph layout: darts from A_i to B_j, grouped by i (contiguous, d per i). */
static int P;
static int NDART;
static int DU[MAXDART], DV[MAXDART], DG[MAXDART], BL[MAXDART];
static int blkCnt[MAXP * MAXP];
static int blkDart[MAXP * MAXP][MAXD];
static int BDN[MAXP][MAXD];

static void layout(int Pn, int cnt[MAXP][MAXP]) {
    P = Pn;
    NDART = 0;
    for (int b = 0; b < MAXP * MAXP; b++) blkCnt[b] = 0;
    for (int i = 0; i < P; i++)
        for (int j = 0; j < P; j++)
            for (int t = 0; t < cnt[i][j]; t++) {
                int e = NDART++;
                DU[e] = i;
                DV[e] = j;
                BL[e] = i * P + j;
                blkDart[i * P + j][blkCnt[i * P + j]++] = e;
            }
    for (int j = 0; j < P; j++) {
        int c = 0;
        for (int e = 0; e < NDART; e++)
            if (DV[e] == j && c < MAXD) BDN[j][c++] = e;
    }
}

static void init_volts(void) {
    for (int b = 0; b < P * P; b++)
        for (int t = 0; t < blkCnt[b]; t++) {
            int e = blkDart[b][t];
            int g, ok;
            do {
                g = rndint(NN);
                ok = 1;
                for (int s = 0; s < t; s++)
                    if (DG[blkDart[b][s]] == g) { ok = 0; break; }
            } while (!ok);
            DG[e] = g;
        }
}

static int used_other(int b, int e, int g) {
    for (int t = 0; t < blkCnt[b]; t++) {
        int f = blkDart[b][t];
        if (f != e && DG[f] == g) return 1;
    }
    return 0;
}

static int distv[MAXV], seenv[MAXV], qv[MAXV];
static int stamp_ = 0;

/* Number of (source, vertex) pairs at distance > D; sources A_{i,e} and B_{j,e}. */
static long eval_bad(void) {
    int N = NN;
    int PN = P * N;
    int V = 2 * PN;
    long total = 0;
    for (int s = 0; s < 2 * P; s++) {
        int src = (s < P) ? (s * N) : (PN + (s - P) * N);
        int head = 0, tail = 0;
        stamp_++;
        seenv[src] = stamp_;
        distv[src] = 0;
        qv[tail++] = src;
        while (head < tail) {
            int v = qv[head++];
            int dv = distv[v];
            if (dv >= D) continue;
            if (v < PN) {
                int i = v / N, x = v % N;
                const int *row = MTAB + (size_t)x * N;
                int lo = i * d;
                for (int e = lo; e < lo + d; e++) {
                    int u = PN + DV[e] * N + row[DG[e]];
                    if (seenv[u] != stamp_) {
                        seenv[u] = stamp_;
                        distv[u] = dv + 1;
                        qv[tail++] = u;
                    }
                }
            } else {
                int w = v - PN;
                int j = w / N, y = w % N;
                for (int q2 = 0; q2 < d; q2++) {
                    int e = BDN[j][q2];
                    int x = MTAB[(size_t)y * N + INVT[DG[e]]];
                    int u = DU[e] * N + x;
                    if (seenv[u] != stamp_) {
                        seenv[u] = stamp_;
                        distv[u] = dv + 1;
                        qv[tail++] = u;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

static long climb(double until) {
    long bad = eval_bad();
    double T = 2.0;
    for (long s = 0; s < STEPS && bad > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        int e = rndint(NDART);
        int b = BL[e];
        int old = DG[e], nv;
        do { nv = rndint(NN); } while (used_other(b, e, nv));
        DG[e] = nv;
        long nb = eval_bad();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else DG[e] = old;
        T *= 0.9997;
        if (T < 0.2) T = 0.2;
    }
    return bad;
}

static int feasible(int Pt, long best_total, long moore) {
    long Nlo = best_total / (2L * Pt) + 1;
    if (Nlo < d + 2) Nlo = d + 2;
    long Nhi = moore / (2L * Pt);
    if (Nhi > MAXN) Nhi = MAXN;
    return Nlo <= Nhi;
}

static int bestP = 0, bestN = 0, bestNDART = 0;
static Grp bestG;
static int bestDU[MAXDART], bestDV[MAXDART], bestDG[MAXDART];
static Grp cand[MAXCAND];

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit threshold\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long thr = atol(argv[5]);
    double t0 = now();
    t_end = t0 + limit;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    long moore = moore_bound_l();
    long best_total = thr;
    int found = 0;
    static int cnt[MAXP][MAXP];

    while (now() < t_end) {
        int Pt = (rnd01() < 0.8) ? 2 : 1;
        if (!feasible(Pt, best_total, moore)) Pt = 3 - Pt;
        if (!feasible(Pt, best_total, moore)) break;

        long Nlo = best_total / (2L * Pt) + 1;
        if (Nlo < d + 2) Nlo = d + 2;
        long Nhi = moore / (2L * Pt);
        if (Nhi > MAXN) Nhi = MAXN;
        long span = Nhi - Nlo + 1;
        if (span > SPAN) span = SPAN;
        int N = (int)(Nlo + rndint((int)span));

        int nc = enum_groups(N, cand);
        if (nc <= 0) continue;
        Grp G = pick_group(cand, nc);

        for (int i = 0; i < MAXP; i++)
            for (int j = 0; j < MAXP; j++) cnt[i][j] = 0;
        if (Pt == 1) {
            cnt[0][0] = d;
        } else {
            int a = 1 + rndint(d / 2);
            cnt[0][0] = a;
            cnt[0][1] = d - a;
            cnt[1][0] = d - a;
            cnt[1][1] = a;
        }

        setup_group(N, G);
        layout(Pt, cnt);
        init_volts();
        long bad = climb(t_end);
        if (bad == 0) {
            long total = 2L * Pt * N;
            if (total > best_total) {
                best_total = total;
                found = 1;
                bestP = Pt;
                bestN = N;
                bestG = G;
                bestNDART = NDART;
                memcpy(bestDU, DU, sizeof(int) * NDART);
                memcpy(bestDV, DV, sizeof(int) * NDART);
                memcpy(bestDG, DG, sizeof(int) * NDART);
            }
        }
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    setup_group(bestN, bestG);
    int N = bestN, P2 = bestP;
    long E = (long)bestNDART * N;
    printf("%d %ld\n", 2 * P2 * N, E);
    for (int e = 0; e < bestNDART; e++) {
        for (int x = 0; x < N; x++) {
            int u = bestDU[e] * N + x;
            int w = P2 * N + bestDV[e] * N + MTAB[(size_t)x * N + bestDG[e]];
            printf("%d %d\n", u, w);
        }
    }
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
    The caller validates the result with lib.is_valid.
    """
    F = lib.GF(q)
    MT, AT = F.mul_table, F.add_table
    pts = []
    for v in itertools.product(range(q), repeat=7):
        if any(v) and next(c for c in v if c) == 1:
            s = AT[AT[MT[v[0], v[4]], MT[v[1], v[5]]], AT[MT[v[2], v[6]], MT[v[3], v[3]]]]
            if s == 0:
                pts.append(tuple(int(c) for c in v))
    N = len(pts)
    index = {v: i for i, v in enumerate(pts)}
    P = np.array(pts, dtype=np.int64)
    lines = set()
    for i in range(N - 1):
        x = P[i]
        Y = P[i + 1:]

        def pp(a, b):
            """Grassmann coordinate p_ab = x_a y_b - x_b y_a, for all y in Y."""
            return AT[MT[x[a], Y[:, b]], MT[x[b], Y[:, a]]]

        s = np.zeros(len(Y), dtype=np.int64)
        for a, b in ((0, 4), (1, 5), (2, 6)):
            s = AT[s, AT[MT[x[a], Y[:, b]], MT[Y[:, a], x[b]]]]
        ok = (s == 0)
        ok &= pp(1, 2) == pp(3, 4)
        ok &= pp(5, 4) == pp(3, 2)
        ok &= pp(2, 0) == pp(3, 5)
        ok &= pp(6, 5) == pp(3, 0)
        ok &= pp(0, 1) == pp(3, 6)
        ok &= pp(4, 6) == pp(3, 1)
        for jj in np.nonzero(ok)[0]:
            y = Y[jj]
            vecs = [tuple(int(c) for c in x)]
            for t in range(q):
                vecs.append(tuple(int(AT[MT[t, x[k]], y[k]]) for k in range(7)))
            idx = []
            for v in vecs:
                c = next(e for e in v if e)
                inv = F.inv(c)
                idx.append(index[tuple(F.mul(inv, e) for e in v)])
            lines.add(tuple(sorted(idx)))
    lines = sorted(lines)
    edges = [(pt, N + k) for k, L in enumerate(lines) for pt in L]
    return 2 * N, edges


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates (may be empty); build() keeps only those that pass lib.is_valid."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 6 and d - 1 in (2, 4):
        try:
            out.append(_hexagon_incidence(d - 1))
        except Exception:
            pass
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            try:
                out.append(_gq_w(q))
            except Exception:
                pass
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # Safe fallback: K_{d,d} has diameter 2 <= D for D >= 2.
    best = lib.haar_graph(d, range(d))
    try:
        starts = known_starts(d, D)
    except Exception:
        starts = []
    for n, e in starts:
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d < 3 or d > 16:
        return best

    budget = 0.80 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 2.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         stdin_graph=None, timeout=budget + 6)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except Exception:
        pass
    return best
