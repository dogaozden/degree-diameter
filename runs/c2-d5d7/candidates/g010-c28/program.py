"""Multi-base voltage lift search for the weak cases (d = 5, D = 7 is the target).

New in this version: the C engine searches voltage lifts of a base bipartite multigraph with s
vertices per side (s = 1..4), not only the bi-Cayley case s = 1 used by the parent.

Construction: base A-vertices A_0..A_{s-1} and B-vertices B_0..B_{s-1}. Each A_i has d darts
(i, tgt[i][t], vol[i][t]), where tgt is a target B-index and vol is a voltage in a group G of order
N. Every B_j receives exactly d darts (the target multiset is preserved by all moves). The lift has
vertices A_i x G and B_j x G and edges A_{i,x} -- B_{j, x*g} for each dart (i, j, g). Its order is
2*s*N, and it is d-regular and bipartite.

Left multiplication by G is an automorphism that is transitive on each fibre, so diameter <= D
holds iff BFS from A_{i,e} and from B_{j,e} (2s sources) reaches everything within D.

Moves (simulated annealing on the number of bad (source, vertex) pairs):
  - change one voltage;
  - swap the targets of two darts (rewires the base graph and keeps column counts).
Both moves reject any row with two darts to the same target with the same voltage, so the lift
stays simple.

The group is a semidirect product Z_m x|_r Z_k, as in the parent. The start graph (hexagon or
projective plane) is returned unchanged if no lift beats it. Python validates everything.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-base voltage lift search over semidirect groups Z_m x|_r Z_k.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0".
 * stdout:  the best valid graph found (lift if it beats the start, else the start).
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXS 4
#define MAXD 16
#define MAXN 1800
#define MAXV (2 * MAXS * MAXN)
#define MAXCAND 512
#define STEPS 6000
#define SPAN 30
#define INMAX 300000

typedef struct { int m, k, r; } Grp;

static int d, D;
static double t_end;
static int SB = 1, NN = 1;

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

/* Enumerate Z_m x|_r Z_k with m*k = N, gcd(r,m)=1, r^k = 1 mod m. */
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
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (cnt < MAXCAND) { out[cnt].m = m; out[cnt].k = k; out[cnt].r = r; cnt++; }
        }
    }
    return cnt;
}

static Grp pick_group(const Grp *c, int cnt) {
    for (int tries = 0; tries < 8; tries++) {
        Grp g = c[rndint(cnt)];
        if (g.m > 1 && g.r != 1) return g;
    }
    return c[rndint(cnt)];
}

/* Multiplication table, inverses and power table for the current group. */
static int MTAB[MAXN * MAXN];
static int INVT[MAXN];
static int RP[MAXN];

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
    /* (a,b)^(-1) = (-r^(-b) a, -b), and r^(-b) = r^((k-b) mod k). */
    for (int x = 0; x < N; x++) {
        long a = x / k, b = x % k;
        int nb = (int)((k - b) % k);
        long na = (m - ((long)RP[nb] * a) % m) % m;
        INVT[x] = (int)(na * k + nb);
    }
}

/* Base-graph state: dart (i,t) goes from A_i to B_{tgt[i][t]} with voltage vol[i][t]. */
static int tgt[MAXS][MAXD], vol[MAXS][MAXD], invv[MAXS][MAXD];
static int incI[MAXS][MAXD], incInv[MAXS][MAXD];
static int distv[MAXV], seenv[MAXV], qv[MAXV];
static int stamp_ = 0;

/* True if dart (i,t) duplicates another dart of row i (same target and same voltage). */
static int dup_dart(int i, int t) {
    for (int u = 0; u < d; u++)
        if (u != t && tgt[i][u] == tgt[i][t] && vol[i][u] == vol[i][t]) return 1;
    return 0;
}

static int row_ok_all(void) {
    for (int i = 0; i < SB; i++)
        for (int t = 0; t < d; t++)
            if (dup_dart(i, t)) return 0;
    return 1;
}

/* Number of (source, vertex) pairs at distance > D over the 2s block representatives. */
static long eval_bad(void) {
    int s = SB, N = NN, base = s * N, V = 2 * s * N;
    int cnt[MAXS];
    memset(cnt, 0, sizeof cnt);
    for (int i = 0; i < s; i++)
        for (int t = 0; t < d; t++) {
            int j = tgt[i][t];
            incI[j][cnt[j]] = i;
            incInv[j][cnt[j]] = invv[i][t];
            cnt[j]++;
        }
    long total = 0;
    for (int si = 0; si < 2 * s; si++) {
        int src = si * N;  /* block si, identity element 0 */
        stamp_++;
        int head = 0, tail = 0;
        seenv[src] = stamp_;
        distv[src] = 0;
        qv[tail++] = src;
        while (head < tail) {
            int v = qv[head++];
            int dv = distv[v];
            if (dv >= D) continue;
            if (v < base) {
                int i = v / N, x = v - i * N;
                const int *row = MTAB + (size_t)x * N;
                for (int t = 0; t < d; t++) {
                    int u = (s + tgt[i][t]) * N + row[vol[i][t]];
                    if (seenv[u] != stamp_) {
                        seenv[u] = stamp_;
                        distv[u] = dv + 1;
                        qv[tail++] = u;
                    }
                }
            } else {
                int w = v - base;
                int j = w / N, y = w - j * N;
                const int *row = MTAB + (size_t)y * N;
                for (int k = 0; k < d; k++) {
                    int u = incI[j][k] * N + row[incInv[j][k]];
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

/* Random simple base state: targets form a multiset with each j repeated d times. */
static void random_state(void) {
    int pool[MAXS * MAXD];
    int P = SB * d;
    for (int p = 0; p < P; p++) pool[p] = p / d;
    for (int p = P - 1; p > 0; p--) {
        int q = rndint(p + 1);
        int tmp = pool[p]; pool[p] = pool[q]; pool[q] = tmp;
    }
    for (int i = 0; i < SB; i++)
        for (int t = 0; t < d; t++) {
            tgt[i][t] = pool[i * d + t];
            vol[i][t] = 0;
        }
    for (int i = 0; i < SB; i++)
        for (int t = 0; t < d; t++) {
            int tries = 0;
            do {
                vol[i][t] = rndint(NN);
                tries++;
            } while (dup_dart(i, t) && tries < 200);
            invv[i][t] = INVT[vol[i][t]];
        }
}

/* Simulated annealing over voltage changes and target swaps. */
static long climb(double until) {
    long bad = eval_bad();
    double T = 2.0;
    for (long st = 0; st < STEPS && bad > 0; st++) {
        if ((st & 127) == 0 && now() > until) break;
        T *= 0.9995;
        if (T < 0.2) T = 0.2;
        if (rnd01() < 0.5) {
            int i = rndint(SB), t = rndint(d);
            int ov = vol[i][t], nv = rndint(NN);
            if (nv == ov) continue;
            vol[i][t] = nv;
            invv[i][t] = INVT[nv];
            if (dup_dart(i, t)) {
                vol[i][t] = ov;
                invv[i][t] = INVT[ov];
                continue;
            }
            long nb = eval_bad();
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
                bad = nb;
            } else {
                vol[i][t] = ov;
                invv[i][t] = INVT[ov];
            }
        } else {
            if (SB == 1) continue;
            int i1 = rndint(SB), t1 = rndint(d), i2 = rndint(SB), t2 = rndint(d);
            int j1 = tgt[i1][t1], j2 = tgt[i2][t2];
            if (j1 == j2) continue;
            tgt[i1][t1] = j2;
            tgt[i2][t2] = j1;
            if (dup_dart(i1, t1) || dup_dart(i2, t2)) {
                tgt[i1][t1] = j1;
                tgt[i2][t2] = j2;
                continue;
            }
            long nb = eval_bad();
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
                bad = nb;
            } else {
                tgt[i1][t1] = j1;
                tgt[i2][t2] = j2;
            }
        }
    }
    return bad;
}

static int SU[INMAX], SV[INMAX];
static int OU[MAXS * MAXN * MAXD], OV[MAXS * MAXN * MAXD];

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    int sn = 0, sm = 0;
    if (scanf("%d %d", &sn, &sm) != 2) { sn = 0; sm = 0; }
    if (sn < 0 || sm < 0 || sm > INMAX) { sn = 0; sm = 0; }
    int got = 0;
    for (int e = 0; e < sm; e++) {
        if (scanf("%d %d", &SU[e], &SV[e]) != 2) break;
        got++;
    }
    if (got != sm) { sn = 0; sm = 0; }

    int found = 0, bestS = 0, bestN = 0;
    Grp bestG;
    memset(&bestG, 0, sizeof bestG);
    static int bTgt[MAXS][MAXD], bVol[MAXS][MAXD];
    long bestV = sn;

    if (d >= 3 && d <= MAXD && D >= 2) {
        long moore = moore_bound();
        static Grp cand[MAXCAND];
        while (now() < t_end) {
            int feas[MAXS], nf = 0;
            long lo_s[MAXS + 1], hi_s[MAXS + 1];
            for (int s2 = 1; s2 <= MAXS; s2++) {
                long lo = bestV / (2L * s2) + 1;
                if (lo < d + 1) lo = d + 1;
                long hi = moore / (2L * s2);
                if (hi > MAXN) hi = MAXN;
                if (lo <= hi) {
                    feas[nf++] = s2;
                    lo_s[s2] = lo;
                    hi_s[s2] = hi;
                }
            }
            if (nf == 0) break;
            int s2 = feas[rndint(nf)];
            long lo = lo_s[s2], hi = hi_s[s2];
            long span = hi - lo + 1;
            if (span > SPAN) span = SPAN;
            int N = (int)(lo + rndint((int)span));
            int cnt = enum_groups(N, cand);
            if (cnt <= 0) continue;
            Grp G = pick_group(cand, cnt);
            setup_group(N, G);
            SB = s2;
            random_state();
            if (!row_ok_all()) continue;
            long bad = climb(t_end);
            if (bad == 0) {
                found = 1;
                bestV = 2L * s2 * N;
                bestS = s2;
                bestN = N;
                bestG = G;
                memcpy(bTgt, tgt, sizeof tgt);
                memcpy(bVol, vol, sizeof vol);
            }
        }
    }

    if (found) {
        int s = bestS, N = bestN;
        SB = s;
        setup_group(N, bestG);
        long ne = 0;
        for (int i = 0; i < s; i++)
            for (int x = 0; x < N; x++)
                for (int t = 0; t < d; t++) {
                    OU[ne] = i * N + x;
                    OV[ne] = s * N + bTgt[i][t] * N + MTAB[(size_t)x * N + bVol[i][t]];
                    ne++;
                }
        printf("%d %ld\n", 2 * s * N, ne);
        for (long i = 0; i < ne; i++) printf("%d %d\n", OU[i], OV[i]);
    } else {
        printf("%d %d\n", sn, sm);
        for (int e = 0; e < sm; e++) printf("%d %d\n", SU[e], SV[e]);
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
    Points: points of the quadric X0X4 + X1X5 + X2X6 = X3^2. Lines: quadric lines whose Grassmann
    coordinates satisfy p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31.
    Characteristic 2, so signs are irrelevant. The caller validates the result with lib.is_valid.
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

        # Collinearity on the quadric: polar form B(x, y) = 0 (char 2 has no 2*x3*y3 term).
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
            # Points of the line: x, and t*x + y for t in GF(q).
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
            out.append(_gq_w(q))
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 16 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
