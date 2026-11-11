"""Base-graph lift search (K fibers per side, semidirect group voltages) for the weakest cases.

Construction: a bipartite base with K vertices per side and d permutation darts P_t, t < d.
Lift over a group G of order M (semidirect Z_m x| Z_k): A-vertex (u, x) is joined to
B-vertex (P_t(u), x * g_{t,u}) for each t. Every vertex has degree d. Left multiplication by G
is an automorphism that is transitive on each fiber, so the diameter check needs BFS from one
representative per fiber (2K BFS runs). Simulated annealing repairs the voltages until no pair is
at distance > D. Orders 2KM above the start graph's order are searched at random, and the
largest valid lift is returned. Otherwise the algebraic start graph is returned unchanged.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Base-graph lift search over semidirect groups Z_m x|_r Z_k.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0".
 * stdout:  the best valid graph found (lift if it beats the start, else the start).
 *
 * Vertices: A-fiber u, element x -> u*M + x  (u < K);  B-fiber v, element y -> (K+v)*M + y.
 * Darts:    for t < d, permutation P[t] of {0..K-1}; voltage G[t][u] in G.
 *           A(u,x) -- B(P[t][u], x * G[t][u]) for all t.
 * Simplicity: darts from the same A-fiber to the same B-fiber need distinct voltages.
 * Diameter:  each fiber is transitive under left multiplication, so BFS from A(u,e) and B(v,e)
 *            for all fibers suffices.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 16
#define MAXK 3
#define MAXV 8192
#define MAXM 4096
#define MAXE 40000
#define MAXGC 20000
#define SPAN 60
#define STEPS 6000

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

/* Group state: element index e = a*gk + b, (a,b)*(c,f) = (a + r^b c, b + f). */
static int K, M, gm, gk;
static int RP[MAXM];
static int P[MAXD][MAXK], PI[MAXD][MAXK];
static int G[MAXD][MAXK], GI[MAXD][MAXK];

static void setup_group(int m, int k2, int r) {
    gm = m;
    gk = k2;
    M = m * k2;
    RP[0] = 1 % m;
    for (int b = 1; b < k2; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
}

static inline int gmul(int x, int g) {
    int a = x / gk, b = x - a * gk;
    int c = g / gk, e = g - c * gk;
    int aa = (int)(((long)a + (long)RP[b] * c) % gm);
    int bb = b + e;
    if (bb >= gk) bb -= gk;
    return aa * gk + bb;
}

static inline int ginv(int g) {
    int a = g / gk, b = g - a * gk;
    int nb = (gk - b) % gk;
    int na = (int)((gm - ((long)RP[nb] * a) % gm) % gm);
    return na * gk + nb;
}

static int GCM[MAXGC], GCK[MAXGC], GCR[MAXGC];

static int enum_groups(int Mt) {
    int cnt = 0;
    for (int m = 1; m <= Mt; m++) {
        if (Mt % m) continue;
        int k2 = Mt / m;
        if (m == 1) {
            if (cnt < MAXGC) { GCM[cnt] = 1; GCK[cnt] = k2; GCR[cnt] = 0; cnt++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k2, m) != 1 % m) continue;
            if (cnt < MAXGC) { GCM[cnt] = m; GCK[cnt] = k2; GCR[cnt] = r; cnt++; }
        }
    }
    return cnt;
}

static void random_perms(void) {
    for (int t = 0; t < d; t++) {
        int p[MAXK];
        for (int u = 0; u < K; u++) p[u] = u;
        for (int u = K - 1; u > 0; u--) {
            int j = rndint(u + 1);
            int tmp = p[u]; p[u] = p[j]; p[j] = tmp;
        }
        for (int u = 0; u < K; u++) {
            P[t][u] = p[u];
            PI[t][p[u]] = u;
        }
    }
}

/* True if putting voltage nv on dart (t,u) would duplicate an edge with another dart of u. */
static int conflict(int t, int u, int nv) {
    for (int tt = 0; tt < d; tt++) {
        if (tt == t) continue;
        if (P[tt][u] == P[t][u] && G[tt][u] == nv) return 1;
    }
    return 0;
}

static int init_voltages(void) {
    for (int t = 0; t < d; t++)
        for (int u = 0; u < K; u++) { G[t][u] = -1; GI[t][u] = -1; }
    for (int t = 0; t < d; t++) {
        for (int u = 0; u < K; u++) {
            int st = rndint(M), ch = -1;
            for (int i = 0; i < M; i++) {
                int nv = (st + i) % M;
                if (!conflict(t, u, nv)) { ch = nv; break; }
            }
            if (ch < 0) return 0;
            G[t][u] = ch;
            GI[t][u] = ginv(ch);
        }
    }
    return 1;
}

static int dist_[MAXV], seen_[MAXV], q_[MAXV];
static int stamp_ = 0;

/* Number of (fiber representative, vertex) pairs at distance > D. */
static long eval_bad(void) {
    int V = 2 * K * M;
    long total = 0;
    for (int s = 0; s < 2 * K; s++) {
        int src = s * M;
        int head = 0, tail = 0;
        stamp_++;
        seen_[src] = stamp_;
        dist_[src] = 0;
        q_[tail++] = src;
        while (head < tail) {
            int v = q_[head++];
            int dv = dist_[v];
            if (dv >= D) continue;
            int f = v / M, x = v - f * M;
            if (f < K) {
                for (int t = 0; t < d; t++) {
                    int w = (K + P[t][f]) * M + gmul(x, G[t][f]);
                    if (seen_[w] != stamp_) {
                        seen_[w] = stamp_;
                        dist_[w] = dv + 1;
                        q_[tail++] = w;
                    }
                }
            } else {
                int vv = f - K;
                for (int t = 0; t < d; t++) {
                    int u = PI[t][vv];
                    int w = u * M + gmul(x, GI[t][u]);
                    if (seen_[w] != stamp_) {
                        seen_[w] = stamp_;
                        dist_[w] = dv + 1;
                        q_[tail++] = w;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

/* Annealed voltage repair. Returns the remaining number of bad pairs. */
static long climb(long steps, double until) {
    long bad = eval_bad();
    double T = 2.0;
    for (long s = 0; s < steps && bad > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int t = rndint(d), u = rndint(K);
        int nv = rndint(M);
        if (nv == G[t][u] || conflict(t, u, nv)) continue;
        int old = G[t][u], oldi = GI[t][u];
        G[t][u] = nv;
        GI[t][u] = ginv(nv);
        long nb = eval_bad();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else { G[t][u] = old; GI[t][u] = oldi; }
        T *= 0.9995;
        if (T < 0.3) T = 0.3;
    }
    return bad;
}

static int OU[MAXV * MAXD], OV[MAXV * MAXD];

static int build_edges(void) {
    int ne = 0;
    for (int u = 0; u < K; u++)
        for (int x = 0; x < M; x++)
            for (int t = 0; t < d; t++) {
                OU[ne] = u * M + x;
                OV[ne] = (K + P[t][u]) * M + gmul(x, G[t][u]);
                ne++;
            }
    return ne;
}

static int SU[MAXE], SV[MAXE];

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
    if (sn < 0 || sm < 0 || sm > MAXE) { sn = 0; sm = 0; }
    int got = 0;
    for (int e = 0; e < sm; e++) {
        if (scanf("%d %d", &SU[e], &SV[e]) != 2) break;
        got++;
    }
    if (got != sm) { sn = 0; sm = 0; }

    int found = 0, ne = 0;
    long bestTot = sn;

    if (d >= 3 && d <= MAXD && D >= 2 && bestTot < moore_bound()) {
        long moore = moore_bound();
        while (now() < t_end && bestTot < moore) {
            int nvi = 0;
            int vK[MAXK], vLo[MAXK], vHi[MAXK];
            for (int kk = 1; kk <= MAXK; kk++) {
                long lo = (bestTot + 2L * kk) / (2L * kk);  /* ceil((bestTot+1)/(2kk)) */
                if (lo < d + 1) lo = d + 1;
                long hi = MAXV / (2L * kk);
                if (hi > MAXM) hi = MAXM;
                if (lo <= hi) {
                    vK[nvi] = kk; vLo[nvi] = (int)lo; vHi[nvi] = (int)hi; nvi++;
                }
            }
            if (nvi == 0) break;
            int idx = rndint(nvi);
            K = vK[idx];
            int lo = vLo[idx], hi = vHi[idx];
            int span = hi - lo + 1;
            if (span > SPAN) span = SPAN;
            int Mt = lo + rndint(span);
            int cnt = enum_groups(Mt);
            if (cnt <= 0) continue;
            int gi = rndint(cnt);
            setup_group(GCM[gi], GCK[gi], GCR[gi]);
            random_perms();
            if (!init_voltages()) continue;
            long bad = climb(STEPS, t_end);
            if (bad == 0) {
                found = 1;
                bestTot = 2L * K * M;
                ne = build_edges();
            }
        }
    }

    if (found) {
        printf("%ld %d\n", bestTot, ne);
        for (int i = 0; i < ne; i++) printf("%d %d\n", OU[i], OV[i]);
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
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 16 or best[0] >= lib.moore_bound(d, D):
        return best

    # Stay well inside the 60 s limit: compile and Python overhead come out of this margin.
    budget = min(0.8 * time_limit, time_limit - 8.0) - (time.monotonic() - t0)
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 6.0)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
