"""Multi-base voltage-lift search for the weakest cases (d = 5, D = 7 is the target).

Construction change from the parent: instead of one base vertex per side (Bi-Cayley), the C engine
searches lifts of a base bipartite graph with s vertices per side (s = 1..4). The base is d-regular:
for each dart index t there is a permutation sigma_t of the s B-vertices, and dart (i, t) joins
A-fiber i to B-fiber sigma_t(i) with a voltage g in G, where G = Z_m x|_r Z_k. The lift has 2*s*|G|
vertices. Left multiplication by G is an automorphism that is transitive on each fibre, so diameter
<= D is checked by BFS from the 2*s fibre representatives. The lift is exact, not a sample.

Moves: change one voltage, or swap two entries of a permutation. Simulated annealing minimises the
number of pairs at distance > D. The best lift above the start order is kept. Otherwise the start
graph (hexagon or projective-plane style algebraic graph, validated in Python) is returned unchanged.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-base voltage lift search over G = Z_m x|_r Z_k.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0".
 * stdout:  best valid graph found (a lift if it beats the start, else the start).
 *
 * Vertices: A-fibre i, element x -> i*N + x            (i < S)
 *           B-fibre j, element y -> (S + j)*N + y       (j < S)
 * Darts:    for each t < d and i < S, sigma_t = SIG[t][i] (a permutation for each t).
 *           Edge (A i,x) -- (B SIG[t][i], x*VOLT[i][t]).
 * Row validity: pairs (SIG[t][i], VOLT[i][t]) distinct over t for each i, so no duplicate edges.
 * Left multiplication by G is an automorphism transitive on each fibre, so the diameter test is
 * BFS from one representative (element 0) of each of the 2S fibres.
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
#define MAXN 8192
#define MAXV 65536
#define MAXIN 300000
#define ATTEMPT 2.5

static int d, D;
static double t_end;

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

/* Group G = Z_GM x|_GR Z_GK, element (a,b) coded as a*GK + b, order GN = GM*GK. */
static int GM, GK, GR, GN;
static int RP[MAXN];

static void setup_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GR = r;
    GN = m * k;
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
}

static int gmul(int x, int y) {
    int a = x / GK, b = x - a * GK;
    int c = y / GK, e = y - c * GK;
    long t = (long)a + (long)RP[b] * c;
    int aa = (int)(t % GM);
    int bb = b + e;
    if (bb >= GK) bb -= GK;
    return aa * GK + bb;
}

static int ginv(int x) {
    int a = x / GK, b = x - a * GK;
    int nb = (GK - b) % GK;
    long t = (long)RP[nb] * a;
    int aa = (int)((GM - t % GM) % GM);
    return aa * GK + nb;
}

/* Random semidirect group of order N, falling back to cyclic Z_N. */
static void sample_group(int N, int *pm, int *pk, int *pr) {
    static int dv[MAXN];
    int nd = 0;
    for (int x = 2; x <= N; x++)
        if (N % x == 0) dv[nd++] = x;
    for (int tries = 0; tries < 30 && nd > 0; tries++) {
        int m = dv[rndint(nd)];
        int k = N / m;
        for (int rt = 0; rt < 100; rt++) {
            int r = 1 + rndint(m - 1);
            if (gcd(r, m) == 1 && powmod(r, k, m) == 1 % m) {
                *pm = m; *pk = k; *pr = r;
                return;
            }
        }
    }
    *pm = 1; *pk = N; *pr = 0;
}

/* Lift state. */
static int S;
static int VOLT[MAXS][MAXD], INVV[MAXS][MAXD];
static int SIG[MAXD][MAXS], ISIG[MAXD][MAXS];

static int row_ok(int i) {
    for (int t = 0; t < d; t++)
        for (int u = t + 1; u < d; u++)
            if (SIG[t][i] == SIG[u][i] && VOLT[i][t] == VOLT[i][u]) return 0;
    return 1;
}

static int all_rows_ok(void) {
    for (int i = 0; i < S; i++)
        if (!row_ok(i)) return 0;
    return 1;
}

static void set_isig(void) {
    for (int t = 0; t < d; t++)
        for (int i = 0; i < S; i++) ISIG[t][SIG[t][i]] = i;
}

static void init_state(void) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < S; i++) SIG[t][i] = i;
        for (int i = S - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = SIG[t][i];
            SIG[t][i] = SIG[t][j];
            SIG[t][j] = tmp;
        }
    }
    set_isig();
    for (int i = 0; i < S; i++) {
        int guard = 0;
        do {
            for (int t = 0; t < d; t++) VOLT[i][t] = rndint(GN);
            guard++;
        } while (!row_ok(i) && guard < 100000);
    }
}

static int dist_[MAXV], seen_[MAXV], q_[MAXV];
static int stamp_ = 0;

/* Number of (fibre representative, vertex) pairs at distance > D. Zero iff the lift is valid. */
static long eval_bad(void) {
    int N = GN, V = 2 * S * N;
    for (int i = 0; i < S; i++)
        for (int t = 0; t < d; t++) INVV[i][t] = ginv(VOLT[i][t]);
    long total = 0;
    for (int f0 = 0; f0 < 2 * S; f0++) {
        int src = f0 * N;
        stamp_++;
        int head = 0, tail = 0;
        seen_[src] = stamp_;
        dist_[src] = 0;
        q_[tail++] = src;
        while (head < tail) {
            int v = q_[head++];
            int dv = dist_[v];
            if (dv >= D) continue;
            int f = v / N, x = v - f * N;
            if (f < S) {
                for (int t = 0; t < d; t++) {
                    int j = SIG[t][f];
                    int u = (S + j) * N + gmul(x, VOLT[f][t]);
                    if (seen_[u] != stamp_) {
                        seen_[u] = stamp_;
                        dist_[u] = dv + 1;
                        q_[tail++] = u;
                    }
                }
            } else {
                int j = f - S;
                for (int t = 0; t < d; t++) {
                    int i = ISIG[t][j];
                    int u = i * N + gmul(x, INVV[i][t]);
                    if (seen_[u] != stamp_) {
                        seen_[u] = stamp_;
                        dist_[u] = dv + 1;
                        q_[tail++] = u;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

/* Undo record for the last move: 0 = voltage, 1 = permutation swap, 2 = no change. */
static int undo_kind, undo_i, undo_i2, undo_t, undo_old;

static void move(void) {
    if (S >= 2 && d >= 2 && rndint(4) == 0) {
        int t = rndint(d);
        int i1 = rndint(S), i2 = rndint(S - 1);
        if (i2 >= i1) i2++;
        int tmp = SIG[t][i1];
        SIG[t][i1] = SIG[t][i2];
        SIG[t][i2] = tmp;
        if (!row_ok(i1) || !row_ok(i2)) {
            tmp = SIG[t][i1];
            SIG[t][i1] = SIG[t][i2];
            SIG[t][i2] = tmp;
            undo_kind = 2;
            return;
        }
        ISIG[t][SIG[t][i1]] = i1;
        ISIG[t][SIG[t][i2]] = i2;
        undo_kind = 1;
        undo_t = t;
        undo_i = i1;
        undo_i2 = i2;
    } else {
        int i = rndint(S), t = rndint(d);
        int old = VOLT[i][t];
        int nv = rndint(GN);
        if (nv == old) { undo_kind = 2; return; }
        VOLT[i][t] = nv;
        if (!row_ok(i)) {
            VOLT[i][t] = old;
            undo_kind = 2;
            return;
        }
        undo_kind = 0;
        undo_i = i;
        undo_t = t;
        undo_old = old;
    }
}

static void undo(void) {
    if (undo_kind == 0) {
        VOLT[undo_i][undo_t] = undo_old;
    } else if (undo_kind == 1) {
        int t = undo_t, i1 = undo_i, i2 = undo_i2;
        int tmp = SIG[t][i1];
        SIG[t][i1] = SIG[t][i2];
        SIG[t][i2] = tmp;
        ISIG[t][SIG[t][i1]] = i1;
        ISIG[t][SIG[t][i2]] = i2;
    }
}

static long anneal(double until) {
    long bad = eval_bad();
    while (bad > 0) {
        if (now() > until) break;
        move();
        if (undo_kind == 2) continue;
        long nb = eval_bad();
        double delta = (double)(nb - bad);
        if (delta <= 0 || rnd01() < exp(-delta / (1.0 + 0.1 * (double)bad))) {
            bad = nb;
        } else {
            undo();
        }
    }
    return bad;
}

/* Best lift found so far. */
static int BS, BN, BM, BK, BR;
static int BSIG[MAXD][MAXS], BVOLT[MAXS][MAXD];

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
    t_end = t0 + (limit > 4.0 ? limit - 1.5 : limit * 0.7);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    static int SU[MAXIN], SV[MAXIN];
    int sn = 0, sm = 0;
    if (scanf("%d %d", &sn, &sm) != 2) { sn = 0; sm = 0; }
    if (sn < 0 || sm < 0 || sm > MAXIN) { sn = 0; sm = 0; }
    int got = 0;
    for (int e = 0; e < sm; e++) {
        if (scanf("%d %d", &SU[e], &SV[e]) != 2) break;
        got++;
    }
    if (got != sm) { sn = 0; sm = 0; }

    int best_n = sn, found = 0;
    if (d >= 3 && d <= MAXD && D >= 2) {
        long moore = moore_bound();
        while (now() < t_end) {
            if (best_n >= moore) break;
            int r = rndint(10);
            S = r < 4 ? 1 : (r < 7 ? 2 : (r < 9 ? 3 : 4));
            long lo = best_n / (2 * S) + 1;
            if (lo < 3 * d) lo = 3 * d;
            long hi = moore / (2 * S);
            if (hi > MAXN) hi = MAXN;
            if (hi > MAXV / (2 * S)) hi = MAXV / (2 * S);
            if (lo > hi) continue;
            long span = hi - lo + 1;
            if (span > 12) span = 12;
            int N = (int)(lo + rndint((int)span));
            int m, k, rr;
            sample_group(N, &m, &k, &rr);
            setup_group(m, k, rr);
            init_state();
            if (!all_rows_ok()) continue;
            double until = now() + ATTEMPT;
            if (until > t_end) until = t_end;
            long bad = anneal(until);
            if (bad == 0 && all_rows_ok()) {
                best_n = 2 * S * N;
                found = 1;
                BS = S; BN = N; BM = m; BK = k; BR = rr;
                for (int t = 0; t < d; t++)
                    for (int i = 0; i < S; i++) BSIG[t][i] = SIG[t][i];
                for (int i = 0; i < S; i++)
                    for (int t = 0; t < d; t++) BVOLT[i][t] = VOLT[i][t];
            }
        }
    }

    if (found) {
        setup_group(BM, BK, BR);
        int N = BN, SS = BS;
        long mtot = (long)SS * N * d;
        printf("%d %ld\n", 2 * SS * N, mtot);
        for (int i = 0; i < SS; i++)
            for (int x = 0; x < N; x++)
                for (int t = 0; t < d; t++) {
                    int a = i * N + x;
                    int b = (SS + BSIG[t][i]) * N + gmul(x, BVOLT[i][t]);
                    printf("%d %d\n", a, b);
                }
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


def _safe(fn, *args):
    try:
        return fn(*args)
    except Exception:
        return None


def known_starts(d, D):
    """Algebraic candidates (may be empty); build() keeps only those that pass lib.is_valid."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(_safe(lib.projective_plane_incidence, d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(_safe(lib.araujo_lopez_graph, d - 2))
    if D >= 6 and d - 1 in (2, 4):
        out.append(_safe(_hexagon_incidence, d - 1))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_safe(_gq_w, q))
    return [c for c in out if c is not None]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 16 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.75 * time_limit - (time.monotonic() - t0) - 3.0
    if budget < 2.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 10)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
