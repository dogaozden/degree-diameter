"""Multi-orbit bi-Cayley lift search for the weakest cases (d = 5, D = 7 is the target).

New idea in this version: the parent used a single G-orbit per side (base graph with one vertex
per side). Here the base has B vertices per side. Vertices are a_{i,x} (i < B, x in G) and
b_{j,y} (j < B, y in G). For each t < d a permutation s_t of {0..B-1} and a voltage g_{i,t} give the
darts a_{i,x} -- b_{s_t(i), x*g_{i,t}}. Every b-vertex then has degree d automatically, and the graph
has 2*B*|G| vertices. Left multiplication by G is an automorphism with B orbits on each side, so the
diameter check needs BFS from a_{i,e} and b_{j,e} for every i and j.

The search mixes voltage moves with permutation swaps, and it samples B in 1..6. Because the order
is 2*B*N, this reaches orders such as 3110 = 2*5*311 with a prime-order group, which the single-orbit
lift cannot reach. Restarts and annealing are kept from the parent. The start graph (H(q) hexagon
incidence, or a smaller algebraic graph) is the fallback, and the Python side checks every result
with lib.is_valid.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-orbit voltage lift search over semidirect groups Z_m x|_r Z_k.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0".
 * stdout:  the best valid graph found (lift if it beats the start, else the start).
 *
 * Vertices: a_{i,x} = i*N + x, b_{j,y} = B*N + j*N + y, with i,j < B and x,y in G, |G| = N.
 * Edges:    for t < d: a_{i,x} -- b_{s_t(i), x*g_{i,t}}, where s_t is a permutation of {0..B-1}
 *           and g_{0,t} is fixed to identity for t = 0 (s_0 = identity).
 * Degree d holds if, for each i, the pairs (s_t(i), g_{i,t}) are distinct over t.
 * Left multiplication by G is an automorphism, so diameter <= D is checked by BFS from a_{i,e}
 * and b_{j,e} for all i, j.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXV 16384
#define MAXD 16
#define MAXB 8
#define MAXE 40000
#define MAXCAND 512
#define STEPS 8000
#define SPAN 40
#define RESTARTS 4
#define BMAX 6

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

/* Group multiplication table and inverses for the current group. */
static int MTAB[MAXN * MAXN];
static int INVT[MAXN];
static int RP[MAXN];
static int NN;   /* group order */
static int NB;   /* base vertices per side */

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
        const int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++)
            if (row[y] == 0) { INVT[x] = y; break; }
    }
}

/* Base structure: perms SG[t][i] (t < d, i < NB), inverses SGI, voltages GV[i][t]. */
static int SG[MAXD][MAXB];
static int SGI[MAXD][MAXB];
static int GV[MAXB][MAXD];

static int dist_[MAXV], seen_[MAXV], q_[MAXV];
static int stamp_ = 0;

/* Number of (source, vertex) pairs at distance > D over sources a_{i,e} and b_{j,e}. */
static long eval_bad(void) {
    int N = NN, BN = NB * N, V = 2 * BN;
    long total = 0;
    for (int s = 0; s < 2 * NB; s++) {
        int src = s < NB ? s * N : BN + (s - NB) * N;
        int head = 0, tail = 0;
        stamp_++;
        seen_[src] = stamp_;
        dist_[src] = 0;
        q_[tail++] = src;
        while (head < tail) {
            int v = q_[head++];
            int dv = dist_[v];
            if (dv >= D) continue;
            if (v < BN) {
                int i = v / N, x = v - i * N;
                const int *row = MTAB + (size_t)x * N;
                for (int t = 0; t < d; t++) {
                    int u = BN + SG[t][i] * N + row[GV[i][t]];
                    if (seen_[u] != stamp_) {
                        seen_[u] = stamp_;
                        dist_[u] = dv + 1;
                        q_[tail++] = u;
                    }
                }
            } else {
                int w = v - BN;
                int j = w / N, y = w - j * N;
                const int *row = MTAB + (size_t)y * N;
                for (int t = 0; t < d; t++) {
                    int i = SGI[t][j];
                    int u = i * N + row[INVT[GV[i][t]]];
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

/* Pairs (SG[s][i], GV[i][s]) for s < t must differ from the pair for t. */
static int pair_ok_upto(int i, int t) {
    for (int s = 0; s < t; s++)
        if (SG[s][i] == SG[t][i] && GV[i][s] == GV[i][t]) return 0;
    return 1;
}

static int pair_ok(int i) {
    for (int t = 1; t < d; t++)
        if (!pair_ok_upto(i, t)) return 0;
    return 1;
}

static void swap_perm(int t, int i1, int i2) {
    int tmp = SG[t][i1];
    SG[t][i1] = SG[t][i2];
    SG[t][i2] = tmp;
    SGI[t][SG[t][i1]] = i1;
    SGI[t][SG[t][i2]] = i2;
}

/* Fresh random perms (t >= 1) and voltages; s_0 = identity and g_{i,0} = identity. */
static void init_state(void) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < NB; i++) SG[t][i] = i;
        if (t > 0) {
            for (int i = NB - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int tmp = SG[t][i];
                SG[t][i] = SG[t][j];
                SG[t][j] = tmp;
            }
        }
        for (int i = 0; i < NB; i++) SGI[t][SG[t][i]] = i;
    }
    for (int i = 0; i < NB; i++) {
        GV[i][0] = 0;
        for (int t = 1; t < d; t++) {
            int tries = 0;
            do {
                GV[i][t] = rndint(NN);
                tries++;
            } while (!pair_ok_upto(i, t) && tries < 100000);
        }
    }
}

/* Annealed hill-climb on voltages and base permutations. */
static long climb(double until, double T0, int steps) {
    long bad = eval_bad();
    double T = T0;
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        if (NB > 1 && rndint(5) == 0) {
            int t = 1 + rndint(d - 1);
            int i1 = rndint(NB), i2 = rndint(NB - 1);
            if (i2 >= i1) i2++;
            swap_perm(t, i1, i2);
            if (!pair_ok(i1) || !pair_ok(i2)) {
                swap_perm(t, i1, i2);
                continue;
            }
            long nb = eval_bad();
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
            else swap_perm(t, i1, i2);
        } else {
            int i = rndint(NB), t = 1 + rndint(d - 1);
            int old = GV[i][t];
            int nv = rndint(NN);
            if (nv == old) continue;
            GV[i][t] = nv;
            if (!pair_ok(i)) {
                GV[i][t] = old;
                continue;
            }
            long nb = eval_bad();
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
            else GV[i][t] = old;
        }
        T *= 0.9995;
        if (T < 0.2) T = 0.2;
    }
    return bad;
}

/* Range of group orders N giving total order 2*B*N > thresh and <= Moore bound. */
static int nrange(int B, int thresh, long moore, int *lo, int *hi) {
    long L = thresh / (2L * B) + 1;
    if (L < d + 1) L = d + 1;
    long H = moore / (2L * B);
    if (H > MAXN) H = MAXN;
    long cap = MAXV / (2L * B);
    if (H > cap) H = cap;
    if (L > H) return 0;
    *lo = (int)L;
    *hi = (int)H;
    return 1;
}

static int OU[MAXV / 2 * MAXD], OV[MAXV / 2 * MAXD];
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

    int found = 0, fOrder = 0, ne = 0;

    if (d >= 3 && d <= MAXD && D >= 2) {
        long moore = moore_bound();
        int thresh = sn;
        static Grp cand[MAXCAND];

        while (now() < t_end) {
            int fB[BMAX], flo[BMAX], fhi[BMAX], nf = 0;
            for (int B = 1; B <= BMAX; B++) {
                int lo, hi;
                if (nrange(B, thresh, moore, &lo, &hi)) {
                    fB[nf] = B; flo[nf] = lo; fhi[nf] = hi; nf++;
                }
            }
            if (nf == 0) break;
            int pick = rndint(nf);
            int B = fB[pick], lo = flo[pick], hi = fhi[pick];
            int span = hi - lo + 1;
            if (span > SPAN) span = SPAN;
            int N = lo + rndint(span);

            int cnt = enum_groups(N, cand);
            if (cnt <= 0) continue;
            Grp G = pick_group(cand, cnt);
            setup_group(N, G);
            NB = B;

            int steps = STEPS / B;
            if (steps < 1500) steps = 1500;
            long bad = 1;
            for (int rs = 0; rs < RESTARTS && bad > 0 && now() < t_end; rs++) {
                init_state();
                bad = climb(t_end, rs == 0 ? 2.0 : 1.0, steps);
            }
            if (bad == 0) {
                int BN = B * N;
                ne = 0;
                for (int i = 0; i < B; i++)
                    for (int x = 0; x < N; x++)
                        for (int t = 0; t < d; t++) {
                            OU[ne] = i * N + x;
                            OV[ne] = BN + SG[t][i] * N + MTAB[(size_t)x * N + GV[i][t]];
                            ne++;
                        }
                found = 1;
                fOrder = 2 * BN;
                thresh = fOrder;
            }
        }
    }

    if (found) {
        printf("%d %d\n", fOrder, ne);
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
