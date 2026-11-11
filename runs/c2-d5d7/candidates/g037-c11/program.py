"""Bi-Cayley voltage search with simple-group families, for the d=5, D=7 target.

Bold change: the C engine no longer searches only metabelian groups Z_m x| Z_k. It also
searches the simple groups PSL(2,p) and PGL(2,p), built by explicit matrix arithmetic. Each
bi-Cayley graph has vertices a_x, b_x for x in G, and edges a_x -- b_{x s} for s in S, where
|S| = d and e in S. Left multiplication by G is transitive on each side, so two BFS sources
(a_e and b_e) decide validity. Candidate orders are 2|G| > the incumbent, and the output is
always the largest graph the C engine verified.

Rounds alternate between simple-group candidates (smallest orders favoured) and the old
semidirect window. Each round runs voltage annealing with elite restarts and steepest-descent
polish. The C engine prints only a valid graph (or "0 0"). Python re-checks everything with
lib.is_valid, and the algebraic starts (projective plane, Araujo-Lopez, hexagon, generalized
quadrangle) remain as fallbacks, so every case returns a valid graph.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Bi-Cayley search over semidirect products Z_m x| Z_k and over PSL(2,p) / PGL(2,p).
 * Usage:   prog d D seed time_limit threshold_n
 * Output:  "n m" and m edge lines for the largest valid graph found with n > threshold_n,
 *          or "0 0" if none. Stdin is ignored.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 5000
#define MAXD 32
#define BC_SPAN 200
#define BC_STEPS 6000
#define POLISH_MAX 400
#define ROUND_SLICE 8.0

static int d, D;
static double t_end;
static int best_n = 0;
static int out_ok = 0, out_n = 0, out_m = 0;
static int out_e[MAXG * MAXD][2];

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

/* ---------------- group tables ---------------- */

static uint16_t MT[MAXG * MAXG];
static int INVT[MAXG];
static int GN = 0, IDX = 0;
static int INVP[64];

static int invmod_p(int a, int p) {
    long r = 1, b = a % p, e = p - 2;
    while (e > 0) {
        if (e & 1) r = r * b % p;
        b = b * b % p;
        e >>= 1;
    }
    return (int)r;
}

/* Canonical code of a 2x2 matrix mod p. type 2 (PGL): scale first nonzero entry to 1.
 * type 1 (PSL): smaller code of M and -M. */
static int canon_code(int p, int type, int a, int b, int c, int e) {
    int v[4] = {a, b, c, e};
    if (type == 2) {
        int f = 0;
        for (int i = 0; i < 4; i++) if (v[i]) { f = v[i]; break; }
        int iv = INVP[f];
        for (int i = 0; i < 4; i++) v[i] = v[i] * iv % p;
        return ((v[0] * p + v[1]) * p + v[2]) * p + v[3];
    }
    int w[4];
    for (int i = 0; i < 4; i++) w[i] = (p - v[i]) % p;
    int c1 = ((v[0] * p + v[1]) * p + v[2]) * p + v[3];
    int c2 = ((w[0] * p + w[1]) * p + w[2]) * p + w[3];
    return c1 < c2 ? c1 : c2;
}

/* Build PSL(2,p) (type 1) or PGL(2,p) (type 2) as a multiplication table. */
static int build_simple(int p, int type) {
    int p4 = p * p * p * p;
    int *pidx = malloc(sizeof(int) * (size_t)p4);
    static int EM[MAXG][4];
    if (!pidx) return 0;
    for (int i = 0; i < p4; i++) pidx[i] = -1;
    for (int v = 1; v < p; v++) INVP[v] = invmod_p(v, p);
    int cnt = 0;
    for (int a = 0; a < p; a++)
        for (int b = 0; b < p; b++)
            for (int c = 0; c < p; c++)
                for (int e = 0; e < p; e++) {
                    int det = ((a * e - b * c) % p + p) % p;
                    if (type == 1 ? det != 1 : det == 0) continue;
                    int code = ((a * p + b) * p + c) * p + e;
                    if (canon_code(p, type, a, b, c, e) != code) continue;
                    if (cnt >= MAXG) { free(pidx); return 0; }
                    pidx[code] = cnt;
                    EM[cnt][0] = a; EM[cnt][1] = b; EM[cnt][2] = c; EM[cnt][3] = e;
                    cnt++;
                }
    GN = cnt;
    for (int x = 0; x < GN; x++) {
        int A = EM[x][0], B = EM[x][1], C = EM[x][2], E = EM[x][3];
        for (int y = 0; y < GN; y++) {
            int a2 = EM[y][0], b2 = EM[y][1], c2 = EM[y][2], e2 = EM[y][3];
            int r0 = (A * a2 + B * c2) % p;
            int r1 = (A * b2 + B * e2) % p;
            int r2 = (C * a2 + E * c2) % p;
            int r3 = (C * b2 + E * e2) % p;
            int code = canon_code(p, type, r0, r1, r2, r3);
            MT[(size_t)x * GN + y] = (uint16_t)pidx[code];
        }
    }
    IDX = pidx[canon_code(p, type, 1, 0, 0, 1)];
    free(pidx);
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++)
            if (MT[(size_t)x * GN + y] == IDX) { INVT[x] = y; break; }
    return 1;
}

/* Z_m x| Z_k with element a*k+b and (a,b)(c,e) = (a + r^b c, b + e). Identity is 0. */
static void build_sd(int m, int k, int r) {
    static int rp[MAXG];
    int N = m * k;
    GN = N;
    IDX = 0;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            int val = (int)(((a + (long)rp[b] * c) % m) * k + (b + e) % k);
            MT[(size_t)x * N + y] = (uint16_t)val;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[(size_t)x * N + y] == 0) { INVT[x] = y; break; }
}

/* Uniform random admissible (m, k, r) of order N, by reservoir sampling. */
static int random_sd(int N, int *pm, int *pk, int *pr) {
    long count = 0;
    int bm = 1, bk = N, br = 1;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)(count < 2000000000L ? count : 2000000000L)) == 0) {
                bm = m; bk = k; br = r;
            }
        }
    }
    if (!count) return 0;
    *pm = bm; *pk = bk; *pr = br;
    return 1;
}

/* ---------------- bi-Cayley objective ---------------- */

static int dist_b[2 * MAXG], seen_b[2 * MAXG], q_b[2 * MAXG];
static int stamp_b = 0;

static int used_upto(const int *gv, int cnt, int v) {
    for (int i = 0; i < cnt; i++)
        if (gv[i] == v) return 1;
    return 0;
}

/* Vertices at distance > D from the two sources a_e and b_e (summed). Zero means valid. */
static long eval_bad(const int *gv) {
    int N = GN, V = 2 * N;
    int gi[MAXD];
    for (int t = 0; t < d; t++) gi[t] = INVT[gv[t]];
    long total = 0;
    for (int s = 0; s < 2; s++) {
        int src = s ? N + IDX : IDX;
        int head = 0, tail = 0;
        stamp_b++;
        seen_b[src] = stamp_b;
        dist_b[src] = 0;
        q_b[tail++] = src;
        while (head < tail) {
            int v = q_b[head++];
            int dv = dist_b[v];
            if (dv >= D) continue;
            if (v < N) {
                const uint16_t *row = MT + (size_t)v * N;
                for (int t = 0; t < d; t++) {
                    int u = N + row[gv[t]];
                    if (seen_b[u] != stamp_b) {
                        seen_b[u] = stamp_b;
                        dist_b[u] = dv + 1;
                        q_b[tail++] = u;
                    }
                }
            } else {
                const uint16_t *row = MT + (size_t)(v - N) * N;
                for (int t = 0; t < d; t++) {
                    int u = row[gi[t]];
                    if (seen_b[u] != stamp_b) {
                        seen_b[u] = stamp_b;
                        dist_b[u] = dv + 1;
                        q_b[tail++] = u;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

/* Annealed voltage hill-climb with gv[0] = IDX fixed. Geometric cooling 2.0 -> 0.2. */
static long climb(int *gv, int *bestgv, double until) {
    long bad = eval_bad(gv);
    long bestb = bad;
    memcpy(bestgv, gv, sizeof(int) * d);
    double T = 2.0;
    const double alpha = pow(0.1, 1.0 / BC_STEPS);
    for (long s = 0; s < BC_STEPS && bad > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        int t = 1 + rndint(d - 1);
        int old = gv[t], nv;
        do { nv = rndint(GN); } while (used_upto(gv, d, nv));
        gv[t] = nv;
        long nb = eval_bad(gv);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
            if (bad < bestb) {
                bestb = bad;
                memcpy(bestgv, gv, sizeof(int) * d);
            }
        } else {
            gv[t] = old;
        }
        T *= alpha;
        if (T < 0.2) T = 0.2;
    }
    return bestb;
}

/* Steepest-descent polish over all single-voltage replacements. */
static long polish(int *gv, long bad, double deadline) {
    int N = GN;
    while (bad > 0 && now() < deadline) {
        long bestb = bad;
        int bt = -1, bv = -1;
        for (int t = 1; t < d; t++) {
            int old = gv[t];
            for (int nv = 0; nv < N; nv++) {
                if ((nv & 63) == 0 && now() > deadline) break;
                if (used_upto(gv, d, nv)) continue;
                gv[t] = nv;
                long nb = eval_bad(gv);
                if (nb < bestb) { bestb = nb; bt = t; bv = nv; }
            }
            gv[t] = old;
        }
        if (bt < 0) break;
        gv[bt] = bv;
        bad = bestb;
    }
    return bad;
}

static void store_graph(const int *gv) {
    int N = GN, m = 0;
    for (int x = 0; x < N; x++)
        for (int t = 0; t < d; t++) {
            out_e[m][0] = x;
            out_e[m][1] = N + MT[(size_t)x * N + gv[t]];
            m++;
        }
    out_n = 2 * N;
    out_m = m;
    out_ok = 1;
}

/* Anneal voltage sets over the current group until success or the deadline. */
static int attempt_loop(double until) {
    static int gv[MAXD], bestgv[MAXD], elite[MAXD];
    long elite_bad = -1;
    while (now() < until) {
        if (elite_bad >= 0 && rnd01() < 0.6) {
            memcpy(gv, elite, sizeof(int) * d);
            int t = 1 + rndint(d - 1), nv;
            do { nv = rndint(GN); } while (used_upto(gv, d, nv));
            gv[t] = nv;
        } else {
            gv[0] = IDX;
            for (int t = 1; t < d; t++) {
                int nv;
                do { nv = rndint(GN); } while (used_upto(gv, t, nv));
                gv[t] = nv;
            }
        }
        long b = climb(gv, bestgv, until);
        if (b > 0 && b <= POLISH_MAX) {
            double pd = now() + 2.0;
            if (pd > until) pd = until;
            b = polish(bestgv, b, pd);
        }
        if (b == 0) {
            store_graph(bestgv);
            best_n = out_n;
            return 1;
        }
        if (elite_bad < 0 || b < elite_bad) {
            elite_bad = b;
            memcpy(elite, bestgv, sizeof(int) * d);
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit threshold_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int thr = argc >= 6 ? atoi(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.94 - 0.3;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    best_n = thr;
    if (d < 3 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    const int plist[7] = {5, 7, 11, 13, 17, 19, 23};
    while (now() < t_end) {
        long moore = moore_bound();
        int cand_p[16], cand_t[16], cand_N[16], nc = 0;
        for (int pi = 0; pi < 7; pi++)
            for (int ty = 1; ty <= 2; ty++) {
                long p = plist[pi];
                long N = ty == 1 ? p * (p * p - 1) / 2 : p * (p * p - 1);
                if (N > MAXG || N < d + 1) continue;
                if (2 * N <= best_n || 2 * N > moore) continue;
                cand_p[nc] = (int)p;
                cand_t[nc] = ty;
                cand_N[nc] = (int)N;
                nc++;
            }
        for (int i = 1; i < nc; i++) {
            int j = i;
            while (j > 0 && cand_N[j - 1] > cand_N[j]) {
                int s;
                s = cand_N[j]; cand_N[j] = cand_N[j - 1]; cand_N[j - 1] = s;
                s = cand_p[j]; cand_p[j] = cand_p[j - 1]; cand_p[j - 1] = s;
                s = cand_t[j]; cand_t[j] = cand_t[j - 1]; cand_t[j - 1] = s;
                j--;
            }
        }
        long half = moore / 2;
        int Nmax = (int)(half < MAXG ? half : MAXG);
        int Nlo = best_n / 2 + 1;
        if (Nlo < d + 1) Nlo = d + 1;
        int sd_ok = Nlo <= Nmax;
        if (nc == 0 && !sd_ok) break;
        double remain = t_end - now();
        if (remain < 0.5) break;
        double until = now() + (remain < ROUND_SLICE ? remain : ROUND_SLICE);
        int simple = nc > 0 && (!sd_ok || rnd01() < 0.4);
        if (simple) {
            double u = rnd01();
            int ci = (int)(u * u * nc);
            if (ci >= nc) ci = nc - 1;
            if (!build_simple(cand_p[ci], cand_t[ci])) break;
            attempt_loop(until);
        } else {
            int span = Nmax - Nlo + 1;
            if (span > BC_SPAN) span = BC_SPAN;
            double u = rnd01();
            int N = Nlo + (int)(u * sqrt(u) * span);
            if (N > Nmax) N = Nmax;
            int m = 1, k = N, r = 1;
            int got = random_sd(N, &m, &k, &r);
            for (int tries = 1; got && tries < 8 && !(m > 1 && k > 1 && r != 1); tries++)
                got = random_sd(N, &m, &k, &r);
            if (!got) break;
            build_sd(m, k, r);
            attempt_loop(until);
        }
    }
    if (out_ok) {
        printf("%d %d\n", out_n, out_m);
        for (int i = 0; i < out_m; i++)
            printf("%d %d\n", out_e[i][0], out_e[i][1]);
    } else {
        printf("0 0\n");
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

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 4.0
    if budget < 3.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         stdin_graph=None, timeout=budget + 3.0)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
