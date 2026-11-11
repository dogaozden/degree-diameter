"""Multi-orbit bi-Cayley lift search for the weakest cases (d = 5, D = 7 is the target).

Construction: pick a group G of order N (a semidirect product Z_m x|_r Z_k). The graph has P orbits
per side, A_i = {a_{i,x}} and B_j = {b_{j,y}} for x, y in G, with 1 <= P <= 2. Darts from A_i to B_j
are a_{i,x} -- b_{j, x*g} for voltages g in a set S_ij. The dart-count matrix c_ij is fixed by the
degree condition: row and column sums equal d. For P = 2, c = [[a, d-a], [d-a, a]] with 1 <= a <= d-1.
A single orbit per side (P = 1) is the classic bi-Cayley lift.

Left multiplication by G is an automorphism, transitive on each orbit. So diameter <= D holds iff a BFS
from each orbit representative a_{i,e} and b_{j,e} reaches every vertex within D steps. The C engine
hill-climbs the voltages (distinct within each S_ij) to zero bad pairs, and tries both P = 1 and P = 2
at each sampled order. A P = 2 lift on N groups has 4N vertices, which gives a finer grid of total orders
than P = 1 (2N vertices).

The start graph (the H(q) hexagon incidence graph, or an algebraic graph) is the fallback. build() keeps
the largest graph that passes lib.is_valid.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-orbit bi-Cayley lift search over semidirect groups Z_m x|_r Z_k.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0".
 * stdout:  the best valid graph found (lift if it beats the start, else the start).
 *
 * Vertices: A_{i,x} = i*N + x (side 0, i < P), B_{j,y} = P*N + j*N + y (side 1, j < P).
 * Edges:    A_{i,x} -- B_{j, x*g} for each voltage g in S_ij, |S_ij| = cm[i][j],
 *           with the voltages in each S_ij distinct and row/column sums of cm equal to d.
 * Left multiplication by G is an automorphism transitive on each orbit, so diameter <= D is
 * equivalent to BFS from each representative A_{i,e} and B_{j,e} reaching everything within D.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXH 2048
#define MAXD 16
#define MAXE 40000
#define MAXCAND 512
#define STEPS 6000
#define SPAN 30
#define RESTARTS 3
#define MAXOUT (4 * MAXH * MAXD)

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

/* Largest possible total order (both sides) of a bipartite graph with max degree d, diameter D. */
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

/* Multiplication table and inverses for the current group. */
static int MTAB[MAXH * MAXH];
static int INVT[MAXH];
static int RP[MAXH];
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
        const int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++)
            if (row[y] == 0) { INVT[x] = y; break; }
    }
}

/* Base structure: P orbits per side, dart counts cm[i][j], voltages vol[i][j][s]. */
static int P;
static int cm[2][2];
static int vol[2][2][MAXD];
static int pl_i[4], pl_j[4], npair;

static void set_base(int Porb, int a) {
    P = Porb;
    memset(cm, 0, sizeof cm);
    if (P == 1) {
        cm[0][0] = d;
    } else {
        cm[0][0] = a;
        cm[0][1] = d - a;
        cm[1][0] = d - a;
        cm[1][1] = a;
    }
    npair = 0;
    for (int i = 0; i < P; i++)
        for (int j = 0; j < P; j++)
            if (cm[i][j] > 0) {
                pl_i[npair] = i;
                pl_j[npair] = j;
                npair++;
            }
}

/* True if v is among the first cnt voltages of S_ij. */
static int in_prefix(int i, int j, int cnt, int v) {
    for (int s = 0; s < cnt; s++)
        if (vol[i][j][s] == v) return 1;
    return 0;
}

static void init_voltages(void) {
    for (int p = 0; p < npair; p++) {
        int i = pl_i[p], j = pl_j[p];
        for (int s = 0; s < cm[i][j]; s++) {
            int v;
            do { v = rndint(NN); } while (in_prefix(i, j, s, v));
            vol[i][j][s] = v;
        }
    }
}

static int BFS_dist[4 * MAXH], BFS_seen[4 * MAXH], BFS_q[4 * MAXH];
static int stamp_ = 0;

/* Number of (representative, vertex) pairs at distance > D. Representatives: A_{i,e}, B_{j,e}. */
static long eval_bad(void) {
    int N = NN;
    int PN = P * N;
    int V = 2 * PN;
    int srcs[4], ns = 0;
    for (int i = 0; i < P; i++) srcs[ns++] = i * N;
    for (int j = 0; j < P; j++) srcs[ns++] = PN + j * N;
    long total = 0;
    for (int si = 0; si < ns; si++) {
        int src = srcs[si];
        int head = 0, tail = 0;
        stamp_++;
        BFS_seen[src] = stamp_;
        BFS_dist[src] = 0;
        BFS_q[tail++] = src;
        while (head < tail) {
            int v = BFS_q[head++];
            int dv = BFS_dist[v];
            if (dv >= D) continue;
            if (v < PN) {
                int i = v / N, x = v % N;
                const int *row = MTAB + (size_t)x * N;
                for (int j = 0; j < P; j++) {
                    int base = PN + j * N;
                    for (int s = 0; s < cm[i][j]; s++) {
                        int u = base + row[vol[i][j][s]];
                        if (BFS_seen[u] != stamp_) {
                            BFS_seen[u] = stamp_;
                            BFS_dist[u] = dv + 1;
                            BFS_q[tail++] = u;
                        }
                    }
                }
            } else {
                int w = v - PN;
                int j = w / N, y = w % N;
                const int *row = MTAB + (size_t)y * N;
                for (int i = 0; i < P; i++) {
                    for (int s = 0; s < cm[i][j]; s++) {
                        int u = i * N + row[INVT[vol[i][j][s]]];
                        if (BFS_seen[u] != stamp_) {
                            BFS_seen[u] = stamp_;
                            BFS_dist[u] = dv + 1;
                            BFS_q[tail++] = u;
                        }
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

/* Annealed voltage hill-climb. Each step replaces one voltage by a new value unused in its S_ij. */
static long climb(double until, double T0) {
    long bad = eval_bad();
    double T = T0;
    for (long s = 0; s < STEPS && bad > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        int p = rndint(npair);
        int i = pl_i[p], j = pl_j[p];
        int idx = rndint(cm[i][j]);
        int old = vol[i][j][idx], nv;
        do { nv = rndint(NN); } while (in_prefix(i, j, cm[i][j], nv));
        vol[i][j][idx] = nv;
        long nb = eval_bad();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else vol[i][j][idx] = old;
        T *= 0.9995;
        if (T < 0.2) T = 0.2;
    }
    return bad;
}

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

    static int SU[MAXE], SV[MAXE];
    int sn = 0, sm = 0;
    if (scanf("%d %d", &sn, &sm) != 2) { sn = 0; sm = 0; }
    if (sn < 0 || sm < 0 || sm > MAXE) { sn = 0; sm = 0; }
    int got = 0;
    for (int e = 0; e < sm; e++) {
        if (scanf("%d %d", &SU[e], &SV[e]) != 2) break;
        got++;
    }
    if (got != sm) { sn = 0; sm = 0; }

    static int OU[MAXOUT], OV[MAXOUT];
    int found = 0, ne = 0;
    long best_total = sn;

    if (d >= 3 && d <= MAXD && D >= 2) {
        long moore = moore_bound();
        static Grp cand[MAXCAND];

        while (now() < t_end) {
            int Pc = (rnd01() < 0.5) ? 2 : 1;
            long Nlo = best_total / (2L * Pc) + 1;
            if (Nlo < d + 1) Nlo = d + 1;
            long Nmax = moore / (2L * Pc);
            if (Nmax > MAXH) Nmax = MAXH;
            if (Nlo > Nmax) {
                Pc = 3 - Pc;
                Nlo = best_total / (2L * Pc) + 1;
                if (Nlo < d + 1) Nlo = d + 1;
                Nmax = moore / (2L * Pc);
                if (Nmax > MAXH) Nmax = MAXH;
                if (Nlo > Nmax) break;
            }
            long span = Nmax - Nlo + 1;
            if (span > SPAN) span = SPAN;
            int N = (int)(Nlo + rndint((int)span));

            int cnt = enum_groups(N, cand);
            if (cnt <= 0) continue;
            Grp G = pick_group(cand, cnt);
            setup_group(N, G);
            int a = 1 + rndint(d - 1);  /* split for P = 2, 1 <= a <= d-1 */
            set_base(Pc, a);

            long bad = 1;
            for (int rs = 0; rs < RESTARTS && bad > 0 && now() < t_end; rs++) {
                init_voltages();
                bad = climb(t_end, rs == 0 ? 2.0 : 1.0);
            }
            if (bad == 0) {
                found = 1;
                best_total = 2L * P * N;
                ne = 0;
                for (int i = 0; i < P; i++)
                    for (int j = 0; j < P; j++)
                        for (int s = 0; s < cm[i][j]; s++)
                            for (int x = 0; x < N; x++) {
                                OU[ne] = i * N + x;
                                OV[ne] = P * N + j * N + MTAB[(size_t)x * N + vol[i][j][s]];
                                ne++;
                            }
            }
        }
    }

    if (found) {
        printf("%d %d\n", (int)best_total, ne);
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
