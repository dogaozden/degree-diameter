"""Bold variant for the d=5, D=7 target: bi-Cayley lifts over simple groups PSL(2,p) and PGL(2,p).

The C engine first searches bi-Cayley graphs over PSL(2,p) and PGL(2,p), which are non-abelian
and non-solvable, so they are structurally unlike the cyclic and metabelian lifts used before.
A bi-Cayley graph with connection set {e, g_1..g_{d-1}} is d-regular and bipartite on 2|G|
vertices. Left multiplication is transitive on each side, so exact diameter is checked by BFS
from the two identity vertices only. After that phase, the remaining time goes to the
metabelian semidirect search (Z_m x| Z_k, as in the previous parent), which covers the regime
where the record was found. Each candidate is checked exactly in C and again with lib.is_valid
in Python. The fallback is the best algebraic start (K_{d,d}, PG(2,d-1), or the split Cayley
hexagon H(q)), so every case returns a valid graph.
"""
import time
import itertools

import numpy as np

import lib

C_SOURCE = r'''
/* Bi-Cayley degree-diameter search over PSL(2,p), PGL(2,p) and metabelian groups.
 * Usage:   prog d D seed time_limit min_vertices
 * stdin is ignored. stdout: "n m" and m edges of a valid graph with more than
 * min_vertices vertices, or "0 0" if none was found.
 * Vertices: A-side x (0..N-1), B-side N+y. Edges: x -- N + (x * g_t) for t = 0..d-1,
 * with g_0 = identity and distinct g_t. Degree d, simple, bipartite by construction.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 6000
#define MAXV (2 * MAXN)
#define MAXD 16
#define MAXOUT (MAXD * MAXN)
#define CSTEPS 8000

enum { KIND_SEMI = 0, KIND_PSL = 1, KIND_PGL = 2 };

static int d, D;
static long moore_b;
static double tend;
static long best_nv;
static long out_nv = 0, out_m = 0;
static int out_e[MAXOUT][2];

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

/* ---------------- group representation ---------------- */

static int gkind = KIND_SEMI;
static int GN, gm, gk, gr, gid;
static int gpow[MAXN];
static int gel[MAXN][4];
static int *glut = NULL;
static int gp;

static int md(long x) {
    x %= gp;
    if (x < 0) x += gp;
    return (int)x;
}

static int code4(int a, int b, int c, int e) { return ((a * gp + b) * gp + c) * gp + e; }

static int inv_p(int x) {
    long r = 1, b = x, e = gp - 2;
    b %= gp;
    while (e > 0) {
        if (e & 1) r = r * b % gp;
        b = b * b % gp;
        e >>= 1;
    }
    return (int)r;
}

/* Canonical code of a projective matrix: PSL identifies M with -M, PGL scales the first nonzero entry to 1. */
static int canon_code(int a, int b, int c, int e) {
    if (gkind == KIND_PSL) {
        int c1 = code4(a, b, c, e);
        int c2 = code4(md(-(long)a), md(-(long)b), md(-(long)c), md(-(long)e));
        return c1 < c2 ? c1 : c2;
    }
    int v[4] = {a, b, c, e}, f = 1;
    for (int i = 0; i < 4; i++)
        if (v[i]) { f = v[i]; break; }
    int s = inv_p(f);
    return code4(a * s % gp, b * s % gp, c * s % gp, e * s % gp);
}

static int setup_simple(int kind, int p) {
    free(glut);
    glut = NULL;
    gkind = kind;
    gp = p;
    long P4 = (long)p * p * p * p;
    glut = (int *)malloc(sizeof(int) * (size_t)P4);
    if (!glut) return 0;
    for (long i = 0; i < P4; i++) glut[i] = -1;
    int N = 0;
    for (int a = 0; a < p; a++)
        for (int b = 0; b < p; b++)
            for (int c = 0; c < p; c++)
                for (int e = 0; e < p; e++) {
                    int det = md((long)a * e - (long)b * c);
                    if (kind == KIND_PSL && det != 1) continue;
                    if (kind == KIND_PGL && det == 0) continue;
                    int cc = canon_code(a, b, c, e);
                    if (glut[cc] >= 0) continue;
                    if (N >= MAXN) return 0;
                    glut[cc] = N;
                    int t = cc;
                    gel[N][3] = t % p; t /= p;
                    gel[N][2] = t % p; t /= p;
                    gel[N][1] = t % p; t /= p;
                    gel[N][0] = t;
                    N++;
                }
    GN = N;
    gid = glut[canon_code(1, 0, 0, 1)];
    return N;
}

static void setup_semi(int m, int k, int r) {
    free(glut);
    glut = NULL;
    gkind = KIND_SEMI;
    gm = m; gk = k; gr = r;
    GN = m * k;
    gid = 0;
    gpow[0] = 1 % m;
    for (int b = 1; b < k; b++) gpow[b] = (int)((long)gpow[b - 1] * r % m);
}

/* Uniform admissible semidirect product Z_m x| Z_k of order N (reservoir sampling over (m, r)). */
static int pick_semi(int N, int *pm, int *pk, int *pr) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { *pm = m; *pk = k; *pr = r; }
        }
    }
    return count > 0;
}

static inline int gmul(int x, int y) {
    if (gkind != KIND_SEMI) {
        const int *X = gel[x], *Y = gel[y];
        int a = X[0] * Y[0] + X[1] * Y[2];
        int b = X[0] * Y[1] + X[1] * Y[3];
        int c = X[2] * Y[0] + X[3] * Y[2];
        int e = X[2] * Y[1] + X[3] * Y[3];
        return glut[canon_code(a % gp, b % gp, c % gp, e % gp)];
    }
    int a = x / gk, b = x % gk, c = y / gk, e = y % gk;
    return (int)((a + (long)gpow[b] * c) % gm) * gk + (b + e) % gk;
}

static inline int ginv(int x) {
    if (gkind != KIND_SEMI) {
        const int *X = gel[x];
        return glut[canon_code(X[3], md(-(long)X[1]), md(-(long)X[2]), X[0])];
    }
    int a = x / gk, b = x % gk;
    int nb = (gk - b) % gk;
    return (int)((-(long)gpow[nb] * a % gm + gm) % gm) * gk + nb;
}

/* ---------------- bi-Cayley state ---------------- */

static int gvx[MAXD];
static int permA[MAXD][MAXN], permB[MAXD][MAXN];

static void set_gen(int t) {
    int g = gvx[t], gi = ginv(g);
    for (int x = 0; x < GN; x++) {
        permA[t][x] = gmul(x, g);
        permB[t][x] = gmul(x, gi);
    }
}

static int in_upto(int v, int cnt) {
    for (int i = 0; i < cnt; i++)
        if (gvx[i] == v) return 1;
    return 0;
}

static void random_init(void) {
    gvx[0] = gid;
    for (int t = 1; t < d; t++) {
        int nv;
        do { nv = rndint(GN); } while (nv == gid || in_upto(nv, t));
        gvx[t] = nv;
    }
    for (int t = 0; t < d; t++) set_gen(t);
}

static int seen_s[MAXV], dist_s[MAXV], q_s[MAXV];
static int stamp_s = 0;

/* Number of vertices reached from src within distance D. */
static int bfs_reach(int src) {
    int N = GN, head = 0, tail = 0;
    stamp_s++;
    seen_s[src] = stamp_s;
    dist_s[src] = 0;
    q_s[tail++] = src;
    while (head < tail) {
        int v = q_s[head++], dv = dist_s[v];
        if (dv >= D) continue;
        if (v < N) {
            for (int t = 0; t < d; t++) {
                int u = N + permA[t][v];
                if (seen_s[u] != stamp_s) {
                    seen_s[u] = stamp_s;
                    dist_s[u] = dv + 1;
                    q_s[tail++] = u;
                }
            }
        } else {
            int y = v - N;
            for (int t = 0; t < d; t++) {
                int u = permB[t][y];
                if (seen_s[u] != stamp_s) {
                    seen_s[u] = stamp_s;
                    dist_s[u] = dv + 1;
                    q_s[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* Unreached (source, vertex) pairs for the two orbit representatives. Zero iff diameter <= D. */
static long bad_eval(void) {
    return (2L * GN - bfs_reach(gid)) + (2L * GN - bfs_reach(GN + gid));
}

static void record(void) {
    long nv = 2L * GN;
    if (nv <= best_nv) return;
    best_nv = nv;
    long m = 0;
    for (int t = 0; t < d; t++)
        for (int x = 0; x < GN; x++) {
            out_e[m][0] = x;
            out_e[m][1] = GN + permA[t][x];
            m++;
        }
    out_nv = nv;
    out_m = m;
}

/* Annealed voltage hill-climb; leaves the current state in place, returns its bad count. */
static long climb(double until) {
    long bad = bad_eval();
    double T = 2.0;
    const double alpha = pow(0.1, 1.0 / CSTEPS);
    for (long s = 0; s < CSTEPS && bad > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        int t = 1 + rndint(d - 1);
        int old = gvx[t], nv;
        do { nv = rndint(GN); } while (nv == gid || in_upto(nv, d));
        gvx[t] = nv;
        set_gen(t);
        long nb = bad_eval();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            gvx[t] = old;
            set_gen(t);
        }
        T *= alpha;
        if (T < 0.2) T = 0.2;
    }
    return bad;
}

/* Random restarts in the current group until success or the deadline. */
static int run_until(double until) {
    while (now() < until) {
        random_init();
        if (climb(until) == 0) {
            record();
            return 1;
        }
    }
    return 0;
}

/* Phase A: simple groups PSL(2,p) and PGL(2,p), smallest first, sharing the time slice. */
static void phase_simple(double until) {
    static const int plist[] = {5, 7, 11, 13, 17, 19, 23};
    int kinds[16], ps[16], nc = 0;
    long Ns[16];
    for (int i = 0; i < 7; i++) {
        for (int k = 0; k < 2; k++) {
            long p = plist[i];
            long N = k == 0 ? p * (p * p - 1) / 2 : p * (p * p - 1);
            if (N > MAXN || N < d + 1 || 2 * N > moore_b || nc >= 16) continue;
            kinds[nc] = k == 0 ? KIND_PSL : KIND_PGL;
            ps[nc] = (int)p;
            Ns[nc] = N;
            nc++;
        }
    }
    for (int i = 1; i < nc; i++)
        for (int j = i; j > 0 && Ns[j - 1] > Ns[j]; j--) {
            long tn = Ns[j]; Ns[j] = Ns[j - 1]; Ns[j - 1] = tn;
            int tk = kinds[j]; kinds[j] = kinds[j - 1]; kinds[j - 1] = tk;
            int tp = ps[j]; ps[j] = ps[j - 1]; ps[j - 1] = tp;
        }
    for (int i = 0; i < nc; i++) {
        if (2 * Ns[i] <= best_nv) continue;
        double t = now();
        if (t >= until) break;
        double slice = (until - t) / (double)(nc - i);
        if (!setup_simple(kinds[i], ps[i])) continue;
        run_until(now() + slice);
    }
}

/* Phase B: metabelian groups Z_m x| Z_k, order window just above the incumbent, biased low. */
static void phase_semi(double until) {
    while (now() < until) {
        long lo = best_nv / 2 + 1;
        if (lo < d + 1) lo = d + 1;
        long hi = moore_b / 2;
        if (hi > MAXN) hi = MAXN;
        if (lo > hi) return;
        long span = hi - lo + 1;
        if (span > 200) span = 200;
        double u = rnd01();
        long N = lo + (long)(u * sqrt(u) * (double)span);
        if (N > hi) N = hi;
        int m, k, r;
        if (!pick_semi((int)N, &m, &k, &r)) continue;
        setup_semi(m, k, r);
        for (int a = 0; a < 3 && now() < until; a++) {
            random_init();
            if (climb(until) == 0) {
                record();
                break;
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit min_vertices\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long minv = atol(argv[5]);
    double t0 = now();
    tend = t0 + limit * 0.93 - 0.2;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    best_nv = minv;
    if (d < 3 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    moore_b = moore_bound();
    if (best_nv >= moore_b) {
        printf("0 0\n");
        return 0;
    }
    double L = tend - t0;
    if (L > 0.5) {
        phase_simple(t0 + 0.3 * L);
        phase_semi(tend);
    }
    if (out_m == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%ld %ld\n", out_nv, out_m);
    for (long i = 0; i < out_m; i++)
        printf("%d %d\n", out_e[i][0], out_e[i][1]);
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

    if d > 15 or D < 2 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         stdin_graph=None, timeout=budget + 8)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
