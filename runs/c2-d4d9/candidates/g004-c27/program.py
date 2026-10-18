"""Cayley-type bipartite search for degree-diameter graphs.

This version replaces voltage lifts over several base vertices with Haar graphs of a single group.
For a group G of order N and connection set S = {s_1, ..., s_d}, the Haar graph has left vertices
x and right vertices y, with x adjacent to y exactly when y = x*s_i for some i. Left
multiplication is an automorphism that is transitive on each side, so the diameter test needs only
two BFS runs, one from the identity on each side. The connection set is searched by simulated
annealing, with s_1 = identity fixed. This is valid because right-translating S by t^{-1} gives an
isomorphic graph.

Groups are drawn from two families:
  * matrix groups PSL/SL/PGL(2, q) for small q (built from the explicit field tables), and
  * random metacyclic groups Z_m x|_r Z_k.

The C engine takes the start graph's order as an argument. It searches for a valid Haar graph
with more vertices than that order, and otherwise echoes the start graph back. Python verifies
every result with lib.is_valid and keeps a valid fallback.
"""
import itertools
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 16384
#define MAXD 32
#define CODEMAX 130321
#define EMAX 300000

static int d, D;
static double t_end;

/* ------------------------------------------------------------------ utilities */

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

/* Largest possible order of a bipartite graph with max degree d and diameter D. */
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

/* ------------------------------------------------------------------ finite fields */

typedef struct {
    int q;
    int add[32][32], mul[32][32], neg[32], inv[32];
} Field;
static Field F;

static int gf2mul(int a, int b, int k, int poly) {
    int r = 0;
    for (int i = 0; i < k; i++)
        if ((b >> i) & 1) r ^= a << i;
    for (int i = 2 * k - 2; i >= k; i--)
        if ((r >> i) & 1) r ^= poly << (i - k);
    return r;
}

static void field_init(int q) {
    memset(&F, 0, sizeof F);
    F.q = q;
    if (q == 8 || q == 16) {
        int k = (q == 8) ? 3 : 4;
        int poly = (q == 8) ? 0xB : 0x13;
        for (int i = 0; i < q; i++)
            for (int j = 0; j < q; j++) {
                F.add[i][j] = i ^ j;
                F.mul[i][j] = gf2mul(i, j, k, poly);
            }
        for (int i = 0; i < q; i++) F.neg[i] = i;
    } else {
        for (int i = 0; i < q; i++)
            for (int j = 0; j < q; j++) {
                F.add[i][j] = (i + j) % q;
                F.mul[i][j] = (i * j) % q;
            }
        for (int i = 0; i < q; i++) F.neg[i] = (q - i) % q;
    }
    for (int i = 1; i < q; i++)
        for (int j = 1; j < q; j++)
            if (F.mul[i][j] == 1) F.inv[i] = j;
}

/* ------------------------------------------------------------------ matrix groups */

typedef struct { int q, mode; } MatSpec; /* mode 0 PSL, 1 SL, 2 PGL */
static const MatSpec MATS[] = {
    {5, 0}, {5, 2}, {5, 1}, {7, 0}, {7, 2}, {7, 1}, {8, 0},
    {11, 0}, {11, 2}, {11, 1}, {13, 0}, {13, 2}, {13, 1}, {16, 0},
    {17, 0}, {17, 2}, {17, 1}, {19, 0}, {19, 2}, {19, 1}
};
#define NMATS ((int)(sizeof(MATS) / sizeof(MATS[0])))

static int MQ, MODE;
static int CODE2IDX[CODEMAX];
static int MAT[MAXN][4];
static int mat_loaded = -1;

static int mat_order(int c) {
    int q = MATS[c].q, mode = MATS[c].mode;
    int o = q * (q * q - 1);
    if (mode == 0 && (q & 1)) o /= 2;
    return o;
}

static int enc(int a, int b, int c, int e) { return ((a * MQ + b) * MQ + c) * MQ + e; }

static int norm_code(int a, int b, int c, int e) {
    if (MODE == 2) {
        int f = a ? a : (b ? b : (c ? c : e));
        int iv = F.inv[f];
        a = F.mul[a][iv];
        b = F.mul[b][iv];
        c = F.mul[c][iv];
        e = F.mul[e][iv];
        return enc(a, b, c, e);
    }
    int c1 = enc(a, b, c, e);
    if (MODE == 0) {
        int c2 = enc(F.neg[a], F.neg[b], F.neg[c], F.neg[e]);
        if (c2 < c1) c1 = c2;
    }
    return c1;
}

static int matrix_group_build(int q, int mode) {
    MQ = q;
    MODE = mode;
    field_init(q);
    int Q4 = q * q * q * q;
    if (Q4 > CODEMAX) return 0;
    for (int i = 0; i < Q4; i++) CODE2IDX[i] = -1;
    int N = 0;
    for (int code = 0; code < Q4; code++) {
        int m3 = code % q;
        int m2 = (code / q) % q;
        int m1 = (code / (q * q)) % q;
        int m0 = code / (q * q * q);
        int det = F.add[F.mul[m0][m3]][F.neg[F.mul[m1][m2]]];
        if (mode == 2) {
            if (det == 0) continue;
        } else if (det != 1) {
            continue;
        }
        if (norm_code(m0, m1, m2, m3) != code) continue;
        if (N >= MAXN) return 0;
        CODE2IDX[code] = N;
        MAT[N][0] = m0;
        MAT[N][1] = m1;
        MAT[N][2] = m2;
        MAT[N][3] = m3;
        N++;
    }
    return N;
}

static int mat_mul(int x, int y) {
    const int *X = MAT[x], *Y = MAT[y];
    int a = F.add[F.mul[X[0]][Y[0]]][F.mul[X[1]][Y[2]]];
    int b = F.add[F.mul[X[0]][Y[1]]][F.mul[X[1]][Y[3]]];
    int c = F.add[F.mul[X[2]][Y[0]]][F.mul[X[3]][Y[2]]];
    int e = F.add[F.mul[X[2]][Y[1]]][F.mul[X[3]][Y[3]]];
    return CODE2IDX[norm_code(a, b, c, e)];
}

static int load_matrix(int c) {
    if (mat_loaded == c) return 1;
    mat_loaded = -1;
    int n = matrix_group_build(MATS[c].q, MATS[c].mode);
    if (n != mat_order(c)) return 0;
    mat_loaded = c;
    return 1;
}

/* ------------------------------------------------------------------ groups */

/* kind 0: Z_m x|_r Z_k with element (a,b) coded a*k+b, (a,b)(c,e) = (a + r^b c, b+e).
 * kind 1: matrix group loaded into the global tables (index c), identity index e. */
typedef struct { int kind, N, e, c, m, k, r; } Grp;
static int RP[MAXN];

static void set_rp(const Grp *G) {
    if (G->kind != 0) return;
    int m = G->m, k = G->k;
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * G->r % m);
}

static int gmul(const Grp *G, int x, int y) {
    if (G->kind == 1) return mat_mul(x, y);
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)(((long)a + (long)RP[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Uniformly random metacyclic group of order N (reservoir over (m, k, r)). */
static int random_group(int N, Grp *G) {
    long count = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (!count) return 0;
    memset(G, 0, sizeof *G);
    G->kind = 0;
    G->N = N;
    G->e = 0;
    G->m = bm;
    G->k = bk;
    G->r = br;
    set_rp(G);
    return 1;
}

/* ------------------------------------------------------------------ Haar graph search */

static int S[MAXD];
static int PERM[MAXD][MAXN], BACK[MAXD][MAXN];
static int TP[MAXN], TB[MAXN];
static int BST[2 * MAXN], BQ[2 * MAXN];
static int btick = 0;

/* Haar graph: left x (index x) ~ right N + x*s_i. PERM[i][x] = x*s_i, BACK[i][y] = y*s_i^-1. */
static void set_gen(const Grp *G, int i, int s) {
    int N = G->N;
    S[i] = s;
    for (int x = 0; x < N; x++) PERM[i][x] = gmul(G, x, s);
    for (int x = 0; x < N; x++) BACK[i][PERM[i][x]] = x;
}

static int in_S(int x, int k) {
    for (int j = 0; j < k; j++)
        if (S[j] == x) return 1;
    return 0;
}

/* Number of vertices within distance D of src. */
static int ball_count(int src, int N) {
    if (++btick == 0x7fffffff) {
        memset(BST, 0, sizeof BST);
        btick = 1;
    }
    int head = 0, tail = 0;
    BST[src] = btick;
    BQ[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = BQ[head];
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int u = N + PERM[i][v];
                    if (BST[u] != btick) { BST[u] = btick; BQ[tail++] = u; }
                }
            } else {
                int y = v - N;
                for (int i = 0; i < d; i++) {
                    int u = BACK[i][y];
                    if (BST[u] != btick) { BST[u] = btick; BQ[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Zero iff the Haar graph has diameter <= D. Left multiplication is transitive on each side,
 * so the identity on each side is a sufficient representative. */
static long sym_bad(int N, int e) {
    return (long)(2 * N - ball_count(e, N)) + (long)(2 * N - ball_count(N + e, N));
}

/* Simulated annealing over S (with S[0] = identity fixed). Returns 1 with S valid, 0 on timeout. */
static int haar_search(const Grp *G, double until, int chunk) {
    int N = G->N;
    if (N < d + 2) return 0;
    while (now() < until) {
        set_gen(G, 0, G->e);
        for (int i = 1; i < d; i++) {
            int x;
            do { x = rndint(N); } while (in_S(x, i));
            set_gen(G, i, x);
        }
        long bad = sym_bad(N, G->e);
        if (bad == 0) return 1;
        double T0 = (0.02 * N + 1.0) * (0.5 + 1.5 * rnd01());
        for (int s = 0; s < chunk && bad > 0; s++) {
            if ((s & 31) == 0 && now() > until) return 0;
            double T = T0 * pow(0.3 / T0, (double)s / chunk);
            int i = 1 + rndint(d - 1);
            int x;
            do { x = rndint(N); } while (in_S(x, d));
            int old = S[i];
            memcpy(TP, PERM[i], sizeof(int) * (size_t)N);
            memcpy(TB, BACK[i], sizeof(int) * (size_t)N);
            set_gen(G, i, x);
            long nb = sym_bad(N, G->e);
            long df = nb - bad;
            if (df <= 0 || rnd01() < exp(-(double)df / T)) {
                bad = nb;
            } else {
                memcpy(PERM[i], TP, sizeof(int) * (size_t)N);
                memcpy(BACK[i], TB, sizeof(int) * (size_t)N);
                S[i] = old;
            }
        }
        if (bad == 0) return 1;
    }
    return 0;
}

typedef struct { Grp G; int S[MAXD]; } Spec;

static void print_spec(const Spec *sp) {
    Grp G = sp->G;
    if (G.kind == 1) {
        if (!load_matrix(G.c)) { printf("0 0\n"); return; }
    } else {
        set_rp(&G);
    }
    int N = G.N;
    printf("%d %ld\n", 2 * N, (long)N * d);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, N + gmul(&G, x, sp->S[i]));
}

/* ------------------------------------------------------------------ main */

static int SU[EMAX], SV[EMAX];
static int SN = 0, SM = 0;

static void print_start(void) {
    printf("%d %d\n", SN, SM);
    for (int e = 0; e < SM; e++) printf("%d %d\n", SU[e], SV[e]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [start_n] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long start_n = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.3;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (scanf("%d %d", &SN, &SM) != 2 || SN < 0 || SM < 0 || SM > EMAX) {
        SN = 0;
        SM = 0;
    } else {
        for (int e = 0; e < SM; e++) {
            if (scanf("%d %d", &SU[e], &SV[e]) != 2) { SN = 0; SM = 0; break; }
        }
    }

    if (d < 2 || d > MAXD || D < 2) {
        print_start();
        return 0;
    }

    long cap = moore_bound();
    if (cap > MAXN) cap = MAXN;
    long best_n = start_n;
    int have = 0;
    static Spec bestsp;

    while (now() < t_end) {
        long lo = best_n / 2 + 1;
        if (lo < d + 2) lo = d + 2;
        if (2 * lo > cap) break;

        Grp G;
        memset(&G, 0, sizeof G);
        int ok = 0;
        if (rnd01() < 0.5) {
            int cc[NMATS], nc = 0;
            for (int c = 0; c < NMATS; c++) {
                long ord = mat_order(c);
                if (ord >= lo && 2 * ord <= cap) cc[nc++] = c;
            }
            if (nc > 0) {
                int pick;
                if (rnd01() < 0.5) {
                    pick = 0;
                    for (int k = 1; k < nc; k++)
                        if (mat_order(cc[k]) < mat_order(cc[pick])) pick = k;
                } else {
                    pick = rndint(nc);
                }
                int c = cc[pick];
                if (load_matrix(c)) {
                    G.kind = 1;
                    G.c = c;
                    G.N = mat_order(c);
                    G.e = CODE2IDX[norm_code(1, 0, 0, 1)];
                    ok = 1;
                }
            }
        }
        if (!ok) {
            long span = lo / 6 + 2;
            long Nl = lo + rndint((int)span);
            if (2 * Nl > cap) Nl = cap / 2;
            if (Nl < d + 2 || 2 * Nl <= best_n) continue;
            if (!random_group((int)Nl, &G)) continue;
        }
        if (2L * G.N <= best_n || 2L * G.N > cap) continue;

        double until = now() + 5.0;
        if (until > t_end) until = t_end;
        if (haar_search(&G, until, 8000)) {
            best_n = 2L * G.N;
            bestsp.G = G;
            memcpy(bestsp.S, S, sizeof(int) * (size_t)d);
            have = 1;
        }
    }

    if (have) print_spec(&bestsp);
    else print_start();
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _try(fn, *args):
    try:
        return fn(*args)
    except Exception:
        return None


def known_starts(d, D):
    """Algebraic candidate graphs (filtered by lib.is_valid by the caller)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(_try(lib.projective_plane_incidence, d - 1))
    if D >= 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(_try(lib.araujo_lopez_graph, d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_try(_gq_w, q))
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.88 * time_limit - (time.monotonic() - t0) - 4.0
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         stdin_graph=best, timeout=budget + 10)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
