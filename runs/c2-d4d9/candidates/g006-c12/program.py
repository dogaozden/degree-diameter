"""Bipartite Haar-graph search over groups (a Cayley-type engine that replaces the voltage-lift search).

A Haar graph of a group G with connection set S = {s_1..s_d} has vertices (0,g) and (1,g), g in G,
and edges (0,g)-(1,g*s_i). Left multiplication is an automorphism that is transitive on each side,
so the diameter check needs only two BFS runs, from (0,e) and (1,e). The C engine:
  * draws groups from semidirect products Z_m x| Z_k (uniform over (m,k,r)) and from matrix groups
    PSL/SL/PGL(2,q) for small q, with order just above the current frontier;
  * runs simulated annealing over the d connection elements, minimising the number of unreached
    vertices, with multiplication tables kept for each generator so that a BFS is pure table lookups;
  * climbs the order frontier after each success.
Python supplies algebraic starts, keeps the largest graph that lib.is_valid accepts, and falls back
to the best start if the C search finds nothing.
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

#define MAXG 10240
#define MAXD 32
#define CODEMAX 279900

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
    {5, 0}, {5, 1}, {5, 2}, {7, 0}, {7, 1}, {7, 2}, {8, 0},
    {11, 0}, {11, 1}, {11, 2}, {13, 0}, {13, 1}, {13, 2}, {16, 0},
    {17, 0}, {17, 1}, {17, 2}, {19, 0}, {19, 1}, {19, 2},
    {23, 0}, {23, 1}, {23, 2}
};
#define NMATS ((int)(sizeof(MATS) / sizeof(MATS[0])))

static int MQ, MODE;
static int CODE2IDX[CODEMAX];
static int MAT[MAXG][4];

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

/* Build the matrix group of spec c into the global tables. Returns its order or 0. */
static int mat_build(int c) {
    int q = MATS[c].q, mode = MATS[c].mode;
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
        if (N >= MAXG) return 0;
        CODE2IDX[code] = N;
        MAT[N][0] = m0;
        MAT[N][1] = m1;
        MAT[N][2] = m2;
        MAT[N][3] = m3;
        N++;
    }
    return N == mat_order(c) ? N : 0;
}

static int mat_mul(int x, int y) {
    const int *X = MAT[x], *Y = MAT[y];
    int a = F.add[F.mul[X[0]][Y[0]]][F.mul[X[1]][Y[2]]];
    int b = F.add[F.mul[X[0]][Y[1]]][F.mul[X[1]][Y[3]]];
    int c = F.add[F.mul[X[2]][Y[0]]][F.mul[X[3]][Y[2]]];
    int e = F.add[F.mul[X[2]][Y[1]]][F.mul[X[3]][Y[3]]];
    return CODE2IDX[norm_code(a, b, c, e)];
}

/* Inverse via the adjugate, which equals the inverse up to a scalar (fixed by normalisation). */
static int mat_inv(int x) {
    const int *X = MAT[x];
    return CODE2IDX[norm_code(X[3], F.neg[X[1]], F.neg[X[2]], X[0])];
}

/* ------------------------------------------------------------------ groups */

/* kind 0: Z_m x|_r Z_k, element (a,b) = a*k+b, (a,b)(c,e) = (a + r^b c, b+e); identity 0.
 * kind 1: matrix group loaded in the global tables; e is the identity index. */
typedef struct {
    int kind;
    int N, e;
    int spec, m, k, r;
    int rp[MAXG];
} Grp;

static void set_semidirect(Grp *G, int m, int k, int r) {
    G->kind = 0;
    G->N = m * k;
    G->e = 0;
    G->m = m;
    G->k = k;
    G->r = r;
    G->rp[0] = 1 % m;
    for (int b = 1; b < k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * r % m);
}

static int set_matrix(Grp *G, int c) {
    int N = mat_build(c);
    if (!N) return 0;
    G->kind = 1;
    G->N = N;
    G->spec = c;
    G->e = CODE2IDX[norm_code(1, 0, 0, 1)];
    return 1;
}

static int gmul(const Grp *G, int x, int y) {
    if (G->kind == 1) return mat_mul(x, y);
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    int first = (int)(((long)a + (long)G->rp[b] * c) % G->m);
    return first * G->k + (b + e) % G->k;
}

static int ginv(const Grp *G, int x) {
    if (G->kind == 1) return mat_inv(x);
    int a = x / G->k, b = x % G->k;
    int nb = (G->k - b) % G->k;
    int na = (int)((G->m - ((long)G->rp[nb] * a) % G->m) % G->m);
    return na * G->k + nb;
}

/* Uniformly random semidirect group of order N (reservoir over (m, k, r)). */
static int random_semidirect(int N, Grp *G) {
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
    set_semidirect(G, bm, bk, br);
    return 1;
}

/* ------------------------------------------------------------------ Haar-graph evaluation */

static int S[MAXD];
static int RB[MAXD][2][MAXG];   /* RB[i][b][v] = v * s_i */
static int IB[MAXD][2][MAXG];   /* IB[i][b][v] = v * s_i^{-1} */
static int act[MAXD];
static const int *PR[MAXD], *PI[MAXD];
static int vis[2 * MAXG];
static int vtick = 0;
static int qbuf[2 * MAXG];

static void fill_tables(const Grp *G, int i, int buf, int x) {
    int xi = ginv(G, x);
    int *R = RB[i][buf], *I = IB[i][buf];
    for (int v = 0; v < G->N; v++) {
        R[v] = gmul(G, v, x);
        I[v] = gmul(G, v, xi);
    }
}

/* Haar graph: side 0 vertex g adjacent to side 1 vertex g*s_i. Two BFS runs (from (0,e) and
 * (1,e)) cover all pairs by left-multiplication symmetry. Returns the count of unreached pairs. */
static long eval_tables(int N, int e) {
    long unreached = 0;
    for (int src = 0; src < 2; src++) {
        if (++vtick == 0x7fffffff) {
            memset(vis, 0, sizeof vis);
            vtick = 1;
        }
        int start = (src == 0) ? e : N + e;
        int head = 0, tail = 0;
        vis[start] = vtick;
        qbuf[tail++] = start;
        for (int lvl = 0; lvl < D && head < tail; lvl++) {
            int end = tail;
            for (; head < end; head++) {
                int v = qbuf[head];
                if (v < N) {
                    for (int i = 0; i < d; i++) {
                        int u = N + PR[i][v];
                        if (vis[u] != vtick) { vis[u] = vtick; qbuf[tail++] = u; }
                    }
                } else {
                    int h = v - N;
                    for (int i = 0; i < d; i++) {
                        int u = PI[i][h];
                        if (vis[u] != vtick) { vis[u] = vtick; qbuf[tail++] = u; }
                    }
                }
            }
        }
        unreached += 2L * N - tail;
    }
    return unreached;
}

static int in_set(int x, int cnt) {
    for (int j = 0; j < cnt; j++)
        if (S[j] == x) return 1;
    return 0;
}

/* One annealing run from a random connection set on group G. Returns 1 if S is a valid set. */
static int sa_attempt(const Grp *G, long max_evals, double until) {
    int N = G->N;
    for (int i = 0; i < d; i++) {
        int x;
        do { x = rndint(N); } while (in_set(x, i));
        S[i] = x;
    }
    for (int i = 0; i < d; i++) {
        act[i] = 0;
        fill_tables(G, i, 0, S[i]);
        PR[i] = RB[i][0];
        PI[i] = IB[i][0];
    }
    long cur = eval_tables(N, G->e);
    for (long it = 0; it < max_evals && cur > 0; it++) {
        if (now() > until) return 0;
        int i = rndint(d);
        int x = rndint(N);
        if (in_set(x, d)) continue;
        int nb = 1 - act[i];
        fill_tables(G, i, nb, x);
        const int *oldR = PR[i], *oldI = PI[i];
        PR[i] = RB[i][nb];
        PI[i] = IB[i][nb];
        long nv = eval_tables(N, G->e);
        long df = nv - cur;
        double T = (0.5 + 0.02 * (double)cur) * (1.0 - (double)it / (double)max_evals) + 0.01;
        if (df <= 0 || rnd01() < exp(-(double)df / T)) {
            cur = nv;
            S[i] = x;
            act[i] = nb;
        } else {
            PR[i] = oldR;
            PI[i] = oldI;
        }
    }
    return cur == 0;
}

/* ------------------------------------------------------------------ output */

static int have_best = 0;
static Grp bestG;
static int bestS[MAXD];
static Grp cur;

static void print_best(void) {
    if (!have_best) {
        printf("0 0\n");
        return;
    }
    static Grp G;
    G = bestG;
    if (G.kind == 1 && !set_matrix(&G, G.spec)) {
        printf("0 0\n");
        return;
    }
    int N = G.N;
    printf("%d %ld\n", 2 * N, (long)N * d);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + gmul(&G, g, bestS[i]));
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [start_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long hint = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.94 - 0.3;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    long cap = moore_bound() / 2;
    if (cap > MAXG) cap = MAXG;
    long Nmin = hint / 2 + 1;
    if (cap / 5 > Nmin) Nmin = cap / 5;
    if (Nmin < d) Nmin = d;

    while (now() < t_end && Nmin <= cap) {
        long span = Nmin / 30 + 3;
        int ok = 0;
        if (rnd01() < 0.5) {
            int cand[NMATS], nc = 0, bc = -1;
            long bo = 0;
            for (int c = 0; c < NMATS; c++) {
                long o = mat_order(c);
                if (o < Nmin || o > cap) continue;
                if (o <= 3 * Nmin) cand[nc++] = c;
                if (bc < 0 || o < bo) { bc = c; bo = o; }
            }
            if (nc == 0 && bc >= 0) cand[nc++] = bc;
            if (nc > 0) ok = set_matrix(&cur, cand[rndint(nc)]);
        }
        if (!ok) {
            long N = Nmin + rndint((int)span);
            if (N > cap) N = cap;
            if (N < d) N = d;
            ok = random_semidirect((int)N, &cur);
        }
        if (!ok || cur.N < d || cur.N > cap) continue;

        double slice = 2.0 + cur.N / 800.0;
        double until = now() + slice;
        if (until > t_end) until = t_end;
        int found = 0;
        while (!found && now() < until)
            found = sa_attempt(&cur, 4000, until);
        if (found) {
            have_best = 1;
            bestG = cur;
            memcpy(bestS, S, sizeof(int) * d);
            Nmin = (long)cur.N + 1 + cur.N / 40;
        }
    }
    print_best();
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         stdin_graph=None, timeout=budget + 10)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
