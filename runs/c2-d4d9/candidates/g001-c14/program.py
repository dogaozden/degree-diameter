"""Haar-Cayley search for bipartite degree-diameter graphs.

Construction: pick a finite group G of order N (semidirect products Z_m x| Z_k, or PSL/PGL(2,q)
and SL(2,2^k)) and d distinct generators s_1..s_d. The Haar graph H(G, S) has parts A and B, each a
copy of G, with A_x adjacent to B_{x s} for s in S. G acts regularly on each part by left
multiplication, so the diameter is the larger eccentricity of A_e and B_e. Checking it takes two
BFS passes. Simulated annealing over S minimises the number of vertices beyond distance D. The
search climbs through group orders, so each success gives a larger graph with 2N vertices.

Python builds the algebraic starts (PG(2,q), W(q), Araujo-Pardo-Lopez, K_{d,d}) and keeps the
largest one that lib.is_valid accepts. The C engine's graph replaces it only if it is larger and
valid.
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

#define MAXD 32
#define NMAX 4200
#define NVMAX (2 * NMAX)
#define NCAP 4000
#define SA_STEPS 8000
#define CODEMAX 130400

static int d, D;
static double t_end;

/* ---- group state ---- */
static int MQ, MODE;
static int CODE2IDX[CODEMAX];
static int MAT[NMAX][4];
static int GKIND = 0;          /* 0 = semidirect, 1 = matrix group */
static int GN, GE;
static int SM, SK;
static int RP[NMAX], RPI[NMAX];

/* ---- search state ---- */
static int S[MAXD];
static int NB_A[MAXD][NMAX], NB_B[MAXD][NMAX];
static int BK_A[NMAX], BK_B[NMAX];
static int DIST[NVMAX], QUE[NVMAX];
static int bestHalf = 0, bestM = 0;
static int BU[MAXD * NMAX], BV[MAXD * NMAX];

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

static int gcdi(int a, int b) {
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

/* ---------------- finite fields ---------------- */
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

/* ---------------- matrix groups ---------------- */
static int enc(int a, int b, int c, int e) { return ((a * MQ + b) * MQ + c) * MQ + e; }

/* Canonical code of a matrix up to the group's identification:
 * MODE 0: PSL (M ~ -M), MODE 1: SL (no quotient), MODE 2: PGL (M ~ scalar * M). */
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
        if (N >= NMAX) return 0;
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

static int mat_inv(int x) {
    const int *X = MAT[x];
    return CODE2IDX[norm_code(X[3], F.neg[X[1]], F.neg[X[2]], X[0])];
}

/* ---------------- semidirect products Z_m x| Z_k ---------------- */
/* Element (a,b) has index a*k+b; (a,b)(c,e) = (a + r^b c, b + e). */
static int semidirect_setup(int N) {
    int divs[256], nd = 0;
    for (int m = 1; m <= N; m++)
        if (N % m == 0 && nd < 256) divs[nd++] = m;
    for (int tr = 0; tr < 200; tr++) {
        int m = divs[rndint(nd)];
        int k = N / m;
        int r;
        if (m == 1) {
            r = 0;
        } else if (rnd01() < 0.1) {
            r = 1;
        } else {
            r = 1 + rndint(m - 1);
            if (gcdi(r, m) != 1 || powmod(r, k, m) != 1 % m) continue;
        }
        SM = m;
        SK = k;
        RP[0] = 1 % m;
        for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
        int rinv = 0;
        if (m > 1)
            for (int t = 1; t < m; t++)
                if ((long)r * t % m == 1) { rinv = t; break; }
        RPI[0] = 1 % m;
        for (int b = 1; b < k; b++) RPI[b] = (int)((long)RPI[b - 1] * rinv % m);
        GKIND = 0;
        GN = N;
        GE = 0;
        return 1;
    }
    return 0;
}

static int gmul(int x, int y) {
    if (GKIND == 1) return mat_mul(x, y);
    int a = x / SK, b = x % SK, c = y / SK, e = y % SK;
    int a2 = (int)(((long)a + (long)RP[b] * c) % SM);
    int b2 = (b + e) % SK;
    return a2 * SK + b2;
}

static int ginv(int x) {
    if (GKIND == 1) return mat_inv(x);
    int a = x / SK, b = x % SK;
    int c = (int)(((long)(SM - a) % SM) * RPI[b] % SM);
    int e = (SK - b) % SK;
    return c * SK + e;
}

/* ---------------- Haar graph scoring ---------------- */
/* Vertex A_x = x, B_y = GN + y. Edge A_x - B_{x s_i} for each generator s_i. */
static void fill_perm(int i) {
    int s = S[i];
    int si = ginv(s);
    for (int x = 0; x < GN; x++) {
        NB_A[i][x] = gmul(x, s);
        NB_B[i][x] = gmul(x, si);
    }
}

static int in_prefix(int v, int cnt) {
    for (int j = 0; j < cnt; j++)
        if (S[j] == v) return 1;
    return 0;
}

static int in_all(int v) { return in_prefix(v, d); }

static void random_S(void) {
    for (int i = 0; i < d; i++) {
        int v;
        do v = rndint(GN); while (in_prefix(v, i));
        S[i] = v;
        fill_perm(i);
    }
}

/* BFS from src up to depth D; returns how many vertices lie within distance D. */
static int reach_within(int src) {
    int V = 2 * GN;
    for (int v = 0; v < V; v++) DIST[v] = -1;
    int head = 0, tail = 0;
    DIST[src] = 0;
    QUE[tail++] = src;
    while (head < tail) {
        int v = QUE[head++];
        if (DIST[v] >= D) continue;
        int nd1 = DIST[v] + 1;
        if (v < GN) {
            for (int i = 0; i < d; i++) {
                int u = GN + NB_A[i][v];
                if (DIST[u] < 0) { DIST[u] = nd1; QUE[tail++] = u; }
            }
        } else {
            int y = v - GN;
            for (int i = 0; i < d; i++) {
                int u = NB_B[i][y];
                if (DIST[u] < 0) { DIST[u] = nd1; QUE[tail++] = u; }
            }
        }
    }
    return tail;
}

/* Zero iff the Haar graph has diameter <= D (G is transitive on each part). */
static int score(void) {
    int V = 2 * GN;
    return (V - reach_within(GE)) + (V - reach_within(GN + GE));
}

static void save_best(void) {
    bestHalf = GN;
    bestM = 0;
    for (int i = 0; i < d; i++)
        for (int x = 0; x < GN; x++) {
            BU[bestM] = x;
            BV[bestM] = GN + NB_A[i][x];
            bestM++;
        }
}

/* Simulated annealing over the generator set for the current group. */
static int attempt(double until) {
    int N = GN;
    while (now() < until) {
        random_S();
        int f = score();
        double T0 = 0.3 + 2.0 * rnd01();
        for (int st = 0; st < SA_STEPS && f > 0; st++) {
            if ((st & 127) == 0 && now() > until) return 0;
            double T = T0 * (1.0 - (double)st / SA_STEPS) + 0.05;
            int i = rndint(d);
            int old = S[i], nw;
            do nw = rndint(N); while (in_all(nw));
            memcpy(BK_A, NB_A[i], sizeof(int) * N);
            memcpy(BK_B, NB_B[i], sizeof(int) * N);
            S[i] = nw;
            fill_perm(i);
            int f2 = score();
            int df = f2 - f;
            if (df <= 0 || rnd01() < exp(-(double)df / T)) {
                f = f2;
            } else {
                S[i] = old;
                memcpy(NB_A[i], BK_A, sizeof(int) * N);
                memcpy(NB_B[i], BK_B, sizeof(int) * N);
            }
        }
        if (f == 0) {
            save_best();
            return 1;
        }
    }
    return 0;
}

static const int MQS[12] = {5, 5, 7, 7, 8, 11, 11, 13, 13, 16, 17, 19};
static const int MMODE[12] = {0, 2, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0};
static const int MORD[12] = {60, 120, 168, 336, 504, 660, 1320, 1092, 2184, 4080, 2448, 3420};

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.93;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }

    while (1) {
        double remaining = t_end - now();
        if (remaining < 0.3) break;
        int lo = bestHalf + 1;
        if (lo < d + 1) lo = d + 1;
        if (lo > NCAP) break;
        int span = bestHalf / 6 + 20;
        int ok = 0;
        if (rnd01() < 0.4) {
            int cand[12], nc = 0;
            for (int c = 0; c < 12; c++)
                if (MORD[c] >= lo && MORD[c] <= lo + 2 * span + 100 && MORD[c] <= NCAP)
                    cand[nc++] = c;
            if (nc > 0) {
                int c = cand[rndint(nc)];
                int n2 = matrix_group_build(MQS[c], MMODE[c]);
                if (n2 > 0) {
                    GKIND = 1;
                    GN = n2;
                    GE = CODE2IDX[norm_code(1, 0, 0, 1)];
                    ok = 1;
                }
            }
        }
        if (!ok) {
            int N = lo + rndint(span);
            if (N > NCAP) N = NCAP;
            if (!semidirect_setup(N)) continue;
        }
        if (GN < d + 1) continue;
        double slice = remaining * 0.08;
        if (slice < 1.0) slice = 1.0;
        if (slice > remaining) slice = remaining;
        attempt(now() + slice);
    }

    if (bestHalf == 0) {
        printf("%d %d\n", 2 * d, d * d);
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++)
                printf("%d %d\n", a, d + b);
    } else {
        printf("%d %d\n", 2 * bestHalf, bestM);
        for (int k = 0; k < bestM; k++)
            printf("%d %d\n", BU[k], BV[k]);
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
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

    if d > 31 or D < 2 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.5
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=None, timeout=budget + 8)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
