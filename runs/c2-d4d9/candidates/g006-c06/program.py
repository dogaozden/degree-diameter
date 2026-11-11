"""Combined bipartite degree-diameter search (voltage lifts over non-abelian groups).

Merges two parents:
  * Multi-base voltage lifts over matrix groups SL/PSL/PGL(2,q) and metacyclic groups
    Z_m x| Z_k. Fibres A(i,x), B(j,y) for i,j < P. A dart (i,j,g) joins A(i,x) to B(j,x*g).
    Left multiplication is an automorphism, so the diameter test needs one BFS per fibre
    representative. Simulated annealing over the voltages minimises the number of unreached pairs.
  * An ascending ladder of candidate orders above a floor, each with a time slice. Every success
    is verified with an explicit bitset diameter check before it is kept.
  * Python algebraic starts (projective plane, generalized quadrangle, Araujo-Pardo-Lopez) as
    fallbacks, and lib.is_valid on every returned graph.
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

#define MAXP 8
#define MAXDEG 16
#define MAXDART (MAXP * MAXDEG)
#define MAXNG 6000
#define MAXV 12000
#define CODEMAX 140000
#define MAXCAND 60000

static int d, D;
static long MOORE;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

/* ------------------------------------------------------------------ finite fields */

static int FQ;
static int FADD[32][32], FMUL[32][32], FNEG[32], FINV[32];

static int gf2mul(int a, int b, int k, int poly) {
    int r = 0;
    for (int i = 0; i < k; i++)
        if ((b >> i) & 1) r ^= a << i;
    for (int i = 2 * k - 2; i >= k; i--)
        if ((r >> i) & 1) r ^= poly << (i - k);
    return r;
}

static void field_init(int q) {
    FQ = q;
    if (q == 8 || q == 16) {
        int k = (q == 8) ? 3 : 4;
        int poly = (q == 8) ? 0xB : 0x13;
        for (int i = 0; i < q; i++)
            for (int j = 0; j < q; j++) {
                FADD[i][j] = i ^ j;
                FMUL[i][j] = gf2mul(i, j, k, poly);
            }
        for (int i = 0; i < q; i++) FNEG[i] = i;
    } else {
        for (int i = 0; i < q; i++)
            for (int j = 0; j < q; j++) {
                FADD[i][j] = (i + j) % q;
                FMUL[i][j] = (i * j) % q;
            }
        for (int i = 0; i < q; i++) FNEG[i] = (q - i) % q;
    }
    for (int i = 0; i < q; i++) FINV[i] = 0;
    for (int i = 1; i < q; i++)
        for (int j = 1; j < q; j++)
            if (FMUL[i][j] == 1) FINV[i] = j;
}

/* ------------------------------------------------------------------ matrix groups */

typedef struct { int q, mode; } MSpec;   /* mode 0 PSL, 1 SL, 2 PGL */
static const MSpec MSPECS[] = {
    {5, 0}, {5, 1}, {5, 2}, {7, 0}, {7, 1}, {7, 2}, {8, 1},
    {11, 0}, {11, 1}, {11, 2}, {13, 0}, {13, 1}, {13, 2}, {16, 1},
    {17, 0}, {17, 1}, {17, 2}, {19, 0}, {19, 1}, {19, 2}
};
#define NMSPEC ((int)(sizeof(MSPECS) / sizeof(MSPECS[0])))

static int MQ, MMODE;
static int CODE2IDX[CODEMAX];
static int MATV[MAXNG][4];

static int mat_order(int q, int mode) {
    int o = q * (q * q - 1);
    if (mode == 0 && (q % 2 == 1)) o /= 2;
    return o;
}

static int enc(int a, int b, int c, int e) { return ((a * MQ + b) * MQ + c) * MQ + e; }

static int norm_code(int a, int b, int c, int e) {
    if (MMODE == 2) {
        int f = a ? a : (b ? b : (c ? c : e));
        int iv = FINV[f];
        a = FMUL[a][iv];
        b = FMUL[b][iv];
        c = FMUL[c][iv];
        e = FMUL[e][iv];
        return enc(a, b, c, e);
    }
    int c1 = enc(a, b, c, e);
    if (MMODE == 0) {
        int c2 = enc(FNEG[a], FNEG[b], FNEG[c], FNEG[e]);
        if (c2 < c1) c1 = c2;
    }
    return c1;
}

static int matrix_build(int q, int mode) {
    MQ = q;
    MMODE = mode;
    field_init(q);
    int Q4 = q * q * q * q;
    if (Q4 > CODEMAX) return 0;
    for (int i = 0; i < Q4; i++) CODE2IDX[i] = -1;
    int n = 0;
    for (int code = 0; code < Q4; code++) {
        int m3 = code % q;
        int m2 = (code / q) % q;
        int m1 = (code / (q * q)) % q;
        int m0 = code / (q * q * q);
        int det = FADD[FMUL[m0][m3]][FNEG[FMUL[m1][m2]]];
        if (mode == 2) {
            if (det == 0) continue;
        } else if (det != 1) {
            continue;
        }
        if (norm_code(m0, m1, m2, m3) != code) continue;
        if (n >= MAXNG) return 0;
        CODE2IDX[code] = n;
        MATV[n][0] = m0;
        MATV[n][1] = m1;
        MATV[n][2] = m2;
        MATV[n][3] = m3;
        n++;
    }
    return n;
}

static int mat_mul(int x, int y) {
    const int *X = MATV[x], *Y = MATV[y];
    int a = FADD[FMUL[X[0]][Y[0]]][FMUL[X[1]][Y[2]]];
    int b = FADD[FMUL[X[0]][Y[1]]][FMUL[X[1]][Y[3]]];
    int c = FADD[FMUL[X[2]][Y[0]]][FMUL[X[3]][Y[2]]];
    int e = FADD[FMUL[X[2]][Y[1]]][FMUL[X[3]][Y[3]]];
    return CODE2IDX[norm_code(a, b, c, e)];
}

/* ------------------------------------------------------------------ current group */

static int CUR_KIND = 0;            /* 0 metacyclic, 1 matrix */
static int GORD = 1, GE = 0;        /* group order and identity index */
static int CM = 1, CK = 1, CR = 1;  /* metacyclic parameters */
static int RP[MAXNG];
static int P = 1, half = 1;         /* base size and fibre offset */

static int gmul(int x, int y) {
    if (CUR_KIND == 1) return mat_mul(x, y);
    int a = x / CK, b = x % CK, c = y / CK, e = y % CK;
    return (int)(((long)a + (long)RP[b] * c) % CM) * CK + (b + e) % CK;
}

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int kind;        /* 0 metacyclic, 1 matrix */
    int q, mode;
    int m, k, r;
    int N, P;
    long V;
    int tier;
} Cand;

static Cand CAND[MAXCAND];
static int NC = 0;

static void push_cand(const Cand *c) {
    if (NC < MAXCAND) CAND[NC++] = *c;
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->tier != y->tier) return x->tier - y->tier;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
    return 0;
}

static void gen_candidates(long lo, long hi) {
    NC = 0;
    for (unsigned s = 0; s < (unsigned)NMSPEC; s++) {
        int q = MSPECS[s].q, mode = MSPECS[s].mode;
        int N = mat_order(q, mode);
        if (N > MAXNG) continue;
        for (int Pp = 1; Pp <= MAXP; Pp++) {
            long V = 2L * Pp * N;
            if (V < lo || V > hi) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.kind = 1;
            c.q = q;
            c.mode = mode;
            c.N = N;
            c.P = Pp;
            c.V = V;
            c.tier = 0;
            push_cand(&c);
        }
    }
    static const int KS[] = {2, 3, 4, 5, 6, 8, 10, 12};
    for (unsigned ki = 0; ki < 8; ki++) {
        long k = KS[ki];
        for (long m = 3; m * k <= MAXNG; m++) {
            long N = m * k;
            if (2L * N > hi) break;
            if (2L * MAXP * N < lo) continue;
            int r = -1;
            for (long rr = 2; rr < m && rr <= 300; rr++) {
                if (gcd_i((int)rr, (int)m) != 1) continue;
                if (powmod(rr, k, m) != 1 % m) continue;
                r = (int)rr;
                break;
            }
            if (r < 0) continue;
            for (int Pp = 1; Pp <= MAXP; Pp++) {
                long V = 2L * Pp * N;
                if (V < lo || V > hi) continue;
                Cand c;
                memset(&c, 0, sizeof c);
                c.kind = 0;
                c.m = (int)m;
                c.k = (int)k;
                c.r = r;
                c.N = (int)N;
                c.P = Pp;
                c.V = V;
                c.tier = 1;
                push_cand(&c);
            }
        }
    }
    qsort(CAND, (size_t)NC, sizeof(Cand), cmp_cand);
}

static int apply_cand(const Cand *c) {
    if (c->kind == 1) {
        int n = matrix_build(c->q, c->mode);
        if (n != c->N || n <= 0) return 0;
        CUR_KIND = 1;
        GORD = n;
        GE = CODE2IDX[norm_code(1, 0, 0, 1)];
        if (GE < 0) return 0;
    } else {
        CUR_KIND = 0;
        CM = c->m;
        CK = c->k;
        CR = c->r;
        GORD = c->m * c->k;
        RP[0] = 1 % CM;
        for (int b = 1; b < CK; b++) RP[b] = (int)((long)RP[b - 1] * CR % CM);
        GE = 0;
    }
    P = c->P;
    half = P * GORD;
    return 1;
}

/* ------------------------------------------------------------------ voltage lift state */

static int nd;
static int dI[MAXDART], dJ[MAXDART], vol[MAXDART];
static int dA[MAXP][MAXDEG], dB[MAXP][MAXDEG];
static int FW[MAXDART][MAXNG];   /* FW[t][x] = x * g_t */
static int BW[MAXDART][MAXNG];   /* BW[t][y] = y * g_t^{-1} */

static void set_dart(int t) {
    int g = vol[t];
    for (int x = 0; x < GORD; x++) FW[t][x] = gmul(x, g);
    for (int x = 0; x < GORD; x++) BW[t][FW[t][x]] = x;
}

/* True if dart t with voltage g clashes with darts u < upto (same base pair, same voltage). */
static int clash(int t, int g, int upto) {
    for (int u = 0; u < upto; u++)
        if (u != t && dI[u] == dI[t] && dJ[u] == dJ[t] && vol[u] == g) return 1;
    return 0;
}

static int new_instance(void) {
    int M[MAXP][MAXP];
    int attempts = 0;
    for (;;) {
        if (++attempts > 200) return 0;
        memset(M, 0, sizeof M);
        for (int c = 0; c < d; c++) {
            int perm[MAXP];
            for (int i = 0; i < P; i++) perm[i] = i;
            for (int i = P - 1; i > 0; i--) {
                int j = rndint(i + 1), s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
            for (int i = 0; i < P; i++) M[i][perm[i]]++;
        }
        int ok = 1;
        for (int i = 0; i < P; i++)
            for (int j = 0; j < P; j++)
                if (M[i][j] > GORD) ok = 0;
        if (!ok) continue;
        int seen[2 * MAXP] = {0}, st[2 * MAXP], top = 0, ns = 1;
        seen[0] = 1;
        st[top++] = 0;
        while (top > 0) {
            int v = st[--top];
            for (int u = 0; u < 2 * P; u++) {
                if (seen[u]) continue;
                int linked = (v < P) ? (u >= P && M[v][u - P] > 0)
                                     : (u < P && M[u][v - P] > 0);
                if (linked) {
                    seen[u] = 1;
                    ns++;
                    st[top++] = u;
                }
            }
        }
        if (ns == 2 * P) break;
    }
    nd = 0;
    int cA[MAXP] = {0}, cB[MAXP] = {0};
    for (int i = 0; i < P; i++)
        for (int j = 0; j < P; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dI[nd] = i;
                dJ[nd] = j;
                dA[i][cA[i]++] = nd;
                dB[j][cB[j]++] = nd;
                nd++;
            }
    for (int t = 0; t < nd; t++) {
        int g = -1;
        for (int tries = 0; tries < 100000; tries++) {
            int cand = rndint(GORD);
            if (!clash(t, cand, t)) {
                g = cand;
                break;
            }
        }
        if (g < 0) return 0;
        vol[t] = g;
    }
    for (int t = 0; t < nd; t++) set_dart(t);
    return 1;
}

/* ------------------------------------------------------------------ implicit BFS cost */

static int STAMP[MAXV];
static int TICK = 0;
static int QV[MAXV];

/* Number of vertices within distance D of src in the implicit lift. */
static int ball(int src) {
    if (++TICK == 0x7fffffff) {
        memset(STAMP, 0, sizeof STAMP);
        TICK = 1;
    }
    int head = 0, tail = 0;
    STAMP[src] = TICK;
    QV[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = QV[head];
            if (v < half) {
                int i = v / GORD, x = v - i * GORD;
                for (int k = 0; k < d; k++) {
                    int t = dA[i][k];
                    int u = half + dJ[t] * GORD + FW[t][x];
                    if (STAMP[u] != TICK) {
                        STAMP[u] = TICK;
                        QV[tail++] = u;
                    }
                }
            } else {
                int w = v - half, j = w / GORD, y = w - j * GORD;
                for (int k = 0; k < d; k++) {
                    int t = dB[j][k];
                    int u = dI[t] * GORD + BW[t][y];
                    if (STAMP[u] != TICK) {
                        STAMP[u] = TICK;
                        QV[tail++] = u;
                    }
                }
            }
        }
    }
    return tail;
}

/* Left multiplication acts regularly on each fibre, so one representative per fibre suffices. */
static long cost_all(void) {
    long c = 0;
    for (int i = 0; i < P; i++) c += 2L * half - ball(i * GORD + GE);
    for (int j = 0; j < P; j++) c += 2L * half - ball(half + j * GORD + GE);
    return c;
}

/* ------------------------------------------------------------------ explicit graph */

typedef struct {
    int n;
    int deg[MAXV];
    int adj[MAXV][MAXDEG];
} Graph;

static Graph TMP, BEST;
static int HAVE = 0;

static uint64_t RA[MAXV * ((MAXV + 63) / 64)];
static uint64_t RB[MAXV * ((MAXV + 63) / 64)];

/* Number of unordered pairs at distance > D (0 means diameter <= D). */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        total += n - c;
    }
    return total / 2;
}

static int finalize(void) {
    TMP.n = 2 * half;
    for (int v = 0; v < TMP.n; v++) TMP.deg[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < GORD; x++) {
            int a = dI[t] * GORD + x;
            int b = half + dJ[t] * GORD + FW[t][x];
            TMP.adj[a][TMP.deg[a]++] = b;
            TMP.adj[b][TMP.deg[b]++] = a;
        }
    for (int v = 0; v < TMP.n; v++)
        if (TMP.deg[v] != d) return 0;
    if (bad_pairs(&TMP) != 0) return 0;
    BEST = TMP;
    HAVE = 1;
    return 1;
}

/* ------------------------------------------------------------------ search */

static int anneal(long steps, double until) {
    long cur = cost_all();
    double T0 = 1.0 + 2.0 * rnd01();
    for (long s = 0; s < steps && cur > 0; s++) {
        if ((s & 31) == 0 && now() > until) return 0;
        double T = T0 * (1.0 - (double)s / (double)steps) + 0.05;
        int t = rndint(nd);
        int old = vol[t];
        int g = rndint(GORD);
        if (g == old || clash(t, g, nd)) continue;
        vol[t] = g;
        set_dart(t);
        long nc = cost_all();
        long df = nc - cur;
        if (df <= 0 || rnd01() < exp(-(double)df / T)) {
            cur = nc;
        } else {
            vol[t] = old;
            set_dart(t);
        }
    }
    return cur == 0;
}

static int try_candidate(const Cand *c, double until) {
    long steps = 20000L + 30000000L / c->V;
    while (now() < until) {
        if (!new_instance()) continue;
        if (anneal(steps, until) && finalize()) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------------ output */

static void print_graph(const Graph *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++) m += g->deg[u];
    m /= 2;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

static void print_complete(void) {
    if (d < 1) {
        printf("1 0\n");
        return;
    }
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [lo]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long lo = argc > 5 ? atol(argv[5]) : 0;

    double t0 = now();
    t_end = t0 + limit * 0.93 - 0.3;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) {
        print_complete();
        return 0;
    }
    MOORE = moore_bound();
    long lowV = lo;
    if (lowV < 2L * d) lowV = 2L * d;
    long hiV = MOORE < MAXV ? MOORE : MAXV;

    if (lowV <= hiV) {
        gen_candidates(lowV, hiV);
        long bestV = 0;
        for (int i = 0; i < NC; i++) {
            double rem = t_end - now();
            if (rem < 0.3) break;
            Cand *c = &CAND[i];
            if (c->V <= bestV) continue;
            if (!apply_cand(c)) continue;
            double slice = rem * 0.15;
            if (slice < 0.8) slice = 0.8;
            if (slice > rem) slice = rem;
            if (try_candidate(c, now() + slice)) bestV = BEST.n;
        }
    }
    if (HAVE) print_graph(&BEST);
    else print_complete();
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


# Known floors (vertex counts) below which the C ladder need not look.
REF_LO = {(4, 9): 4300}


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 16 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.88 * time_limit - (time.monotonic() - t0) - 3.0
    if budget < 1.0:
        return best
    lo = max(best[0], REF_LO.get((d, D), 0))
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo],
                         timeout=budget + 10)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
