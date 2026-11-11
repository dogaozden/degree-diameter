"""Two-phase search for the bipartite degree-diameter problem.

Phase A keeps the parent's affine-group Haar search (F_q x| H), which already reaches the
record for the hard cases. It gets about half the budget and provides a safe result.

Phase B is the new, different construction. It is a voltage lift of a small balanced
base multigraph with B left and B right base vertices (B = 1, 2, 3). Each base vertex
has d darts, given by d random permutations of [B]. Every dart carries a voltage in the
semidirect product G = Z_m x|_r Z_k, with r^k = 1 mod m. The lift has 2*B*|G| vertices
and is d-regular, bipartite and simple. Simplicity is enforced by making parallel darts
carry distinct voltages.

Left multiplication by G is an automorphism, so the diameter test reduces to BFS from the
2B base vertices at element e. Simulated annealing changes one voltage at a time. The
candidates are tried in ascending order of order, with retries, and the largest valid lift
above the current best is kept. The Python side keeps the best valid graph from all
phases, so every case still returns a valid graph.
"""
import itertools
import time

import lib

C_HAAR = r'''
/* Affine-group Haar lift search.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 256
#define MAXC 256
#define MAXN 8192
#define MAXD 32
#define MAXCAND 8192

typedef struct { int q, p, k, c, N; } Cand;

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* ------------------------------------------------------------ finite fields */

static int ADDT[MAXQ][MAXQ], MULT[MAXQ][MAXQ], NEGT[MAXQ];
static int built_q = -1;

static int factor_pp(int q, int *p, int *k) {
    int pp = 0;
    for (int f = 2; f * f <= q; f++)
        if (q % f == 0) { pp = f; break; }
    if (!pp) pp = q;
    int r = q, kk = 0;
    while (r % pp == 0) { r /= pp; kk++; }
    if (r != 1 || kk < 1) return 0;
    *p = pp;
    *k = kk;
    return 1;
}

/* Multiply field elements a, b (base-p digit vectors) modulo the monic f with digits m. */
static int polymul(int a, int b, int p, int k, const int *pw, const int *m) {
    int pa[16], pb[16], prod[32];
    for (int i = 0; i < k; i++) {
        pa[i] = (a / pw[i]) % p;
        pb[i] = (b / pw[i]) % p;
    }
    for (int i = 0; i < 2 * k; i++) prod[i] = 0;
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            prod[i + j] = (prod[i + j] + pa[i] * pb[j]) % p;
    for (int deg = 2 * k - 2; deg >= k; deg--) {
        int c = prod[deg];
        if (!c) continue;
        for (int i = 0; i < k; i++) {
            int idx = deg - k + i;
            prod[idx] = ((prod[idx] - c * m[i]) % p + p) % p;
        }
        prod[deg] = 0;
    }
    int r = 0;
    for (int i = 0; i < k; i++) r += prod[i] * pw[i];
    return r;
}

static void build_field(int q, int p, int k) {
    if (built_q == q) return;
    int pw[16];
    pw[0] = 1;
    for (int i = 1; i <= k; i++) pw[i] = pw[i - 1] * p;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            int r = 0;
            for (int i = 0; i < k; i++)
                r += (((a / pw[i]) % p + (b / pw[i]) % p) % p) * pw[i];
            ADDT[a][b] = r;
        }
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            if (ADDT[a][b] == 0) NEGT[a] = b;

    int found = 0;
    for (int code = 0; code < q && !found; code++) {
        int m[16];
        int t = code;
        for (int i = 0; i < k; i++) { m[i] = t % p; t /= p; }
        int ok = 1;
        for (int a = 1; a < q && ok; a++)
            for (int b = 1; b < q && ok; b++)
                if (polymul(a, b, p, k, pw, m) == 0) ok = 0;   /* zero divisor: reducible */
        if (ok) {
            found = 1;
            for (int a = 0; a < q; a++)
                for (int b = 0; b < q; b++)
                    MULT[a][b] = polymul(a, b, p, k, pw, m);
        }
    }
    built_q = q;
}

/* ------------------------------------------------------------ group G = F_q x| H */

static int GQ, GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Element (a, h_j) is coded as a*c + j, with h_j = g^(j*(q-1)/c). Product:
 * (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). */
static void setup_group(int q, int p, int k, int c) {
    build_field(q, p, k);
    GQ = q;
    GC = c;
    GN = q * c;
    int g = -1;
    for (int g0 = 2; g0 < q && g < 0; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) g = g0;
    }
    PWG[0] = 1;
    for (int i = 1; i < q - 1; i++) PWG[i] = MULT[PWG[i - 1]][g];
    int step = (q - 1) / c;
    for (int j = 0; j < q; j++) hidx[j] = -1;
    for (int t = 0; t < c; t++) {
        Hel[t] = PWG[(t * step) % (q - 1)];
        hidx[Hel[t]] = t;
    }
    for (int j = 0; j < c; j++)
        for (int t = 0; t < c; t++)
            HM[j * c + t] = hidx[MULT[Hel[j]][Hel[t]]];
}

static inline int gmul(int x, int y) {
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static int ginv(int x) {
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

/* ------------------------------------------------------------ Haar graph state */

static int S[MAXD], Sinv[MAXD], bestS[MAXD];
static int fwd[MAXD][MAXN], bwd[MAXD][MAXN];
static int vis[2 * MAXN], que[2 * MAXN];
static int stamp_ = 0;

/* Vertices: L_g = g (0..N-1), R_h = N + h. L_g ~ R_{g s}, so R_h ~ L_{h s^-1}. */
static void set_s(int i, int x) {
    S[i] = x;
    Sinv[i] = ginv(x);
    for (int g = 0; g < GN; g++) {
        fwd[i][g] = gmul(g, x);
        bwd[i][g] = gmul(g, Sinv[i]);
    }
}

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int N = GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int u = N + fwd[i][v];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int h = v - N;
                for (int i = 0; i < d; i++) {
                    int u = bwd[i][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Vertex-transitivity on each side means two BFS runs (from L_e and R_e) decide diameter. */
static long cover_cost(void) {
    int V = 2 * GN;
    return (long)(V - bfs_count(0)) + (long)(V - bfs_count(GN));
}

static int in_S(int x, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == x) return 1;
    return 0;
}

/* Simulated annealing over the connection set S of size d in the current group.
 * Returns 1 when cost 0 is reached (diameter <= D), 0 on timeout. */
static int search_group(double until) {
    int N = GN;
    const int iters = 8000;
    while (now() < until) {
        for (int i = 0; i < d; i++) {
            int x;
            do { x = rndint(N); } while (in_S(x, i));
            set_s(i, x);
        }
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(d);
            int x;
            do { x = rndint(N); } while (in_S(x, d));
            int old = S[i];
            set_s(i, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_s(i, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void print_result(void) {
    int N = GN;
    printf("%d %d\n", 2 * N, N * d);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + fwd[i][g]);
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (hi > MAXN) hi = MAXN;
    if (lo < 2 * d) lo = 2 * d;

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            if (nc < MAXCAND) {
                Cand cd = {q, p, k, c, (int)N};
                cand[nc++] = cd;
            }
        }
    }
    for (int i = 1; i < nc; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].N > t.N) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = t;
    }

    /* Repeated passes in ascending order. Each attempt gets 20% of the remaining
     * time (at least 1 s). Candidates that failed in an earlier pass are retried
     * with fresh random starts. */
    int best_idx = -1, bestN = 0;
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            if (cand[ci].N <= bestN) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = 0.2 * rem;
            if (slice < 1.0) slice = 1.0;
            if (slice > rem) slice = rem;
            setup_group(cand[ci].q, cand[ci].p, cand[ci].k, cand[ci].c);
            if (search_group(now() + slice)) {
                bestN = GN;
                best_idx = ci;
                memcpy(bestS, S, sizeof(int) * (size_t)d);
            }
        }
        if (!tried || t_end - now() < 0.3) break;
    }

    if (best_idx < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(cand[best_idx].q, cand[best_idx].p, cand[best_idx].k, cand[best_idx].c);
    for (int i = 0; i < d; i++) set_s(i, bestS[i]);
    print_result();
    return 0;
}
'''

C_VOLT = r'''
/* Voltage-lift search over G = Z_m x|_r Z_k with a B-vertex base per side.
 * Usage: prog d D seed time_limit minTotal maxTotal     (stdin ignored)
 * Output: "n m" then m lines "u v" for the best valid lift, or "0 0".
 *
 * Vertices: left (u,x) = u*N + x, right (v,y) = (B+v)*N + y, with N = |G|.
 * Dart (j,u) joins (u,x) to (pi_j(u), x*g_{j,u}). Each pi_j is a permutation of [B],
 * so the lift is d-regular and bipartite. Parallel darts need distinct voltages (cost).
 * Left multiplication is an automorphism, so diameter <= D iff BFS from (u,e) for
 * each of the 2B base vertices reaches everything within D.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 16
#define MAXB 3
#define MAXV 16384
#define MAXK 12
#define MAXCAND 60000
#define RPICK 3

typedef struct { int b, m, k, r, N, T, key; } Cand;

static int dd, DD;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
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

/* ------------------------------------------------------------ group Z_m x|_r Z_k */

static int gm, gk, gr, gN;
static long gpow[MAXK + 1];

static void set_group(int m, int k, int r) {
    gm = m;
    gk = k;
    gr = r;
    gN = m * k;
    gpow[0] = 1 % m;
    for (int i = 1; i < k; i++) gpow[i] = (gpow[i - 1] * (long)r) % m;
}

/* Element (a, b) is coded a*k + b. (a,b)(c,e) = (a + r^b c, b + e). */
static inline int gmul(int x, int y) {
    int a = x / gk, b = x - a * gk;
    int c = y / gk, e = y - c * gk;
    long na = (a + gpow[b] * c) % gm;
    int nb = b + e;
    if (nb >= gk) nb -= gk;
    return (int)na * gk + nb;
}

/* Inverse of (a, b) is (-r^(-b) a, -b), with r^(-b) = r^((k-b) mod k). */
static inline int ginv(int x) {
    int a = x / gk, b = x - a * gk;
    int nb = (gk - b) % gk;
    long na = (gm - (gpow[nb] * a) % gm) % gm;
    return (int)na * gk + nb;
}

/* ------------------------------------------------------------ base voltage state */

static int B;
static int V;
static int pi_[MAXD][MAXB], pinv_[MAXD][MAXB];
static int Gv[MAXD][MAXB], Gi[MAXD][MAXB];
static int sPi[MAXD][MAXB], sG[MAXD][MAXB];

static void set_volt(int j, int u, int g) {
    Gv[j][u] = g;
    Gi[j][u] = ginv(g);
}

static void random_perms(void) {
    for (int j = 0; j < dd; j++) {
        int p[MAXB];
        for (int u = 0; u < B; u++) p[u] = u;
        for (int u = B - 1; u > 0; u--) {
            int t = rndint(u + 1);
            int tmp = p[u];
            p[u] = p[t];
            p[t] = tmp;
        }
        for (int u = 0; u < B; u++) {
            pi_[j][u] = p[u];
            pinv_[j][p[u]] = u;
        }
    }
}

/* ------------------------------------------------------------ BFS and cost */

static int vis[MAXV], que[MAXV], stampc = 0;

/* Number of vertices within distance DD of src. */
static int bfs_reach(int src) {
    int NL = B * gN;
    stampc++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stampc;
    for (int lvl = 0; lvl < DD && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int id = que[head++];
            if (id < NL) {
                int u = id / gN, x = id - u * gN;
                for (int j = 0; j < dd; j++) {
                    int v = pi_[j][u];
                    int y = gmul(x, Gv[j][u]);
                    int nid = NL + v * gN + y;
                    if (vis[nid] != stampc) { vis[nid] = stampc; que[tail++] = nid; }
                }
            } else {
                int idx = id - NL;
                int v = idx / gN, y = idx - v * gN;
                for (int j = 0; j < dd; j++) {
                    int u = pinv_[j][v];
                    int x = gmul(y, Gi[j][u]);
                    int nid = u * gN + x;
                    if (vis[nid] != stampc) { vis[nid] = stampc; que[tail++] = nid; }
                }
            }
        }
    }
    return tail;
}

/* Parallel darts with equal voltage give duplicate edges. Count them as cost. */
static long collisions(void) {
    long c = 0;
    for (int u = 0; u < B; u++)
        for (int j = 0; j < dd; j++)
            for (int t = j + 1; t < dd; t++)
                if (pi_[j][u] == pi_[t][u] && Gv[j][u] == Gv[t][u]) c++;
    return c;
}

/* Source s < B is left base vertex s; s >= B is right base vertex s-B. Both have id s*gN. */
static long cover_cost(void) {
    long c = 0;
    for (int s = 0; s < 2 * B; s++)
        c += (long)(V - bfs_reach(s * gN));
    return c + collisions();
}

/* Annealing over voltages for the current group and base size. Returns 1 on cost 0. */
static int search_cand(double until) {
    while (now() < until) {
        random_perms();
        for (int j = 0; j < dd; j++)
            for (int u = 0; u < B; u++)
                set_volt(j, u, rndint(gN));
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        const int iters = 6000;
        for (int it = 0; it < iters; it++) {
            if ((it & 7) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int j = rndint(dd), u = rndint(B);
            int old = Gv[j][u];
            int g = rndint(gN);
            if (g == old) continue;
            set_volt(j, u, g);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                if (cost == 0) return 1;
            } else {
                set_volt(j, u, old);
            }
        }
    }
    return 0;
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    if (x->T != y->T) return x->T < y->T ? -1 : 1;
    if (x->key != y->key) return x->key < y->key ? -1 : 1;
    return 0;
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long minT = atol(argv[5]), maxT = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (dd < 2 || dd > MAXD || DD < 3) { printf("0 0\n"); return 0; }
    if (maxT > MAXV) maxT = MAXV;
    if (minT < 2) minT = 2;
    if (minT > maxT) { printf("0 0\n"); return 0; }

    static Cand cand[MAXCAND];
    static int rl[8200];
    int nc = 0;
    for (int b = 1; b <= MAXB; b++)
        for (int k = 1; k <= MAXK; k++)
            for (int m = 1; ; m++) {
                long T = 2L * b * m * k;
                if (T > maxT) break;
                if (T < minT) continue;
                int nr = 0;
                if (m >= 2) {
                    for (int r = 2; r < m; r++) {
                        if (gcd_i(r, m) != 1) continue;
                        long p = 1;
                        for (int i = 0; i < k; i++) p = (p * r) % m;
                        if (p == 1 && nr < 8200) rl[nr++] = r;
                    }
                }
                int ch[RPICK], nch = 0;
                if (m == 1) {
                    ch[nch++] = 0;
                } else {
                    ch[nch++] = 1;  /* the direct product Z_m x Z_k */
                    for (int t = 0; t < RPICK - 1 && nr > 0; t++) {
                        int pick = rndint(nr);
                        ch[nch++] = rl[pick];
                        rl[pick] = rl[--nr];
                    }
                }
                for (int t = 0; t < nch && nc < MAXCAND; t++) {
                    Cand cd;
                    cd.b = b;
                    cd.m = m;
                    cd.k = k;
                    cd.r = ch[t];
                    cd.N = m * k;
                    cd.T = (int)T;
                    cd.key = rndint(1 << 30);
                    cand[nc++] = cd;
                }
            }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    long bestT = minT - 1;
    int found = 0;
    Cand bc;
    memset(&bc, 0, sizeof(bc));
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            if (cand[ci].T <= bestT) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = 0.15 * rem;
            if (slice < 0.6) slice = 0.6;
            if (slice > rem) slice = rem;
            B = cand[ci].b;
            set_group(cand[ci].m, cand[ci].k, cand[ci].r);
            V = 2 * B * gN;
            if (search_cand(now() + slice)) {
                bestT = cand[ci].T;
                bc = cand[ci];
                found = 1;
                memcpy(sPi, pi_, sizeof(pi_));
                memcpy(sG, Gv, sizeof(Gv));
            }
        }
        if (!tried || t_end - now() < 0.3) break;
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    B = bc.b;
    set_group(bc.m, bc.k, bc.r);
    int N = gN;
    printf("%d %d\n", 2 * B * N, B * N * dd);
    for (int u = 0; u < B; u++)
        for (int x = 0; x < N; x++)
            for (int j = 0; j < dd; j++) {
                int v = sPi[j][u];
                int y = gmul(x, sG[j][u]);
                printf("%d %d\n", u * N + x, (B + v) * N + y);
            }
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d (kept small for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.85 * time_limit - 2.0
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2 and is the safe fallback.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    def run_search(src, args, budget):
        try:
            text = lib.run_c(src, args, stdin_graph=None, timeout=budget + 8.0)
            consider(lib.parse_graph_text(text))
        except Exception:
            pass   # keep the best valid graph so far

    if D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
        # Exact Moore graph: nothing can beat it.
        if D == 3 and lib.is_prime_power(d - 1) and best[0] > 2 * d:
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)

        # Phase A: affine-group Haar search (the parent's engine), about half the budget.
        left = deadline - time.monotonic()
        lo_a = max(best[0] // 2 + 1, mb // 8)
        hi_a = mb // 3
        if left > 2.0 and lo_a <= hi_a:
            budget = 0.5 * left
            run_search(C_HAAR, [d, D, seed, round(budget, 2), lo_a, hi_a], budget)

        # Phase B: voltage lifts over Z_m x|_r Z_k with 1-3 base vertices per side.
        # Only orders above the current best are tried.
        left = deadline - time.monotonic()
        min_t = max(best[0] + 1, mb // 4)
        max_t = min(mb // 2, 16000)
        if left > 2.0 and min_t <= max_t:
            run_search(C_VOLT, [d, D, seed, round(left, 2), min_t, max_t], left)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
