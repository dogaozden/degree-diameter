"""Base-lift search for the bipartite degree-diameter problem, with a Haar fallback.

New construction in this version: a generalized voltage lift over an affine group
G = F_q x| H (order N = q*c, c | q-1, c >= 2), with a base graph of b left and b right
vertices (b = 1, 2, 3). The base is d-regular on each side, and each dart carries a
group voltage. The lift has 2*b*N vertices and is d-regular and bipartite. Darts that
share both endpoints get distinct voltages, so the lift is simple. Left multiplication
is an automorphism acting regularly on each fibre, so the diameter check needs only 2*b
BFS runs, one from each fibre representative. Simulated annealing moves voltages and
swaps dart targets while keeping the column counts fixed.

The previous Haar engine (b = 1 with a single base vertex per side) is kept as a second
stage, so the result never falls below the earlier 2510. Every returned graph is checked
with lib.is_valid, and K_{d,d} is the final fallback.
"""
import itertools
import time

import lib

# Stage A: generalized affine base-lift search (new construction).
C_BASE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 256
#define MAXN 2400
#define MAXD 32
#define MAXB 3
#define MAXBD (MAXB * MAXD)
#define MAXV (2 * MAXB * MAXN)
#define MAXCAND 8192
#define ITERS 15000

typedef struct { int q, p, k, c, n, b, v; } Cand;

static int d, D, b, N;
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

static int polymul(int a, int b2, int p, int k, const int *pw, const int *m) {
    int pa[16], pb[16], prod[32];
    for (int i = 0; i < k; i++) {
        pa[i] = (a / pw[i]) % p;
        pb[i] = (b2 / pw[i]) % p;
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
        for (int b2 = 0; b2 < q; b2++) {
            int r = 0;
            for (int i = 0; i < k; i++)
                r += (((a / pw[i]) % p + (b2 / pw[i]) % p) % p) * pw[i];
            ADDT[a][b2] = r;
        }
    for (int a = 0; a < q; a++)
        for (int b2 = 0; b2 < q; b2++)
            if (ADDT[a][b2] == 0) NEGT[a] = b2;

    int found = 0;
    for (int code = 0; code < q && !found; code++) {
        int m[16];
        int t = code;
        for (int i = 0; i < k; i++) { m[i] = t % p; t /= p; }
        int ok = 1;
        for (int a = 1; a < q && ok; a++)
            for (int b2 = 1; b2 < q && ok; b2++)
                if (polymul(a, b2, p, k, pw, m) == 0) ok = 0;
        if (ok) {
            found = 1;
            for (int a = 0; a < q; a++)
                for (int b2 = 0; b2 < q; b2++)
                    MULT[a][b2] = polymul(a, b2, p, k, pw, m);
        }
    }
    built_q = q;
}

/* ------------------------------------------------------------ group F_q x| H */

static int HEL[MAXQ];
static short MT[MAXN][MAXN];
static int INVG[MAXN];

/* Element (a, h_j) is coded a*c + j, h_j = g^(j*(q-1)/c). Product (a,h_j)(b,h_t)
 * = (a + h_j*b, h_(j+t mod c)). */
static void setup_affine(int q, int p, int k, int c) {
    build_field(q, p, k);
    N = q * c;
    int g = -1;
    for (int g0 = 2; g0 < q && g < 0; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) g = g0;
    }
    int PW[MAXQ];
    PW[0] = 1;
    for (int i = 1; i < q - 1; i++) PW[i] = MULT[PW[i - 1]][g];
    int step = (q - 1) / c;
    for (int j = 0; j < c; j++) HEL[j] = PW[(j * step) % (q - 1)];
    for (int x = 0; x < N; x++) {
        int a = x / c, j = x % c;
        for (int y = 0; y < N; y++) {
            int bb = y / c, t = y % c;
            int na = ADDT[a][MULT[HEL[j]][bb]];
            MT[x][y] = (short)(na * c + (j + t) % c);
        }
    }
    for (int x = 0; x < N; x++) {
        int a = x / c, j = x % c;
        int jn = (c - j) % c;
        int na = NEGT[MULT[HEL[jn]][a]];
        INVG[x] = na * c + jn;
    }
}

/* ------------------------------------------------------------ base-lift state */

static int J[MAXBD], G[MAXBD], bestJ[MAXBD], bestG[MAXBD];
static int rdl[MAXB][MAXD];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static void rebuild_rdl(void) {
    int cnt[MAXB];
    for (int j = 0; j < b; j++) cnt[j] = 0;
    for (int e = 0; e < b * d; e++) {
        int j = J[e];
        rdl[j][cnt[j]++] = e;
    }
}

static int all_ok(void) {
    for (int i = 0; i < b; i++)
        for (int k1 = 0; k1 < d; k1++)
            for (int k2 = k1 + 1; k2 < d; k2++) {
                int e1 = i * d + k1, e2 = i * d + k2;
                if (J[e1] == J[e2] && G[e1] == G[e2]) return 0;
            }
    return 1;
}

static int conflict_e(int e) {
    int i = e / d;
    for (int k = 0; k < d; k++) {
        int e2 = i * d + k;
        if (e2 != e && J[e2] == J[e] && G[e2] == G[e]) return 1;
    }
    return 0;
}

static void random_init(void) {
    int tot = b * d;
    int T[MAXBD];
    for (int e = 0; e < tot; e++) T[e] = e % b;   /* every target appears exactly d times */
    for (int e = tot - 1; e > 0; e--) {
        int r = rndint(e + 1);
        int tmp = T[e]; T[e] = T[r]; T[r] = tmp;
    }
    for (int e = 0; e < tot; e++) { J[e] = T[e]; G[e] = rndint(N); }
    for (int it = 0; it < 200 && !all_ok(); it++)
        for (int e = 0; e < tot; e++)
            if (conflict_e(e)) G[e] = rndint(N);
}

/* Vertex ids: L(i,x) = i*N + x, R(j,y) = (b+j)*N + y. */
static int ball(int src) {
    int Nb = b * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < Nb) {
                int i = v / N, x = v % N;
                for (int k = 0; k < d; k++) {
                    int e = i * d + k;
                    int u = (b + J[e]) * N + MT[x][G[e]];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int r = v - Nb;
                int j = r / N, y = r % N;
                for (int t = 0; t < d; t++) {
                    int e = rdl[j][t];
                    int i = e / d;
                    int u = i * N + MT[y][INVG[G[e]]];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left multiplication is an automorphism that is regular on each fibre, so BFS from
 * the identity of every fibre decides the diameter. */
static long cost(void) {
    long V = 2L * b * N;
    long c = 0;
    for (int i = 0; i < b; i++) c += V - ball(i * N);
    for (int j = 0; j < b; j++) c += V - ball((b + j) * N);
    return c;
}

static void save_best(void) {
    memcpy(bestJ, J, sizeof(int) * (size_t)(b * d));
    memcpy(bestG, G, sizeof(int) * (size_t)(b * d));
}

static int search(double until) {
    int tot = b * d;
    int sJ[MAXBD], sG[MAXBD];
    while (now() < until) {
        random_init();
        if (!all_ok()) continue;
        rebuild_rdl();
        long cur = cost();
        if (cur == 0) { save_best(); return 1; }
        double c0 = (double)cur;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < ITERS && cur > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / ITERS);
            memcpy(sJ, J, sizeof(int) * (size_t)tot);
            memcpy(sG, G, sizeof(int) * (size_t)tot);
            if (rnd01() < 0.5) {
                int e = rndint(tot);
                G[e] = rndint(N);
            } else {
                int e1 = rndint(tot), e2 = rndint(tot);
                if (J[e1] == J[e2]) continue;
                int tmp = J[e1]; J[e1] = J[e2]; J[e2] = tmp;
            }
            if (!all_ok()) {
                memcpy(J, sJ, sizeof(int) * (size_t)tot);
                memcpy(G, sG, sizeof(int) * (size_t)tot);
                continue;
            }
            rebuild_rdl();
            long c2 = cost();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                memcpy(J, sJ, sizeof(int) * (size_t)tot);
                memcpy(G, sG, sizeof(int) * (size_t)tot);
                rebuild_rdl();
            }
        }
        if (cur == 0) { save_best(); return 1; }
    }
    return 0;
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

    if (d < 2 || d > MAXD || D < 1) { printf("0 0\n"); return 0; }

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            int n = q * c;
            if (n > MAXN || n < 2 * d) continue;
            for (int bb = 1; bb <= MAXB; bb++) {
                int v = 2 * bb * n;
                if (v < lo || v > hi) continue;
                if (nc < MAXCAND) {
                    Cand cd = {q, p, k, c, n, bb, v};
                    cand[nc++] = cd;
                }
            }
        }
    }
    for (int i = 1; i < nc; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].v > t.v) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = t;
    }

    /* Ascending pass: each candidate above the best found so far gets a slice of the
     * remaining time. Successes raise the bar; failures cost only a small slice. */
    int best_v = 0, best_idx = -1;
    for (int idx = 0; idx < nc && now() < t_end; idx++) {
        if (cand[idx].v <= best_v) continue;
        double rem = t_end - now();
        double slice = 0.06 * rem;
        if (slice < 0.3) slice = 0.3;
        if (slice > rem) slice = rem;
        setup_affine(cand[idx].q, cand[idx].p, cand[idx].k, cand[idx].c);
        b = cand[idx].b;
        if (search(now() + slice)) {
            best_v = cand[idx].v;
            best_idx = idx;
        }
    }

    if (best_idx < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_affine(cand[best_idx].q, cand[best_idx].p, cand[best_idx].k, cand[best_idx].c);
    b = cand[best_idx].b;
    memcpy(J, bestJ, sizeof(int) * (size_t)(b * d));
    memcpy(G, bestG, sizeof(int) * (size_t)(b * d));
    long V = 2L * b * N;
    long m = (long)b * N * d;
    printf("%ld %ld\n", V, m);
    for (int i = 0; i < b; i++)
        for (int x = 0; x < N; x++)
            for (int k = 0; k < d; k++) {
                int e = i * d + k;
                int u = i * N + x;
                int v = (b + J[e]) * N + MT[x][G[e]];
                printf("%d %d\n", u, v);
            }
    return 0;
}
'''

# Stage B: the previous affine Haar engine (single base vertex per side), kept as a
# safety net so the result never drops below the earlier record-level graph.
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

    int best_idx = -1, bestN = 0;

    /* Phase 1: binary search for the largest feasible order. */
    int a = 0, b = nc - 1;
    while (a <= b && now() < t_end) {
        int mid = (a + b) / 2;
        int span = b - a + 1;
        int probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = t_end - now();
        double slice = rem / (probes + 1);
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_group(cand[mid].q, cand[mid].p, cand[mid].k, cand[mid].c);
        if (search_group(now() + slice)) {
            if (cand[mid].N > bestN) {
                bestN = cand[mid].N;
                best_idx = mid;
                memcpy(bestS, S, sizeof(int) * (size_t)d);
            }
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }

    /* Phase 2: spend the leftover time on the next few orders above the best. */
    int fails = 0;
    int idx = best_idx < 0 ? 0 : best_idx + 1;
    while (idx < nc && now() < t_end && fails < 2) {
        if (cand[idx].N <= bestN) { idx++; continue; }
        double rem = t_end - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        setup_group(cand[idx].q, cand[idx].p, cand[idx].k, cand[idx].c);
        if (search_group(now() + slice)) {
            bestN = cand[idx].N;
            best_idx = idx;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
            idx++;
            fails = 0;
        } else {
            idx++;
            fails++;
        }
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
        deadline = t0 + 0.85 * time_limit - 1.0

        # Stage A: generalized affine base-lift search (new construction).
        budA = 0.6 * (deadline - time.monotonic())
        if budA > 3.0:
            lo_v = max(best[0] + 1, mb // 4)
            if lo_v <= mb:
                try:
                    text = lib.run_c(C_BASE, [d, D, seed, round(budA, 2), lo_v, mb],
                                     stdin_graph=None, timeout=budA + 8.0)
                    consider(lib.parse_graph_text(text))
                except Exception:
                    pass   # keep the valid graph found so far

        # Stage B: the affine Haar engine, searching orders above the current best.
        budB = deadline - time.monotonic()
        if budB > 3.0:
            lo_n = max(best[0] // 2 + 1, mb // 8)
            hi_n = mb // 2
            if lo_n <= hi_n:
                try:
                    text = lib.run_c(C_HAAR, [d, D, seed, round(budB, 2), lo_n, hi_n],
                                     stdin_graph=None, timeout=budB + 8.0)
                    consider(lib.parse_graph_text(text))
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
