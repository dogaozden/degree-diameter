"""Two-base voltage lifts over metacyclic groups, with the affine-group Haar search kept as a fallback.

New construction (this version): take two left vertices L_0, L_1 and two right vertices R_0, R_1.
Each left vertex has d darts. L_0 sends t darts to R_0 and d-t to R_1; L_1 sends d-t to R_0
and t to R_1. Every right vertex then has degree d. For a group G = Z_m x|_r Z_k of order N,
a dart (a, b, s) joins (a, x) to (b, x*s). The lift has 4N vertices, is bipartite and
d-regular. Left translations act with 4 orbits, so the diameter is <= D iff four BFS runs
from L_0, L_1, R_0, R_1 reach everything within D steps. Simulated annealing searches over
the voltages, the group and t. Orders ascend from just above the record (4N > 2496).

The affine-group Haar search from the parent is kept as a second engine, with the leftover
budget, so the parent's valid result is still available as a fallback.
"""
import itertools
import time

import lib

MAX_N_LIFT = 4000

C_SOURCE_LIFT = r'''
/* Two-base voltage lift search over Z_m x|_r Z_k.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 * Vertices: left (a,x) = a*N + x, right (b,y) = 2N + b*N + y, a,b in {0,1}.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 32
#define MAXGL 3000
#define ITERS 4000

static int d, D;
static int N, M_, K_;
static int PW[MAXN];
static int VS[2 * MAXD], VIS[2 * MAXD], TG[2 * MAXD], SL[2][MAXD];
static int FW[2 * MAXD][MAXN], BW[2 * MAXD][MAXN];
static int vis[4 * MAXN], que[4 * MAXN];
static int stampc = 0;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static int bestN = 0, bestT = 0, bestM = 0, bestK = 0;
static int bestVS[2 * MAXD], bestPW[MAXN];

static int GM[MAXGL], GK[MAXGL], GR[MAXGL];
static int ngl = 0;

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

/* ------------------------------------------------------------ groups */

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int powmod_i(int b, int e, int m) {
    long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* All Z_m x|_r Z_k with m*k = n, gcd(r,m) = 1, r^k = 1 mod m. */
static void enum_groups(int n) {
    ngl = 0;
    for (int m = 1; m <= n && ngl < MAXGL; m++) {
        if (n % m) continue;
        int k = n / m;
        for (int r = 0; r < m && ngl < MAXGL; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod_i(r, k, m) != 1 % m) continue;
            GM[ngl] = m;
            GK[ngl] = k;
            GR[ngl] = r;
            ngl++;
        }
    }
}

static void setup_group(int m, int k, int r) {
    M_ = m;
    K_ = k;
    PW[0] = 1 % m;
    for (int b = 1; b < k; b++) PW[b] = (int)((long)PW[b - 1] * r % m);
}

/* (a,b)(c,d) = (a + r^b c, b + d). Element (a,b) is coded a*K + b. */
static inline int gmul(int x, int y) {
    int xa = x / K_, xb = x - xa * K_;
    int ya = y / K_, yb = y - ya * K_;
    int za = (xa + PW[xb] * ya) % M_;
    int zb = xb + yb;
    if (zb >= K_) zb -= K_;
    return za * K_ + zb;
}

/* Inverse of (a,b) is (-r^(-b) a, -b). */
static inline int ginv(int x) {
    int xa = x / K_, xb = x - xa * K_;
    int nb = (K_ - xb) % K_;
    int na = (M_ - (PW[nb] * xa) % M_) % M_;
    return na * K_ + nb;
}

/* ------------------------------------------------------------ lift state */

/* Slot s = a*d + j is dart j of left vertex a. Its target block is TG[s]. */
static void setup_targets(int t) {
    int cnt[2] = {0, 0};
    for (int a = 0; a < 2; a++)
        for (int j = 0; j < d; j++) {
            int s = a * d + j;
            int b;
            if (a == 0) b = (j < t) ? 0 : 1;
            else b = (j < d - t) ? 0 : 1;
            TG[s] = b;
            SL[b][cnt[b]++] = s;
        }
}

static void rebuild_slot(int s) {
    int b = TG[s], a = (s >= d) ? 1 : 0;
    int v = VS[s], vi = VIS[s];
    for (int x = 0; x < N; x++) {
        FW[s][x] = 2 * N + b * N + gmul(x, v);
        BW[s][x] = a * N + gmul(x, vi);
    }
}

static void rebuild_all(void) {
    for (int s = 0; s < 2 * d; s++) rebuild_slot(s);
}

/* x may be used as a voltage in slot s only if no other slot of the same
 * left vertex with the same target block uses it (keeps the lift simple). */
static int slot_ok(int s, int x) {
    int a = (s >= d) ? 1 : 0, b = TG[s];
    for (int j = 0; j < d; j++) {
        int s2 = a * d + j;
        if (s2 != s && TG[s2] == b && VS[s2] == x) return 0;
    }
    return 1;
}

static void random_init(void) {
    for (int s = 0; s < 2 * d; s++) VS[s] = -1;
    for (int s = 0; s < 2 * d; s++) {
        int x;
        do { x = rndint(N); } while (!slot_ok(s, x));
        VS[s] = x;
        VIS[s] = ginv(x);
    }
}

/* Number of vertices within distance D of src. */
static int bfs_reach(int src) {
    stampc++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stampc;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < 2 * N) {
                int a = (v >= N) ? 1 : 0;
                int x = v - a * N;
                for (int j = 0; j < d; j++) {
                    int u = FW[a * d + j][x];
                    if (vis[u] != stampc) {
                        vis[u] = stampc;
                        que[tail++] = u;
                    }
                }
            } else {
                int r = v - 2 * N;
                int b = (r >= N) ? 1 : 0;
                int y = r - b * N;
                for (int k = 0; k < d; k++) {
                    int u = BW[SL[b][k]][y];
                    if (vis[u] != stampc) {
                        vis[u] = stampc;
                        que[tail++] = u;
                    }
                }
            }
        }
    }
    return tail;
}

/* Left translations give 4 vertex orbits (2 per side), so 4 BFS runs decide the diameter. */
static long cost_eval(void) {
    int srcs[4] = {0, N, 2 * N, 3 * N};
    long c = 0;
    for (int i = 0; i < 4; i++) c += (long)(4 * N - bfs_reach(srcs[i]));
    return c;
}

/* Simulated annealing on the voltages. Returns 1 at cost 0, 0 when the
 * iteration budget ends, -1 on timeout. */
static int sa_attempt(double until, int iters) {
    long cost = cost_eval();
    double c0 = cost > 0 ? (double)cost : 1.0;
    double Ts = 0.05 * c0 + 1.0, Te = 0.3;
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 15) == 0 && now() > until) return -1;
        double T = Ts * pow(Te / Ts, (double)it / iters);
        int s = rndint(2 * d);
        int x;
        do { x = rndint(N); } while (!slot_ok(s, x));
        int old = VS[s], oldi = VIS[s];
        VS[s] = x;
        VIS[s] = ginv(x);
        rebuild_slot(s);
        long c2 = cost_eval();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            VS[s] = old;
            VIS[s] = oldi;
            rebuild_slot(s);
        }
    }
    return cost == 0 ? 1 : 0;
}

static void save_best(int t) {
    bestN = N;
    bestT = t;
    bestM = M_;
    bestK = K_;
    for (int s = 0; s < 2 * d; s++) bestVS[s] = VS[s];
    for (int b = 0; b < K_; b++) bestPW[b] = PW[b];
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
    if (d < 3 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (lo < 2 * d) lo = 2 * d;
    if (hi > MAXN) hi = MAXN;

    /* Ascending group orders N (vertices = 4N). Each N gets a slice of the
     * remaining time; success moves on to larger N. */
    for (int n = lo; n <= hi; n++) {
        if (now() > t_end - 0.3) break;
        enum_groups(n);
        if (ngl == 0) continue;
        N = n;
        double rem = t_end - now();
        double slice = 0.12 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        double until = now() + slice;
        int ok = 0;
        while (!ok && now() < until) {
            int gi = rndint(ngl);
            int t = 1 + rndint(d - 1);
            setup_group(GM[gi], GK[gi], GR[gi]);
            setup_targets(t);
            random_init();
            rebuild_all();
            int r = sa_attempt(until, ITERS);
            if (r < 0) break;
            if (r == 1) {
                save_best(t);
                ok = 1;
            }
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    M_ = bestM;
    K_ = bestK;
    N = bestN;
    memcpy(PW, bestPW, sizeof(int) * (size_t)bestK);
    setup_targets(bestT);
    for (int s = 0; s < 2 * d; s++) {
        VS[s] = bestVS[s];
        VIS[s] = ginv(VS[s]);
    }
    rebuild_all();
    printf("%d %d\n", 4 * N, 2 * N * d);
    for (int a = 0; a < 2; a++)
        for (int x = 0; x < N; x++)
            for (int j = 0; j < d; j++) {
                int s = a * d + j;
                printf("%d %d\n", a * N + x, FW[s][x]);
            }
    return 0;
}
'''

# Parent engine (affine-group Haar lifts), kept verbatim as the fallback search.
C_SOURCE_HAAR = r'''
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
     * with fresh random starts, so the time left after the first pass is not wasted. */
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
    deadline = t0 + 0.9 * time_limit - 1.0
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

    mb = lib.moore_bound(d, D)

    # Bold new family: two-base voltage lifts over metacyclic groups (4N vertices).
    if d >= 3 and D >= 3:
        avail = deadline - time.monotonic()
        lift_budget = 0.55 * avail
        lo = max(best[0] // 4 + 1, mb // 15 + 1)
        hi = min(mb // 4, MAX_N_LIFT)
        if lift_budget > 2.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE_LIFT, [d, D, seed, round(lift_budget, 2), lo, hi],
                                 stdin_graph=None, timeout=lift_budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the best valid graph so far

    # Parent engine: affine-group Haar graphs, run with the leftover budget.
    if D >= 3 and d >= 2:
        budget = deadline - time.monotonic() - 2.0
        lo_p = max(best[0] // 2 + 1, mb // 8)
        hi_p = mb // 3
        if budget > 2.0 and lo_p <= hi_p:
            try:
                text = lib.run_c(C_SOURCE_HAAR, [d, D, seed, round(budget, 2), lo_p, hi_p],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
