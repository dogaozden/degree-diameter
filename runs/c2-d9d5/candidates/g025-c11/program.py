"""Two-stage search for the bipartite degree-diameter problem.

Stage 1 (new family): 4-fibre cyclic voltage lifts. The base graph has two A-fibres
and two B-fibres. Each A-fibre vertex has d darts, and the dart counts between the
fibres are a, d-a, d-a, a (1 <= a <= d/2, so the base is connected). Each dart
carries a voltage in Z_N, and darts between the same pair of fibres need distinct
voltages, so the lift is simple. The lift has 4N vertices, is d-regular and
bipartite. Translations act transitively on each fibre, so diameter <= D reduces to
four BFS runs, one from a vertex of each fibre. Annealing searches the voltages for
each N in ascending order from just above the incumbent.

Stage 2 (parent family, kept as a safety net): affine-group Haar lifts over F_q x| H.
It runs only if stage 1 did not improve on the incumbent.

Every candidate goes through lib.is_valid before it is kept. K_{d,d} is the fallback.
"""
import itertools
import time

import lib

LIFT_SOURCE = r'''
/* 4-fibre cyclic voltage lift search.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * Fibres: A0 = [0,N), A1 = [N,2N), B0 = [2N,3N), B1 = [3N,4N).
 * Darts k in [0,d) start in A0, darts in [d,2d) start in A1.
 * Dart k joins A(i,x) to B(DBi[k], x + VOLT[k]).
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXD2 64
#define MAXN 4096

static int d, D, N;
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

static int DAi[MAXD2], DBi[MAXD2], VOLT[MAXD2], solV[MAXD2];
static int LB[2][MAXD];
static int vis[4 * MAXN], que[4 * MAXN];
static int stamp_ = 0;

/* Split a: pairs (A0,B0) a darts, (A0,B1) d-a, (A1,B0) d-a, (A1,B1) a. */
static void setup_split(int a) {
    for (int k = 0; k < 2 * d; k++) {
        if (k < d) {
            DAi[k] = 0;
            DBi[k] = (k < a) ? 0 : 1;
        } else {
            int kk = k - d;
            DAi[k] = 1;
            DBi[k] = (kk < d - a) ? 0 : 1;
        }
    }
    int c0 = 0, c1 = 0;
    for (int k = 0; k < 2 * d; k++) {
        if (DBi[k] == 0) LB[0][c0++] = k;
        else LB[1][c1++] = k;
    }
}

/* Voltage v is allowed for dart k if no other dart in the same pair uses it. */
static int volt_ok(int k, int v) {
    for (int m = 0; m < 2 * d; m++)
        if (m != k && DAi[m] == DAi[k] && DBi[m] == DBi[k] && VOLT[m] == v)
            return 0;
    return 1;
}

/* Number of vertices within distance D of src. */
static int reach_count(int src) {
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < 2 * N) {
                int i = v / N, x = v - i * N;
                for (int t = 0; t < d; t++) {
                    int k = i * d + t;
                    int s = x + VOLT[k];
                    if (s >= N) s -= N;
                    int u = 2 * N + DBi[k] * N + s;
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int j = (v - 2 * N) / N;
                int y = v - 2 * N - j * N;
                for (int t = 0; t < d; t++) {
                    int k = LB[j][t];
                    int s = y - VOLT[k];
                    if (s < 0) s += N;
                    int u = DAi[k] * N + s;
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Translations act transitively on each fibre, so one source per fibre suffices. */
static long cost_fn(void) {
    int V = 4 * N;
    long c = 0;
    c += V - reach_count(0);
    c += V - reach_count(N);
    c += V - reach_count(2 * N);
    c += V - reach_count(3 * N);
    return c;
}

static void random_init(void) {
    for (int k = 0; k < 2 * d; k++) VOLT[k] = -1;
    for (int k = 0; k < 2 * d; k++) {
        int v;
        do { v = rndint(N); } while (!volt_ok(k, v));
        VOLT[k] = v;
    }
}

/* Iterated annealing for one split a. Returns 1 on cost 0 (solution in solV). */
static int search_split(int a, double until) {
    setup_split(a);
    int have = 0;
    long bestc = 0;
    int bestV[MAXD2];
    while (now() < until) {
        if (!have) {
            random_init();
        } else {
            memcpy(VOLT, bestV, sizeof(int) * (size_t)(2 * d));
            for (int t = 0; t < 3; t++) {
                int k = rndint(2 * d), v;
                do { v = rndint(N); } while (!volt_ok(k, v));
                VOLT[k] = v;
            }
        }
        long cost = cost_fn();
        if (cost == 0) {
            memcpy(solV, VOLT, sizeof(int) * (size_t)(2 * d));
            return 1;
        }
        double c0 = (double)cost;
        double Ts = (have ? 0.05 : 0.2) * c0 + 1.0, Te = 0.2;
        const int iters = 6000;
        for (int it = 0; it < iters; it++) {
            if ((it & 31) == 0 && now() > until) break;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int k = rndint(2 * d), v;
            int old = VOLT[k];
            do { v = rndint(N); } while (!volt_ok(k, v));
            VOLT[k] = v;
            long c2 = cost_fn();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else VOLT[k] = old;
            if (cost == 0) break;
        }
        if (cost == 0) {
            memcpy(solV, VOLT, sizeof(int) * (size_t)(2 * d));
            return 1;
        }
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(bestV, VOLT, sizeof(int) * (size_t)(2 * d));
        }
    }
    return 0;
}

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

    if (d < 3 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (hi > MAXN) hi = MAXN;
    if (lo < d) lo = d;

    int bestN = 0, bestA = 0;
    static int bestV[MAXD2];
    /* Ascending N: each success moves on to a larger N with the remaining time. */
    for (int n = lo; n <= hi && now() < t_end; n++) {
        N = n;
        int found = 0;
        for (int a = 1; a <= d / 2 && !found; a++) {
            double rem = t_end - now();
            if (rem < 0.2) break;
            double slice = 0.1 * rem;
            if (slice < 0.5) slice = 0.5;
            if (slice > rem) slice = rem;
            if (search_split(a, now() + slice)) {
                found = 1;
                bestN = n;
                bestA = a;
                memcpy(bestV, solV, sizeof(int) * (size_t)(2 * d));
            }
        }
    }

    if (!bestN) {
        printf("0 0\n");
        return 0;
    }
    N = bestN;
    setup_split(bestA);
    memcpy(VOLT, bestV, sizeof(int) * (size_t)(2 * d));
    printf("%d %d\n", 4 * N, 2 * N * d);
    for (int i = 0; i < 2; i++)
        for (int x = 0; x < N; x++)
            for (int t = 0; t < d; t++) {
                int k = i * d + t;
                int s = x + VOLT[k];
                if (s >= N) s -= N;
                printf("%d %d\n", i * N + x, 2 * N + DBi[k] * N + s);
            }
    return 0;
}
'''

C_SOURCE = r'''
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

/* Iterated annealing over the connection set S of size d in the current group.
 * The first round starts from a random set. Later rounds start from the incumbent
 * (the lowest-cost set seen so far) with two elements replaced, at a lower starting
 * temperature, so time concentrates near good sets.
 * Returns 1 when cost 0 is reached (diameter <= D), 0 on timeout. */
static int search_group(double until) {
    int N = GN;
    const int iters = 8000;
    int have = 0;
    long bestc = 0;
    int incS[MAXD];
    while (now() < until) {
        if (!have) {
            for (int i = 0; i < d; i++) {
                int x;
                do { x = rndint(N); } while (in_S(x, i));
                set_s(i, x);
            }
        } else {
            for (int i = 0; i < d; i++) set_s(i, incS[i]);
            for (int t = 0; t < 2; t++) {
                int i = rndint(d), x;
                do { x = rndint(N); } while (in_S(x, d));
                set_s(i, x);
            }
        }
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
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
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(incS, S, sizeof(int) * (size_t)d);
        }
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

    /* Ascending order from lo: the smallest orders above the current best are the
     * ones that can beat the record, so each attempt gets 20% of the remaining time
     * (at least 1 s). Failed attempts shrink the pool only slowly. */
    int best_idx = -1, bestN = 0;
    for (int ci = 0; ci < nc; ci++) {
        double rem = t_end - now();
        if (rem < 0.3) break;
        if (cand[ci].N <= bestN) continue;
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

    def remaining():
        return 0.88 * time_limit - (time.monotonic() - t0) - 2.0

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

        # Stage 1 (new family): 4-fibre cyclic voltage lifts, order 4N.
        before = best[0]
        budget = remaining()
        lo = max(best[0] // 4 + 1, mb // 16, d)
        hi = mb // 4
        if d >= 3 and budget > 3.0 and lo <= hi:
            b1 = round(0.6 * budget, 2)
            try:
                text = lib.run_c(LIFT_SOURCE, [d, D, seed, b1, lo, hi],
                                 stdin_graph=None, timeout=b1 + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass

        # Stage 2 (parent family): affine Haar lifts, only if stage 1 did not improve.
        if best[0] == before:
            budget = remaining()
            lo2 = max(best[0] // 2 + 1, mb // 8)
            hi2 = mb // 3
            if budget > 2.0 and lo2 <= hi2:
                try:
                    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo2, hi2],
                                     stdin_graph=None, timeout=budget + 8.0)
                    consider(lib.parse_graph_text(text))
                except Exception:
                    pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
