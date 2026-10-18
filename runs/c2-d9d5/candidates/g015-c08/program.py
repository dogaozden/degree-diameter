"""Two-block bi-Cayley lifts over affine groups, with the single-block Haar search as fallback.

Family 1 (new): for a prime power q and c | q-1, G = F_q x| H (|G| = q*c). Left vertices
(i, g) and right vertices (j, h) for i, j in {0, 1}. Block pair (i, j) uses a connection set
S_ij, with (i, g) ~ (j, g*s) for s in S_ij. Sizes |S_ij| form the matrix [[a, d-a], [d-a, a]],
so every vertex has degree d. The graph has 4|G| vertices. Left translations preserve every
block, so diameter <= D reduces to four BFS runs, one from each block's identity.

Family 2 (parent): single-block Haar graph on G, 2|G| vertices.

The C engine is shared: argument M selects 1 or 2 blocks per side. The annealing is iterated:
each round perturbs the incumbent connection sets and anneals from there at a lower temperature.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-block affine-group lift search.
 * Usage: prog d D seed time_limit lo hi M     (stdin ignored)
 * M = 1: Haar graph on G (2|G| vertices). M = 2: bi-Cayley lift with 2 blocks per side (4|G| vertices).
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
#define MAXN 4096
#define MAXD 16
#define MAXM 2
#define MAXCAND 8192

typedef struct { int q, p, k, c, N; } Cand;

static int d, D, M;
static int A[MAXM][MAXM];          /* A[i][j] = number of connection elements in block pair (i, j) */
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
                if (polymul(a, b, p, k, pw, m) == 0) ok = 0;
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

/* Element (a, h_j) is coded a*c + j with h_j = g^(j*(q-1)/c).
 * Product: (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). */
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

/* ------------------------------------------------------------ bi-Cayley state
 * Left (i, g) = i*N + g. Right (j, h) = M*N + j*N + h.
 * (i, g) ~ (j, g*s) for s = ST[i][j][t], t < A[i][j].
 * Right (j, h) ~ (i, h*s^-1). */

static int ST[MAXM][MAXM][MAXD], SI[MAXM][MAXM][MAXD];
static int FW[MAXM][MAXM][MAXD][MAXN], BW[MAXM][MAXM][MAXD][MAXN];
static int incST[MAXM][MAXM][MAXD], bestST[MAXM][MAXM][MAXD];
static int vis[2 * MAXM * MAXN], que[2 * MAXM * MAXN];
static int stamp_ = 0;

static void set_elem(int i, int j, int t, int x) {
    ST[i][j][t] = x;
    SI[i][j][t] = ginv(x);
    for (int g = 0; g < GN; g++) {
        FW[i][j][t][g] = gmul(g, x);
        BW[i][j][t][g] = gmul(g, SI[i][j][t]);
    }
}

/* Is x among the first `upto` elements of block pair (i, j)? */
static int in_block(int i, int j, int x, int upto) {
    for (int t = 0; t < upto; t++)
        if (ST[i][j][t] == x) return 1;
    return 0;
}

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int NN = GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < M * NN) {
                int i = v / NN, g = v % NN;
                for (int j = 0; j < M; j++)
                    for (int t = 0; t < A[i][j]; t++) {
                        int u = M * NN + j * NN + FW[i][j][t][g];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
            } else {
                int r = v - M * NN, j = r / NN, h = r % NN;
                for (int i = 0; i < M; i++)
                    for (int t = 0; t < A[i][j]; t++) {
                        int u = i * NN + BW[i][j][t][h];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
            }
        }
    }
    return tail;
}

/* Block translations are automorphisms, so one BFS per block (2M sources) decides diameter. */
static long cover_cost(void) {
    int NN = GN, V = 2 * M * NN;
    long c = 0;
    for (int b = 0; b < M; b++) {
        c += (long)(V - bfs_count(b * NN));
        c += (long)(V - bfs_count(M * NN + b * NN));
    }
    return c;
}

static void random_init(void) {
    for (int i = 0; i < M; i++)
        for (int j = 0; j < M; j++)
            for (int t = 0; t < A[i][j]; t++) {
                int x;
                do { x = rndint(GN); } while (in_block(i, j, x, t));
                set_elem(i, j, t, x);
            }
}

/* Iterated annealing. Round 1 starts from a random configuration; later rounds start from the
 * incumbent with two elements replaced, at a lower starting temperature.
 * Returns 1 when cost 0 is reached (state left valid), 0 on timeout. */
static int search(double until) {
    const int iters = 6000;
    int have = 0;
    long bestc = 0;
    while (now() < until) {
        if (!have) {
            random_init();
        } else {
            for (int i = 0; i < M; i++)
                for (int j = 0; j < M; j++)
                    for (int t = 0; t < A[i][j]; t++)
                        set_elem(i, j, t, incST[i][j][t]);
            for (int r = 0; r < 2; r++) {
                int i = rndint(M), j = rndint(M), t = rndint(A[i][j]);
                int x;
                do { x = rndint(GN); } while (in_block(i, j, x, A[i][j]));
                set_elem(i, j, t, x);
            }
        }
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(M), j = rndint(M), t = rndint(A[i][j]);
            int x;
            do { x = rndint(GN); } while (in_block(i, j, x, A[i][j]));
            int old = ST[i][j][t];
            set_elem(i, j, t, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_elem(i, j, t, old);
            }
        }
        if (cost == 0) return 1;
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(incST, ST, sizeof(ST));
        }
    }
    return 0;
}

static void print_result(void) {
    int NN = GN;
    printf("%d %d\n", 2 * M * NN, M * NN * d);
    for (int i = 0; i < M; i++)
        for (int g = 0; g < NN; g++)
            for (int j = 0; j < M; j++)
                for (int t = 0; t < A[i][j]; t++)
                    printf("%d %d\n", i * NN + g, M * NN + j * NN + FW[i][j][t][g]);
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
    M = (argc >= 8) ? atoi(argv[7]) : 1;
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (M != 1 && M != 2) { printf("0 0\n"); return 0; }
    if (M == 2 && d < 2) { printf("0 0\n"); return 0; }

    memset(A, 0, sizeof(A));
    if (M == 1) {
        A[0][0] = d;
    } else {
        int a = (d + 1) / 2;
        A[0][0] = a;
        A[1][1] = a;
        A[0][1] = d - a;
        A[1][0] = d - a;
    }

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

    /* Ascending order: each attempt gets 20% of the remaining time (at least 1 s). */
    int best_idx = -1, bestN = 0;
    for (int ci = 0; ci < nc; ci++) {
        double rem = t_end - now();
        if (rem < 0.3) break;
        if (cand[ci].N <= bestN) continue;
        double slice = 0.2 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_group(cand[ci].q, cand[ci].p, cand[ci].k, cand[ci].c);
        if (search(now() + slice)) {
            bestN = GN;
            best_idx = ci;
            memcpy(bestST, ST, sizeof(ST));
        }
    }

    if (best_idx < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(cand[best_idx].q, cand[best_idx].p, cand[best_idx].k, cand[best_idx].c);
    for (int i = 0; i < M; i++)
        for (int j = 0; j < M; j++)
            for (int t = 0; t < A[i][j]; t++)
                set_elem(i, j, t, bestST[i][j][t]);
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


def _run_engine(d, D, seed, budget, lo, hi, M):
    """Run the C engine with M blocks per side; returns a parsed (n, edges) or None."""
    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi, M],
                     stdin_graph=None, timeout=budget + 8.0)
    return lib.parse_graph_text(text)


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

        # Stage 1 (new family): two-block bi-Cayley lift, 4|G| vertices.
        budget1 = 0.7 * (0.88 * time_limit - (time.monotonic() - t0) - 2.0)
        lo1 = max(mb // 16, 2 * d)
        hi1 = min(mb // 4, 4096)
        if budget1 > 2.0 and lo1 <= hi1:
            try:
                consider(_run_engine(d, D, seed, budget1, lo1, hi1, 2))
            except Exception:
                pass   # keep the valid graph found so far

        # Stage 2 (fallback family): single-block Haar lift, 2|G| vertices, with the remaining time.
        budget2 = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        lo2 = max(best[0] // 2 + 1, mb // 8)
        hi2 = min(mb // 3, 4096)
        if budget2 > 2.0 and lo2 <= hi2:
            try:
                consider(_run_engine(d, D, seed + 1, budget2, lo2, hi2, 1))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
