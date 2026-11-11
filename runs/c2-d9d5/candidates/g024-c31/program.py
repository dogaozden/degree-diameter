"""Affine and semidirect Haar lift search for the bipartite degree-diameter problem.

New in this version: a second group family in the C engine. The parent searches only
the affine groups F_q x| H, whose orders q*c (q a prime power, c | q-1) are sparse, so
the binary search sees few admissible orders near the frontier. This version also
searches the metacyclic groups Z_m x|_r Z_k with k <= 12 and r^k = 1 (mod m),
gcd(r, m) = 1, r != 1. Their orders m*k are dense, which gives the binary search
candidates just above the best affine order.

For either group G, take a d-element set S and the bipartite Haar graph on G with
L_g ~ R_{g s} for s in S. Left translations act transitively on each side, so the
diameter check needs only two BFS runs, from L_e and from R_e.

Candidates of both families are merged and sorted by order. Phase 1 is the same
binary search as the parent, with each probe given an equal share of the remaining
time. Phase 2 spends the leftover time on the next orders above the best.

Python keeps the projective-plane, Araujo-Lopez and W(q) baselines and the K_{d,d}
fallback. Every returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Haar lift search over affine groups F_q x| H and metacyclic groups Z_m x|_r Z_k.
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
#define MAXN 8192
#define MAXD 32
#define MAXK 12
#define MAXCAND 40000

typedef struct { int type, A, B, R, N; } Cand;
/* type 0: affine, A = q, B = c.  type 1: semidirect, A = m, B = k, R = r. */

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

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

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

/* ------------------------------------------------------------ group state */

static int GT = 0;                 /* 0 = affine, 1 = semidirect Z_m x| Z_k */
static int GN;
static int GQ, GC;                 /* affine: field size and |H| */
static int Hel[MAXQ], hidx[MAXQ], HM[MAXQ * MAXQ], PWG[MAXQ];
static int GM, GK, PWB[MAXQ];      /* semidirect: m, k, and r^b mod m */

/* Affine element (a, h_j) is coded as a*c + j, h_j = g^(j*(q-1)/c).
 * Product: (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). */
static void setup_affine(int q, int c) {
    int p, k;
    factor_pp(q, &p, &k);
    build_field(q, p, k);
    GT = 0;
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

/* Semidirect Z_m x| Z_k: element (a, b) coded a*k + b.
 * (a, b)(c, e) = (a + r^b c, b + e). Needs r^k = 1 (mod m). */
static void setup_semi(int m, int k, int r) {
    GT = 1;
    GM = m;
    GK = k;
    GN = m * k;
    PWB[0] = 1 % m;
    for (int b = 1; b < k; b++) PWB[b] = (PWB[b - 1] * r) % m;
}

static void setup_cand(const Cand *cd) {
    if (cd->type == 0) setup_affine(cd->A, cd->B);
    else setup_semi(cd->A, cd->B, cd->R);
}

static inline int gmul(int x, int y) {
    if (GT == 0) {
        int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
        int na = ADDT[a][MULT[Hel[j]][b]];
        return na * GC + HM[j * GC + t];
    }
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int na = (a + PWB[b] * c) % GM;
    return na * GK + (b + e) % GK;
}

static int ginv(int x) {
    if (GT == 0) {
        int a = x / GC, j = x % GC;
        int jn = (GC - j) % GC;
        int na = NEGT[MULT[Hel[jn]][a]];
        return na * GC + jn;
    }
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;               /* r^(-b) = r^(k-b) since r^k = 1 */
    int na = (GM - (PWB[nb] * a) % GM) % GM;
    return na * GK + nb;
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

/* Left translations are transitive on each side, so two BFS runs (from L_e and R_e)
 * decide the diameter. */
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

/* ------------------------------------------------------------ candidates */

static int cmpc(const void *x, const void *y) {
    const Cand *a = (const Cand *)x, *b = (const Cand *)y;
    if (a->N != b->N) return a->N - b->N;
    return a->type - b->type;
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

    /* Affine family: order q*c, q a prime power, c | q-1, c >= 2. */
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi || nc >= MAXCAND) continue;
            Cand cd = {0, q, c, 0, (int)N};
            cand[nc++] = cd;
        }
    }

    /* Semidirect family: Z_m x|_r Z_k with k <= MAXK, r^k = 1 (mod m), r != 1.
     * Up to two multipliers r per (m, k). Orders m*k are dense, unlike q*c. */
    for (int kk = 2; kk <= MAXK; kk++) {
        int mlo = (lo + kk - 1) / kk, mhi = hi / kk;
        if (mlo < 2) mlo = 2;
        for (int m = mlo; m <= mhi && nc < MAXCAND; m++) {
            int found = 0;
            for (int r = 2; r < m && found < 2; r++) {
                if (gcd_int(r, m) != 1) continue;
                int x = 1 % m;
                for (int i = 0; i < kk; i++) x = (x * r) % m;
                if (x != 1 % m) continue;
                Cand cd = {1, m, kk, r, m * kk};
                cand[nc++] = cd;
                found++;
            }
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmpc);

    int best_idx = -1, bestN = 0;

    /* Phase 1: binary search for the largest feasible order. The remaining time is
     * split evenly over the probes still needed, so early failures cannot starve
     * the probes near the frontier. */
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
        setup_cand(&cand[mid]);
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
        setup_cand(&cand[idx]);
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
    setup_cand(&cand[best_idx]);
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

    # Haar graphs over affine and semidirect groups. A graph on 2N vertices needs
    # N <= moore_bound / 2.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] // 2 + 1, mb // 8)
        hi = mb // 2
        if budget > 2.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
