"""Two-orbit affine lifts for the bipartite degree-diameter problem.

New construction in this version: multi-orbit group lifts over the affine group G = F_q x| H.
The parent uses one orbit per side (a Haar graph, L_g ~ R_{g s}). Here each side is split
into M = 2 orbits, L_{0,*}, L_{1,*}, R_{0,*}, R_{1,*}, each a copy of G. Left orbit i sends
A darts to right orbit 0 and d - A darts to right orbit 1 (right orbit 0 receives A from
L_0 and d - A from L_1, so all degrees are d). A dart (i, j, s) joins L_{i,g} to R_{j,g s}.
Each (i, j) pair uses distinct s values, so the graph is simple. Left translations
L_{i,g} -> L_{i,hg}, R_{j,k} -> R_{j,hk} are automorphisms, so one BFS per orbit
representative (2M BFS runs) decides diameter <= D. The lift has 4N vertices, so it can
beat the single-orbit record when N is larger than the single-orbit frontier divided by 2.

The C engine searches in two phases. Phase 1 is the parent's single-orbit affine Haar
search, which gives a safe baseline. Phase 2 searches two-orbit lifts with 4N > best
total, using a binary search over affine group orders with equal time slices per probe.
Every returned graph is checked with lib.is_valid, and K_{d,d}, projective-plane,
Araujo-Lopez and W(q) baselines remain as fallbacks.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit affine lift search.
 * Usage: prog d D seed time_limit lo hi mb     (stdin ignored)
 *   lo, hi: range of N for phase 1 (single orbit, total 2N).
 *   mb:     Moore bound, so phase 2 uses 4N <= mb.
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 1024
#define MAXC 1024
#define MAXN 8192
#define MAXD 32
#define MAXDART (2 * MAXD)
#define MAXCAND 8192

typedef struct { int q, p, k, c, N; } Cand;

static Cand cand[MAXCAND];
static int ncand = 0;

static int d, D;
static int M = 1;      /* number of left orbits = number of right orbits */
static int A = 1;      /* M == 2: left orbit 0 sends A darts to right orbit 0 */
static int NG = 0;     /* group order */
static int NDART = 0;  /* darts = M * d */
static double t_end;
static uint64_t rs = 88172645463325252ULL;

/* best solution so far */
static long bestTotal = 0;
static int bestValid = 0;
static int bq, bp, bk, bc, bM, bA;
static int bsv[MAXDART];

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

static int GQ, GC;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Element (a, h_j) is coded a*c + j with h_j = g^(j*(q-1)/c).
 * Product (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). Identity is code 0. */
static void setup_group(int q, int p, int k, int c) {
    build_field(q, p, k);
    GQ = q;
    GC = c;
    NG = q * c;
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

/* ------------------------------------------------------------ multi-orbit lift state */

static int sv[MAXDART], sinv[MAXDART], tgt[MAXDART], grp[MAXDART];
static int RL[2][MAXD];                 /* RL[j][r] = dart ids that end in right orbit j */
static int fwd[MAXDART][MAXN], bwd[MAXDART][MAXN];
static int vis[4 * MAXN], que[4 * MAXN];
static int stamp_ = 0;

/* Dart t = i*d + k leaves left orbit i and ends in right orbit tgt[t] with group label sv[t].
 * Edge L(i,g) - R(j, g*s). Right vertex R(j,h) reaches L(i, h*s^-1). */
static void set_dart(int t, int x) {
    sv[t] = x;
    sinv[t] = ginv(x);
    for (int g = 0; g < NG; g++) {
        fwd[t][g] = gmul(g, x);
        bwd[t][g] = gmul(g, sinv[t]);
    }
}

static void setup_darts(void) {
    NDART = M * d;
    for (int i = 0; i < M; i++)
        for (int k = 0; k < d; k++) {
            int t = i * d + k, j;
            if (M == 1) j = 0;
            else if (i == 0) j = (k < A) ? 0 : 1;
            else j = (k < d - A) ? 0 : 1;
            tgt[t] = j;
            grp[t] = i * M + j;
        }
    for (int j = 0; j < M; j++) {
        int cnt = 0;
        for (int t = 0; t < NDART; t++)
            if (tgt[t] == j && cnt < d) RL[j][cnt++] = t;
    }
}

/* Random labels with distinct values inside each (i, j) group (keeps the graph simple). */
static void random_darts(int N) {
    for (int t = 0; t < NDART; t++) {
        int x, ok;
        do {
            x = rndint(N);
            ok = 1;
            for (int t2 = 0; t2 < t; t2++)
                if (grp[t2] == grp[t] && sv[t2] == x) { ok = 0; break; }
        } while (!ok);
        set_dart(t, x);
    }
}

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int MN = M * NG;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < MN) {
                int i = v / NG, g = v - i * NG;
                for (int k = 0; k < d; k++) {
                    int t = i * d + k;
                    int u = MN + tgt[t] * NG + fwd[t][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int off = v - MN;
                int j = off / NG, h = off - j * NG;
                for (int r = 0; r < d; r++) {
                    int t = RL[j][r];
                    int u = (t / d) * NG + bwd[t][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left translations act transitively on each left orbit and right translations on each
 * right orbit, so one BFS per orbit representative decides diameter. */
static long cover_cost(void) {
    int MN = M * NG, V = 2 * MN;
    long c = 0;
    for (int i = 0; i < M; i++) c += (long)(V - bfs_count(i * NG));
    for (int j = 0; j < M; j++) c += (long)(V - bfs_count(MN + j * NG));
    return c;
}

/* Simulated annealing over the dart labels (and A when M == 2).
 * Returns 1 when cost 0 is reached (diameter <= D), 0 on timeout. */
static int search_group(double until) {
    const int iters = 8000;
    int N = NG;
    while (now() < until) {
        if (M == 2) A = 1 + rndint(d / 2);
        setup_darts();
        random_darts(N);
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int t = rndint(NDART);
            int x, ok, tries = 0;
            do {
                x = rndint(N);
                ok = 1;
                for (int t2 = 0; t2 < NDART; t2++)
                    if (t2 != t && grp[t2] == grp[t] && sv[t2] == x) { ok = 0; break; }
            } while (!ok && ++tries < 200);
            if (!ok) continue;
            int old = sv[t];
            set_dart(t, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_dart(t, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ search phases */

static Cand *cur_cand_ref;

static void record(int idx) {
    long total = 2L * M * NG;
    if (total <= bestTotal) return;
    bestTotal = total;
    bestValid = 1;
    bq = cand[idx].q;
    bp = cand[idx].p;
    bk = cand[idx].k;
    bc = cand[idx].c;
    bM = M;
    bA = A;
    memcpy(bsv, sv, sizeof(int) * (size_t)NDART);
}

/* Binary search over candidate group orders with N in [lo, hi] for the given orbit count. */
static void phase(int mm, int lo, int hi, double until) {
    int a = 0;
    while (a < ncand && cand[a].N < lo) a++;
    int b = ncand - 1;
    while (b >= 0 && cand[b].N > hi) b--;
    while (a <= b && now() < until) {
        int mid = (a + b) / 2;
        int span = b - a + 1, probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = until - now();
        double slice = rem / (probes + 1);
        if (slice < 0.5) slice = 0.5;
        if (slice > rem) slice = rem;
        M = mm;
        setup_group(cand[mid].q, cand[mid].p, cand[mid].k, cand[mid].c);
        if (search_group(now() + slice)) {
            record(mid);
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }
}

static void print_best(void) {
    setup_group(bq, bp, bk, bc);
    M = bM;
    A = bA;
    setup_darts();
    for (int t = 0; t < NDART; t++) set_dart(t, bsv[t]);
    int N = NG, MN = M * N;
    printf("%d %d\n", 2 * MN, MN * d);
    for (int i = 0; i < M; i++)
        for (int g = 0; g < N; g++)
            for (int k = 0; k < d; k++) {
                int t = i * d + k;
                printf("%d %d\n", i * N + g, (M + tgt[t]) * N + fwd[t][g]);
            }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    long mb = atol(argv[7]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }

    /* Candidate affine groups F_q x| H with q < MAXQ. Prime powers with k > 1 are limited
     * to q <= 256 because their modulus search is slower. */
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        if (k > 1 && q > 256) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N > MAXN || ncand >= MAXCAND) continue;
            Cand cd = {q, p, k, c, (int)N};
            cand[ncand++] = cd;
        }
    }
    for (int i = 1; i < ncand; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].N > t.N) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = t;
    }

    if (lo < 2 * d) lo = 2 * d;
    if (hi > MAXN) hi = MAXN;

    /* Phase 1: single-orbit affine Haar baseline (total 2N). */
    double T = t_end - t0;
    phase(1, lo, hi, t0 + 0.45 * T);

    /* Phase 2: two-orbit lifts with total 4N > best total, and 4N <= Moore bound. */
    int lo2 = bestValid ? (int)(bestTotal / 4 + 1) : 2 * d;
    if (lo2 < 2 * d) lo2 = 2 * d;
    long hi2 = mb / 4;
    if (hi2 > MAXN) hi2 = MAXN;
    if (lo2 <= hi2) phase(2, lo2, (int)hi2, t_end);

    if (!bestValid) {
        printf("0 0\n");
        return 0;
    }
    print_best();
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

    # Affine-group lifts: single-orbit Haar baseline plus two-orbit lifts (C engine).
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
        lo = max(best[0] // 2 + 1, mb // 8)
        hi = mb // 2
        if budget > 2.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi, mb],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
