"""Mixed-group Haar lift search for the bipartite degree-diameter problem.

New idea in this version: the parent searched only the affine groups F_q x| H,
which gives few admissible orders. This version adds the semidirect products
Z_m x|_r Z_k (r^k = 1 mod m, gcd(r, m) = 1), including cyclic groups (m = 1) and
abelian ones (r = 1). Every order N in [lo, hi] then has at least one candidate,
so the binary search runs over all orders, not only q*c.

For a graph on 2N vertices the C engine takes a group G of order N, a d-element
set S in G, and the bipartite Haar graph L_g ~ R_{g s}. Left translations are
automorphisms, so diameter <= D reduces to BFS from L_e and R_e. Simulated
annealing over S minimises the number of uncovered vertices.

Candidates are sorted by order. Each binary-search probe tries up to three
random candidates of that order and splits its time slice across them. Phase 2
then explores the orders above the best one. The Python side keeps the
projective-plane, Araujo-Lopez, W(q) and K_{d,d} baselines, and every returned
graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Mixed-group Haar lift search.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * Groups: affine F_q x| H (type 0) and semidirect Z_m x|_r Z_k (type 1).
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
#define MAXCAND 40000
#define TRIES 3

typedef struct { int type, a1, a2, a3, a4, N; } Cand;

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

/* ------------------------------------------------------------ groups */

static int GTYPE = 0;   /* 0 = affine F_q x| H, 1 = semidirect Z_m x|_r Z_k */
static int GN;

/* affine state */
static int GQ, GC;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

static void setup_affine(int q, int p, int k, int c) {
    build_field(q, p, k);
    GTYPE = 0;
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

static inline int aff_mul(int x, int y) {
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static int aff_inv(int x) {
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

/* semidirect state: element (a, b) is coded a*SK + b; (a,b)(c,e) = (a + r^b c, b + e) */
static int SM, SK, SR;
static int PWS[MAXN];   /* PWS[b] = r^b mod m */

static void setup_semi(int m, int k, int r) {
    GTYPE = 1;
    SM = m;
    SK = k;
    SR = r;
    GN = m * k;
    long v = 1 % m;
    for (int b = 0; b < k; b++) {
        PWS[b] = (int)v;
        v = (v * r) % m;
    }
}

static inline int semi_mul(int x, int y) {
    int a = x / SK, b = x % SK, c = y / SK, e = y % SK;
    int na = (int)(((long)a + (long)PWS[b] * c) % SM);
    int nb = (b + e) % SK;
    return na * SK + nb;
}

static int semi_inv(int x) {
    int a = x / SK, b = x % SK;
    int nb = (SK - b) % SK;
    int na = (int)((SM - ((long)PWS[nb] * a) % SM) % SM);
    return na * SK + nb;
}

static inline int gmul(int x, int y) {
    return GTYPE == 0 ? aff_mul(x, y) : semi_mul(x, y);
}
static inline int ginv(int x) {
    return GTYPE == 0 ? aff_inv(x) : semi_inv(x);
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

/* Left translations are automorphisms, so BFS from L_e and R_e decide the diameter. */
static long cover_cost(void) {
    int V = 2 * GN;
    return (long)(V - bfs_count(0)) + (long)(V - bfs_count(GN));
}

static int in_S(int x, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == x) return 1;
    return 0;
}

/* Simulated annealing over S (size d) in the current group. Returns 1 at cost 0. */
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

static Cand cand[MAXCAND];
static int nc = 0;
static long seen_cnt = 0;

/* Reservoir sampling keeps a uniform subset when there are too many candidates. */
static void add_cand(int type, int a1, int a2, int a3, int a4, int N) {
    Cand cd = {type, a1, a2, a3, a4, N};
    seen_cnt++;
    if (nc < MAXCAND) { cand[nc++] = cd; return; }
    long j = (long)(rnd() % (uint64_t)seen_cnt);
    if (j < MAXCAND) cand[j] = cd;
}

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod_int(int b, int e, int m) {
    long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static void setup_cand(const Cand *cd) {
    if (cd->type == 0) setup_affine(cd->a1, cd->a2, cd->a3, cd->a4);
    else setup_semi(cd->a1, cd->a2, cd->a3);
}

static int cmpc(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    return (x->N > y->N) - (x->N < y->N);
}

static int ordv[MAXCAND], ords[MAXCAND], ordc[MAXCAND], nord = 0;

/* Try up to TRIES random candidates of the given order, sharing the slice.
 * On success returns the candidate index and leaves the graph set in bestS. */
static int probe_order(int oi, double slice) {
    int cnt = ordc[oi], st = ords[oi];
    int tries = cnt < TRIES ? cnt : TRIES;
    double until0 = now() + slice;
    for (int t = 0; t < tries; t++) {
        double left = until0 - now();
        if (left <= 0) break;
        double per = left / (tries - t);
        int ci = st + rndint(cnt);
        setup_cand(&cand[ci]);
        if (search_group(now() + per)) {
            memcpy(bestS, S, sizeof(int) * (size_t)d);
            return ci;
        }
    }
    return -1;
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
    t_end = now() + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (hi > MAXN) hi = MAXN;
    if (lo < 2 * d) lo = 2 * d;
    if (lo > hi) { printf("0 0\n"); return 0; }

    /* Affine candidates F_q x| H with q prime power, c | q-1, c >= 2. */
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            add_cand(0, q, p, k, c, (int)N);
        }
    }

    /* Semidirect candidates Z_m x|_r Z_k, m*k in [lo, hi].
     * m = 1 gives the cyclic group Z_k; r = 1 gives the abelian group. */
    for (int m = 1; 2 * m <= hi; m++) {
        for (int k = 2; (long)m * k <= hi; k++) {
            int N = m * k;
            if (N < lo) continue;
            if (m == 1) { add_cand(1, 1, k, 0, 0, N); continue; }
            for (int r = 1; r < m; r++) {
                if (gcd_int(r, m) != 1) continue;
                if (powmod_int(r, k, m) != 1) continue;
                add_cand(1, m, k, r, 0, N);
            }
        }
    }
    if (nc == 0) { printf("0 0\n"); return 0; }

    qsort(cand, (size_t)nc, sizeof(Cand), cmpc);
    for (int i = 0; i < nc; i++) {
        if (i == 0 || cand[i].N != cand[i - 1].N) {
            ordv[nord] = cand[i].N;
            ords[nord] = i;
            ordc[nord] = 0;
            nord++;
        }
        ordc[nord - 1]++;
    }

    int best_c = -1, best_ord = -1, bestN = 0;

    /* Phase 1: binary search over the distinct orders. Each probe gets an equal
     * share of the remaining time over the probes still needed. */
    int a = 0, b = nord - 1;
    while (a <= b && now() < t_end) {
        int mid = (a + b) / 2;
        int span = b - a + 1, probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = t_end - now();
        if (rem <= 0) break;
        double slice = rem / (probes + 1);
        if (slice < 0.5) slice = 0.5;
        if (slice > rem) slice = rem;
        int ci = probe_order(mid, slice);
        if (ci >= 0) {
            bestN = ordv[mid];
            best_c = ci;
            best_ord = mid;
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }

    /* Phase 2: spend the leftover time on the next orders above the best. */
    int fails = 0;
    int oi = best_ord + 1;
    while (oi < nord && now() < t_end && fails < 2) {
        double rem = t_end - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        int ci = probe_order(oi, slice);
        if (ci >= 0) {
            bestN = ordv[oi];
            best_c = ci;
            best_ord = oi;
            fails = 0;
        } else {
            fails++;
        }
        oi++;
    }

    if (best_c < 0) { printf("0 0\n"); return 0; }
    setup_cand(&cand[best_c]);
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

    # Mixed-group Haar graphs: a graph on 2N vertices needs N <= moore_bound / 2.
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
