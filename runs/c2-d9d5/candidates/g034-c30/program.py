"""Two-orbit affine Haar lifts for the bipartite degree-diameter problem.

New idea in this version: the parent's family is a single Haar graph on G = F_q x| H,
with one orbit per side and d connection elements. Here each side has MO = 1 or 2 orbits
of G, so the order is 2*MO*|G|. For MO = 2 the left orbits L^0, L^1 and right orbits
R^0, R^1 are joined by four connection sets of sizes x, d-x, d-x, x (1 <= x <= d-1), which
keeps every vertex at degree d. Left multiplication by G preserves every edge, so
distances from a vertex equal distances from its orbit representative. Diameter <= D
therefore reduces to 2*MO BFS runs, from L^a_e and R^b_e.

This gives orders 4|G| that the one-orbit family cannot reach. The C engine searches
candidate orders in ascending order of vertex count, with simulated annealing over the
connection elements. It cycles x across restarts.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Two-orbit affine Haar lift search.
 * Usage: prog d D seed time_limit loV hiV     (stdin ignored)
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
#define MAXN 4800
#define MAXD 32
#define MAXCAND 4096

typedef struct { int q, p, k, c, N, M, V; } Cand;

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

/* ------------------------------------------------------------ group G = F_q x| H */

static int GQ, GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Element (a, h_j) is coded a*c + j, with h_j = g^(j*(q-1)/c). */
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

/* ------------------------------------------------------------ two-orbit state */

static int MO;                       /* orbits per side: 1 or 2 */
static int B[2][MAXD];               /* target right orbit of slot (a,i) */
static int S[2][MAXD], Sinv[2][MAXD];
static int fwd[2][MAXD][MAXN], bwd[2][MAXD][MAXN];
static int rsa[2][MAXD], rsi[2][MAXD]; /* slots feeding right orbit b */
static int vis[4 * MAXN], que[4 * MAXN];
static int stampv = 0;
static int restart_ctr = 0;
static int bestx;
static int bestS[2][MAXD];

/* Vertices: L^a_g = a*GN + g, R^b_h = MO*GN + b*GN + h.
 * Slot (a,i) joins L^a_g to R^{B[a][i]}_{g*S[a][i]}. */
static void set_slot(int a, int i, int s) {
    S[a][i] = s;
    Sinv[a][i] = ginv(s);
    for (int g = 0; g < GN; g++) {
        fwd[a][i][g] = gmul(g, s);
        bwd[a][i][g] = gmul(g, Sinv[a][i]);
    }
}

static void setup_pattern(int x) {
    for (int a = 0; a < MO; a++)
        for (int i = 0; i < d; i++) {
            if (MO == 1) B[a][i] = 0;
            else if (a == 0) B[a][i] = (i < x) ? 0 : 1;
            else B[a][i] = (i < d - x) ? 0 : 1;
            S[a][i] = -1;
        }
    for (int b = 0; b < MO; b++) {
        int cnt = 0;
        for (int a = 0; a < MO; a++)
            for (int i = 0; i < d; i++)
                if (B[a][i] == b) { rsa[b][cnt] = a; rsi[b][cnt] = i; cnt++; }
    }
}

/* s is admissible for slot (a,i) if no other slot in the same (a, b) class has s. */
static int ok_s(int a, int i, int s) {
    for (int j = 0; j < d; j++)
        if (j != i && B[a][j] == B[a][i] && S[a][j] == s) return 0;
    return 1;
}

static void random_init(void) {
    for (int a = 0; a < MO; a++)
        for (int i = 0; i < d; i++) {
            int s;
            do { s = rndint(GN); } while (!ok_s(a, i, s));
            set_slot(a, i, s);
        }
}

/* Number of vertices within distance D of src. */
static int bfs_reach(int src) {
    int NL = MO * GN;
    stampv++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stampv;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < NL) {
                int a = v / GN, g = v - a * GN;
                for (int i = 0; i < d; i++) {
                    int u = NL + B[a][i] * GN + fwd[a][i][g];
                    if (vis[u] != stampv) { vis[u] = stampv; que[tail++] = u; }
                }
            } else {
                int w = v - NL, b = w / GN, h = w - b * GN;
                for (int j = 0; j < d; j++) {
                    int a = rsa[b][j], i = rsi[b][j];
                    int u = a * GN + bwd[a][i][h];
                    if (vis[u] != stampv) { vis[u] = stampv; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Orbit representatives suffice: the group acts regularly on each orbit by left
 * multiplication, which preserves all edges. */
static long cover_cost(void) {
    int V = 2 * MO * GN;
    long c = 0;
    for (int a = 0; a < MO; a++) c += V - bfs_reach(a * GN);
    for (int b = 0; b < MO; b++) c += V - bfs_reach(MO * GN + b * GN);
    return c;
}

/* Simulated annealing over the connection elements, with restarts cycling x. */
static int search_group(double until) {
    const int iters = 6000;
    while (now() < until) {
        int x = (MO == 1) ? d : 1 + (restart_ctr % (d - 1));
        restart_ctr++;
        setup_pattern(x);
        random_init();
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int a = rndint(MO), i = rndint(d), s;
            do { s = rndint(GN); } while (!ok_s(a, i, s));
            int old = S[a][i];
            set_slot(a, i, s);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_slot(a, i, old);
            }
        }
        if (cost == 0) {
            bestx = x;
            memcpy(bestS, S, sizeof S);
            return 1;
        }
    }
    return 0;
}

static void print_result(void) {
    int NL = MO * GN;
    printf("%d %d\n", 2 * NL, NL * d);
    setup_pattern(bestx);
    for (int a = 0; a < MO; a++)
        for (int i = 0; i < d; i++) set_slot(a, i, bestS[a][i]);
    for (int v = 0; v < NL; v++) {
        int a = v / GN, g = v - a * GN;
        for (int i = 0; i < d; i++)
            printf("%d %d\n", v, NL + B[a][i] * GN + fwd[a][i][g]);
    }
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
    long loV = atol(argv[5]), hiV = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 1; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            for (int M = 1; M <= 2; M++) {
                long N = (long)q * c;
                long V = 2L * M * N;
                if (N < 2L * d || N > MAXN) continue;
                if (V < loV || V > hiV) continue;
                if (nc < MAXCAND) {
                    Cand cd = {q, p, k, (int)c, (int)N, M, (int)V};
                    cand[nc++] = cd;
                }
            }
        }
    }
    for (int i = 1; i < nc; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].V > t.V) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = t;
    }

    /* Repeated passes in ascending order of vertex count. Each attempt gets 20% of
     * the remaining time (at least 1 s). Failed candidates are retried in later passes. */
    int bestV = 0, bestci = -1;
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            if (cand[ci].V <= bestV) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = 0.2 * rem;
            if (slice < 1.0) slice = 1.0;
            if (slice > rem) slice = rem;
            setup_group(cand[ci].q, cand[ci].p, cand[ci].k, cand[ci].c);
            MO = cand[ci].M;
            if (search_group(now() + slice)) {
                bestV = cand[ci].V;
                bestci = ci;
            }
        }
        if (!tried || t_end - now() < 0.3) break;
    }

    if (bestci < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(cand[bestci].q, cand[bestci].p, cand[bestci].k, cand[bestci].c);
    MO = cand[bestci].M;
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

    # Search: one- and two-orbit affine Haar lifts in a window of vertex counts.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, mb // 5)
        hi = mb // 3
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
