"""Multi-vertex affine voltage lifts for the bipartite degree-diameter problem.

Change from the parent: instead of one Haar graph (base = 2 vertices joined by d
parallel darts), this version searches lifts of a d-regular bipartite base multigraph
with r A-vertices and r B-vertices. Each base dart k from A_i to B_{sigma_k(i)} carries
a voltage g in G = F_q x| H, where sigma_k are permutations of [r]. The lift has
vertices (A,i,x) and (B,j,y) for x,y in G, and edges (A,i,x)~(B,j,x*g). Left
multiplication by G is an automorphism that acts regularly on each fiber, so the
diameter is at most D iff every one of the 2r sources (A,i,e) and (B,j,e) reaches
all 2rN vertices within D steps. The search anneals voltages (cost = total number of
unreached (source, vertex) pairs) and iterates from the incumbent, as in the parent.
Order is 2rN, so r = 1 reproduces the parent's Haar family and r >= 2 adds new orders.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-vertex affine voltage lift search.
 * Usage: prog d D seed time_limit lo hi rmax     (stdin ignored)
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
#define MAXR 4
#define MAXD 32
#define MAXN 8192
#define MAXV 65536
#define MAXCAND 8192
#define ITERS 4000

typedef struct { int q, p, k, c, N, r, T; } Cand;

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

/* Element (a, h_j) is coded as a*c + j, with h_j = g^(j*(q-1)/c).
 * Product: (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). Identity is code 0. */
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

/* ------------------------------------------------------------ voltage lift state */

/* Base: R A-vertices and R B-vertices, d darts per A-vertex (dart k goes from A_i to
 * B_{sig[k][i]}), so each B-vertex also has exactly d darts (sinv[k][j] is its A-end). */
static int R, NN;
static int sig[MAXD][MAXR], sinv[MAXD][MAXR];
static int volt[MAXR][MAXD], vinv[MAXR][MAXD];
static int incSig[MAXD][MAXR], incVolt[MAXR][MAXD];
static int bestSig[MAXD][MAXR], bestVolt[MAXR][MAXD];
static int vis[MAXV], que[MAXV];
static int stampc = 0;

static void refresh_sinv(void) {
    for (int k = 0; k < d; k++)
        for (int i = 0; i < R; i++) sinv[k][sig[k][i]] = i;
}

static void refresh_vinv(void) {
    for (int i = 0; i < R; i++)
        for (int k = 0; k < d; k++) vinv[i][k] = ginv(volt[i][k]);
}

static void set_volt(int i, int k, int x) {
    volt[i][k] = x;
    vinv[i][k] = ginv(x);
}

/* 1 if some other dart from A_i to the same B-vertex already has voltage x:
 * parallel lift edges would then be duplicates. */
static int conflict(int i, int k, int x) {
    for (int k2 = 0; k2 < d; k2++)
        if (k2 != k && sig[k2][i] == sig[k][i] && volt[i][k2] == x) return 1;
    return 0;
}

static void random_perms(void) {
    for (int k = 0; k < d; k++) {
        int p[MAXR];
        for (int i = 0; i < R; i++) p[i] = i;
        if (k > 0)
            for (int i = R - 1; i > 0; i--) {
                int j = rndint(i + 1), t = p[i];
                p[i] = p[j];
                p[j] = t;
            }
        for (int i = 0; i < R; i++) sig[k][i] = p[i];
    }
    refresh_sinv();
}

static int random_volts(void) {
    for (int i = 0; i < R; i++)
        for (int k = 0; k < d; k++) volt[i][k] = -1;
    for (int i = 0; i < R; i++)
        for (int k = 0; k < d; k++) {
            int ok = 0;
            for (int t = 0; t < 20000 && !ok; t++) {
                int x = rndint(NN);
                if (!conflict(i, k, x)) { volt[i][k] = x; ok = 1; }
            }
            if (!ok) return 0;
        }
    refresh_vinv();
    return 1;
}

static void load_incumbent(void) {
    memcpy(sig, incSig, sizeof sig);
    memcpy(volt, incVolt, sizeof volt);
    refresh_sinv();
    refresh_vinv();
}

/* Vertices: A(i,x) = i*NN + x; B(j,y) = R*NN + j*NN + y.
 * Edge A(i,x) ~ B(sig[k][i], x*volt[i][k]) for each dart k.
 * Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int RN = R * NN;
    stampc++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stampc;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < RN) {
                int i = v / NN, x = v - i * NN;
                for (int k = 0; k < d; k++) {
                    int j = sig[k][i];
                    int u = RN + j * NN + gmul(x, volt[i][k]);
                    if (vis[u] != stampc) { vis[u] = stampc; que[tail++] = u; }
                }
            } else {
                int w = v - RN, j = w / NN, y = w - j * NN;
                for (int k = 0; k < d; k++) {
                    int i = sinv[k][j];
                    int u = i * NN + gmul(y, vinv[i][k]);
                    if (vis[u] != stampc) { vis[u] = stampc; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left translations act regularly on each fiber, so eccentricities are constant on
 * fibers. The diameter is <= D iff the 2R fiber representatives reach everything. */
static long cover_cost(void) {
    int V = 2 * R * NN, RN = R * NN;
    long c = 0;
    for (int i = 0; i < R; i++) c += (long)(V - bfs_count(i * NN));
    for (int j = 0; j < R; j++) c += (long)(V - bfs_count(RN + j * NN));
    return c;
}

/* Iterated annealing over voltages (and occasionally the base permutations).
 * The first round, and every fifth round, starts from a fresh random lift. Other rounds
 * start from the incumbent with two voltages replaced, at a lower start temperature.
 * Returns 1 with the successful lift left in sig/volt, 0 on timeout or failure. */
static int search_cand(double until) {
    int have = 0;
    long bestc = 0;
    int rounds = 0;
    while (now() < until) {
        int fresh = !have || (rounds % 5 == 4);
        if (fresh) {
            random_perms();
            if (!random_volts()) return 0;
        } else {
            load_incumbent();
            for (int t = 0; t < 2; t++) {
                int i = rndint(R), k = rndint(d), x = -1;
                for (int tr = 0; tr < 1000; tr++) {
                    int y = rndint(NN);
                    if (!conflict(i, k, y)) { x = y; break; }
                }
                if (x >= 0) set_volt(i, k, x);
            }
        }
        rounds++;
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (fresh ? 0.05 : 0.02) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < ITERS && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double temp = Ts * pow(Te / Ts, (double)it / ITERS);
            int i = rndint(R), k = rndint(d), x = -1;
            for (int tr = 0; tr < 200; tr++) {
                int y = rndint(NN);
                if (!conflict(i, k, y)) { x = y; break; }
            }
            if (x < 0) continue;
            int old = volt[i][k];
            set_volt(i, k, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) cost = c2;
            else set_volt(i, k, old);
        }
        if (cost == 0) return 1;
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(incSig, sig, sizeof sig);
            memcpy(incVolt, volt, sizeof volt);
        }
    }
    return 0;
}

static void print_best(const Cand *cd) {
    setup_group(cd->q, cd->p, cd->k, cd->c);
    R = cd->r;
    NN = cd->N;
    memcpy(sig, bestSig, sizeof sig);
    memcpy(volt, bestVolt, sizeof volt);
    refresh_sinv();
    refresh_vinv();
    int RN = R * NN;
    printf("%d %d\n", 2 * RN, RN * d);
    for (int i = 0; i < R; i++)
        for (int x = 0; x < NN; x++)
            for (int k = 0; k < d; k++)
                printf("%d %d\n", i * NN + x, RN + sig[k][i] * NN + gmul(x, volt[i][k]));
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
    int lo = atoi(argv[5]), hi = atoi(argv[6]), rmax = atoi(argv[7]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (rmax < 1) rmax = 1;
    if (rmax > MAXR) rmax = MAXR;
    if (hi > MAXV) hi = MAXV;
    if (lo < 2 * d) lo = 2 * d;

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 1; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            int N = q * c;
            if (N > MAXN || N < d) continue;
            for (int r = 1; r <= rmax; r++) {
                int T = 2 * r * N;
                if (T < lo || T > hi) continue;
                if (nc < MAXCAND) {
                    Cand cd = {q, p, k, c, N, r, T};
                    cand[nc++] = cd;
                }
            }
        }
    }
    for (int i = 1; i < nc; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].T > t.T) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = t;
    }

    /* Ascending order from lo: each attempt gets a share of the remaining time, and
     * a success raises the bar so only larger orders are tried afterwards. */
    int bestci = -1, bestT = 0;
    for (int ci = 0; ci < nc; ci++) {
        if (cand[ci].T <= bestT) continue;
        double rem = t_end - now();
        if (rem < 0.5) break;
        double slice = 0.12 * rem;
        if (slice < 1.5) slice = 1.5;
        if (slice > rem) slice = rem;
        setup_group(cand[ci].q, cand[ci].p, cand[ci].k, cand[ci].c);
        R = cand[ci].r;
        NN = cand[ci].N;
        if (search_cand(now() + slice)) {
            bestT = cand[ci].T;
            bestci = ci;
            memcpy(bestSig, sig, sizeof sig);
            memcpy(bestVolt, volt, sizeof volt);
        }
    }

    if (bestci < 0) {
        printf("0 0\n");
        return 0;
    }
    print_best(&cand[bestci]);
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


RMAX = 3  # number of base vertices per side tried by the C search


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

    # Search: multi-vertex affine voltage lifts, in the order-range just above the record.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, int(0.25 * mb))
        hi = int(0.4 * mb)
        if budget > 2.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi, RMAX],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
