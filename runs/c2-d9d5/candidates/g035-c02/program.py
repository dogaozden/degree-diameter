"""Two-stage voltage-lift search for the bipartite degree-diameter problem.

Stage A reproduces the parent's search: Haar graphs (one base vertex per side) over
F_q x| H, climbing in ascending order. It keeps the parent's score as a floor.

Stage B is the new construction. Each graph is a lift of a base bipartite multigraph
with B vertices per side (B = 1..4) and d darts per base vertex. Darts carry voltages
in a group G, which is either F_q x| H or a semidirect product Z_m x| Z_k. The lift
has 2*B*|G| vertices. Left translations act transitively on each fibre, so the
diameter check reduces to 2*B BFS runs. Stage B searches random candidates above the
best order found so far, with simulated annealing over the voltages.

Every output is checked with lib.is_valid. If nothing better is found, the program
returns the best Python construction (K_{d,d} or a projective-plane graph).
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-vertex voltage lifts over small groups, with a parent-style Haar stage.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo, hi are vertex-count bounds. Output: "n m" then m edges, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 256
#define MAXN 1600
#define MAXB 4
#define MAXD 32
#define MAXDART (MAXB * MAXD)
#define MAXV (2 * MAXB * MAXN)
#define MAXCAND 60000

typedef struct { int type, B, N, q, c, m, kk, r; unsigned rk; } Cand;

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
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

/* gtype 0: F_q x| H, element a*GC+j, (a,h_j)(b,h_t) = (a + h_j b, h_j h_t).
 * gtype 1: Z_m x|_r Z_k, element a*GC+b, (a,b)(c,d) = (a + r^b c, b+d).
 * Identity is always index 0. */
static int gtype, GN, GQ, GC;
static int Hel[MAXQ], hidx[MAXQ], HM[MAXQ * MAXQ], PWG[MAXQ];
static int PW[MAXN + 1];
static int GI[MAXN];
static unsigned short M[MAXN][MAXN];   /* M[g][x] = x * g */

static void setup_group0(int q, int p, int k, int c) {
    build_field(q, p, k);
    gtype = 0;
    GQ = q;
    GC = c;
    GN = q * c;
    int g = -1;
    for (int g0 = 2; g0 < q && g < 0; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) g = g0;
    }
    if (g < 0) g = 1;
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

static void setup_group1(int m, int k, int r) {
    gtype = 1;
    GQ = m;
    GC = k;
    GN = m * k;
    PW[0] = 1 % m;
    for (int b = 1; b < k; b++) PW[b] = (int)(((long)PW[b - 1] * r) % m);
}

static int gm(int x, int y) {
    if (gtype == 0) {
        int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
        int na = ADDT[a][MULT[Hel[j]][b]];
        return na * GC + HM[j * GC + t];
    } else {
        int a = x / GC, b = x % GC, c = y / GC, e = y % GC;
        int na = (a + (PW[b] * c) % GQ) % GQ;
        return na * GC + (b + e) % GC;
    }
}

static int gi(int x) {
    if (gtype == 0) {
        int a = x / GC, j = x % GC;
        int jn = (GC - j) % GC;
        int na = NEGT[MULT[Hel[jn]][a]];
        return na * GC + jn;
    } else {
        int a = x / GC, b = x % GC;
        int nb = (GC - b) % GC;
        int na = (GQ - (PW[nb] * a) % GQ) % GQ;
        return na * GC + nb;
    }
}

static void build_tables(void) {
    for (int g = 0; g < GN; g++)
        for (int x = 0; x < GN; x++)
            M[g][x] = (unsigned short)gm(x, g);
    for (int g = 0; g < GN; g++) GI[g] = gi(g);
}

/* ------------------------------------------------------------ graph state */

static int B;
static int NDART;
static int dI[MAXDART], dJ[MAXDART], dG[MAXDART], dGI[MAXDART];
static int RQ[MAXB][MAXD];           /* RQ[j][t] = dart index going into right j, level t */
static int vis[MAXV], que[MAXV];
static int stampv = 0;

/* Dart q = i*d + t goes from left fibre i to right fibre dJ[q] = perm_t(i). */
static void make_pattern(void) {
    NDART = B * d;
    for (int t = 0; t < d; t++) {
        int perm[MAXB];
        for (int i = 0; i < B; i++) perm[i] = i;
        for (int i = B - 1; i > 0; i--) {
            int j = rndint(i + 1), tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < B; i++) {
            int q = i * d + t;
            dI[q] = i;
            dJ[q] = perm[i];
            RQ[perm[i]][t] = q;
        }
    }
}

/* True if element g can be used by dart q without repeating an edge (same cell). */
static int cell_ok(int q, int g) {
    for (int q2 = 0; q2 < NDART; q2++)
        if (q2 != q && dG[q2] == g && dI[q2] == dI[q] && dJ[q2] == dJ[q]) return 0;
    return 1;
}

/* Number of vertices within distance D of src. Vertices: left (i,x) = i*GN+x,
 * right (j,y) = B*GN + j*GN + y. Edge (i,x)-(j, x*g) for each dart (i,j,g). */
static int reached(int src) {
    int N = GN, BN = B * GN;
    stampv++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stampv;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int i = v / N, x = v - i * N;
                for (int t = 0; t < d; t++) {
                    int q = i * d + t;
                    int u = BN + dJ[q] * N + (int)M[dG[q]][x];
                    if (vis[u] != stampv) { vis[u] = stampv; que[tail++] = u; }
                }
            } else {
                int w = v - BN;
                int j = w / N, y = w - j * N;
                for (int t = 0; t < d; t++) {
                    int q = RQ[j][t];
                    int u = dI[q] * N + (int)M[dGI[q]][y];
                    if (vis[u] != stampv) { vis[u] = stampv; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Vertex-transitivity on each fibre: BFS from each fibre's identity vertex. */
static long cost_full(void) {
    int V = 2 * B * GN;
    long c = 0;
    for (int r = 0; r < 2 * B; r++)
        c += (long)(V - reached(r * GN));
    return c;
}

static int search_cand(double until, int iters) {
    while (now() < until) {
        make_pattern();
        for (int q = 0; q < NDART; q++) dG[q] = -1;
        for (int q = 0; q < NDART; q++) {
            int g;
            do { g = rndint(GN); } while (!cell_ok(q, g));
            dG[q] = g;
            dGI[q] = GI[g];
        }
        long cost = cost_full();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 7) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int q = rndint(NDART);
            int old = dG[q], oldi = dGI[q];
            int g;
            do { g = rndint(GN); } while (g == old || !cell_ok(q, g));
            dG[q] = g;
            dGI[q] = GI[g];
            long c2 = cost_full();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                dG[q] = old;
                dGI[q] = oldi;
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ candidates */

static Cand cand[MAXCAND];
static int nc = 0;
static int bestV = 0;
static Cand bestC;
static int bestDJ[MAXDART], bestDG[MAXDART];

static void add_cand(int type, int Bb, int N, int q, int c, int m, int kk, int r) {
    if (nc >= MAXCAND) return;
    Cand x;
    x.type = type; x.B = Bb; x.N = N; x.q = q; x.c = c;
    x.m = m; x.kk = kk; x.r = r;
    x.rk = (unsigned)rnd();
    cand[nc++] = x;
}

/* mode 0: B = 1, F_q x| H only (parent family). mode 1: all families, B = 1..MAXB. */
static void enumerate(int mode, long lo, long hi) {
    nc = 0;
    int bmax = (mode == 0) ? 1 : MAXB;
    for (int Bb = 1; Bb <= bmax; Bb++) {
        long Nlo = (lo + 2L * Bb - 1) / (2L * Bb);
        long Nhi = hi / (2L * Bb);
        if (Nlo < d + 1) Nlo = d + 1;
        if (Nlo < 3) Nlo = 3;
        if (Nhi > MAXN) Nhi = MAXN;
        for (int N = (int)Nlo; N <= Nhi; N++) {
            for (int q = 3; q <= N && q < MAXQ; q++) {
                if (N % q) continue;
                int c = N / q, p, k;
                if (!factor_pp(q, &p, &k)) continue;
                if ((q - 1) % c) continue;
                add_cand(0, Bb, N, q, c, 0, 0, 0);
            }
            if (mode == 1) {
                for (int kk = 1; kk <= N; kk++) {
                    if (N % kk) continue;
                    int m = N / kk;
                    if (m < 2) continue;
                    for (int r = 1; r < m; r++) {
                        if (gcd_i(r, m) != 1) continue;
                        if (powmod_i(r, kk, m) != 1 % m) continue;
                        add_cand(1, Bb, N, 0, 0, m, kk, r);
                    }
                }
            }
        }
    }
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    long vx = 2L * x->B * x->N, vy = 2L * y->B * y->N;
    if (vx != vy) return vx < vy ? -1 : 1;
    if (x->rk != y->rk) return x->rk < y->rk ? -1 : 1;
    return 0;
}

static void setup_candidate(const Cand *c) {
    B = c->B;
    if (c->type == 0) {
        int p, k;
        factor_pp(c->q, &p, &k);
        setup_group0(c->q, p, k, c->c);
    } else {
        setup_group1(c->m, c->kk, c->r);
    }
    build_tables();
}

static void save_best(const Cand *c) {
    bestV = 2 * B * GN;
    bestC = *c;
    for (int q = 0; q < NDART; q++) {
        bestDJ[q] = dJ[q];
        bestDG[q] = dG[q];
    }
}

static void run_stage(int mode, long lo, long hi, double until) {
    enumerate(mode, lo, hi);
    if (nc == 0) return;
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);
    static int order[MAXCAND];
    for (int pass = 0; pass < 100000; pass++) {
        for (int i = 0; i < nc; i++) order[i] = i;
        if (mode == 1) {
            for (int i = nc - 1; i > 0; i--) {
                int j = rndint(i + 1), t2 = order[i];
                order[i] = order[j];
                order[j] = t2;
            }
        }
        int tried = 0;
        for (int oi = 0; oi < nc; oi++) {
            int ci = order[oi];
            int V = 2 * cand[ci].B * cand[ci].N;
            if (V <= bestV) continue;
            double rem = until - now();
            if (rem < 0.3) break;
            double slice;
            if (mode == 0) {
                slice = 0.2 * rem;
                if (slice < 1.0) slice = 1.0;
            } else {
                int ps = pass < 5 ? pass : 5;
                slice = (double)(1 << ps);
            }
            if (slice > rem) slice = rem;
            tried = 1;
            setup_candidate(&cand[ci]);
            if (search_cand(now() + slice, mode == 0 ? 8000 : 4000))
                save_best(&cand[ci]);
        }
        if (!tried || until - now() < 0.3) break;
    }
}

static void print_best(void) {
    setup_candidate(&bestC);
    int N = GN, BN = B * N;
    printf("%d %d\n", 2 * BN, B * d * N);
    for (int q = 0; q < B * d; q++) {
        int i = q / d, j = bestDJ[q], g = bestDG[q];
        for (int x = 0; x < N; x++)
            printf("%d %d\n", i * N + x, BN + j * N + (int)M[g][x]);
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
    long lo = atol(argv[5]), hi = atol(argv[6]);
    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (lo < 2L * d) lo = 2L * d;

    /* Stage A: parent-style Haar lifts over F_q x| H (one base vertex). */
    double split = t0 + 0.55 * (t_end - t0);
    run_stage(0, lo, hi, split);

    /* Stage B: multi-vertex base lifts over all families, above the stage-A order. */
    long loB = (long)bestV + 2 > lo ? (long)bestV + 2 : lo;
    long hiB = hi < loB + 200 ? hi : loB + 200;
    if (loB <= hiB) run_stage(1, loB, hiB, t_end);

    if (bestV <= 0) {
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

    # Search: stage A (parent Haar family) then stage B (multi-vertex base lifts).
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
        lo = max(best[0] + 2, mb // 8, 2 * d)
        hi = max(lo, mb // 3)
        if budget > 3.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
