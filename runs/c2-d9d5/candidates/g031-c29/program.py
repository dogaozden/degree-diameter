"""Four-orbit bi-affine lifts for the bipartite degree-diameter problem.

Change from the parent: instead of a single Haar graph on one group G (two base
vertices, one orbit per side), this version uses a 2x2 base with four connection
sets S[a][b] on G (a = left orbit, b = right orbit). The graph has 4|G| vertices:
L_{a,g} ~ R_{b, g*s} for s in S[a][b]. Left multiplication is an automorphism, so
diameter <= D reduces to four BFS runs, one from each base vertex L0, L1, R0, R1.

Groups: Z_q x| Z_c (q prime, c | q-1, c >= 2), which is non-abelian, and cyclic Z_M
only where no affine group of that order exists. The class sizes are
|S00| = s, |S01| = d-s, |S10| = d-s, |S11| = s, so every vertex has degree d.
Candidate group orders are tried in ascending order above the current best, and
each attempt is an iterated annealing that restarts from the incumbent set.
Every output is re-checked in Python with lib.is_valid, with a valid fallback.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Four-orbit bi-affine lift search.
 * Usage: prog d D seed time_limit lo hi     (lo, hi are group orders M; stdin ignored)
 * Output: "n m" then m lines "u v" for a valid graph with n = 4M, or "0 0".
 * Vertices: L_{a,g} = a*M + g, R_{b,h} = 2M + b*M + h.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 2400
#define MAXD 32
#define MAXCAND 40000

typedef struct { int type, q, c, M; } Cand;   /* type 1: Z_q x| Z_c ; type 0: Z_M */

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

/* ------------------------------------------------------------ groups */

static int gtype, gM, gq, gc;
static int Hv[MAXM];   /* affine: Hv[j] = h_j, the cyclic subgroup of order c in Z_q^* */

static long long mpow(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int prim_root(int q) {
    int fac[32], nf = 0, n = q - 1;
    for (int f = 2; (long)f * f <= n; f++)
        if (n % f == 0) {
            fac[nf++] = f;
            while (n % f == 0) n /= f;
        }
    if (n > 1) fac[nf++] = n;
    for (int g = 2; g < q; g++) {
        int ok = 1;
        for (int i = 0; i < nf && ok; i++)
            if (mpow(g, (q - 1) / fac[i], q) == 1) ok = 0;
        if (ok) return g;
    }
    return -1;
}

static void setup_group(int type, int q, int c, int M) {
    gtype = type;
    gM = M;
    gq = q;
    gc = c;
    if (type == 1) {
        int g = prim_root(q);
        for (int j = 0; j < c; j++)
            Hv[j] = (int)mpow(g, (long long)j * ((q - 1) / c), q);
    }
}

/* Affine element (a, h_j) is coded a*c + j. Product (a,h_j)(b,h_t) = (a + h_j b, h_{j+t}). */
static inline int gmul(int x, int y) {
    if (gtype == 0) {
        int r = x + y;
        if (r >= gM) r -= gM;
        return r;
    }
    int a = x / gc, j = x % gc, b = y / gc, t = y % gc;
    int na = (int)((a + (long long)Hv[j] * b) % gq);
    int nj = j + t;
    if (nj >= gc) nj -= gc;
    return na * gc + nj;
}

static inline int ginv(int x) {
    if (gtype == 0) return x == 0 ? 0 : gM - x;
    int a = x / gc, j = x % gc;
    int jn = (gc - j) % gc;
    int na = (int)((gq - ((long long)Hv[jn] * a) % gq) % gq);
    return na * gc + jn;
}

/* ------------------------------------------------------------ connection sets */

static int sz[2][2];
static int S[2][2][MAXD];
static int Fw[2][2][MAXD][MAXM];   /* Fw: L_{a,g} -> R_{b, g*s} */
static int Bw[2][2][MAXD][MAXM];   /* Bw: R_{b,h} -> L_{a, h*s^-1} */

static void set_el(int a, int b, int i, int x) {
    S[a][b][i] = x;
    int xi = ginv(x);
    for (int g = 0; g < gM; g++) {
        Fw[a][b][i][g] = gmul(g, x);
        Bw[a][b][i][g] = gmul(g, xi);
    }
}

static int in_class(int a, int b, int x, int upto) {
    for (int j = 0; j < upto; j++)
        if (S[a][b][j] == x) return 1;
    return 0;
}

static int vis[4 * MAXM], que[4 * MAXM];
static int stamp_ = 0;

/* Number of vertices within distance D of src. */
static int bfs_reach(int src) {
    int M_ = gM, V = 4 * M_;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail && tail < V; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < 2 * M_) {
                int a = v / M_, g = v - a * M_;
                for (int b = 0; b < 2; b++)
                    for (int i = 0; i < sz[a][b]; i++) {
                        int u = 2 * M_ + b * M_ + Fw[a][b][i][g];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
            } else {
                int w = v - 2 * M_;
                int b = w / M_, h = w - b * M_;
                for (int a = 0; a < 2; a++)
                    for (int i = 0; i < sz[a][b]; i++) {
                        int u = a * M_ + Bw[a][b][i][h];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
            }
        }
    }
    return tail;
}

/* Sum over the four base vertices of the number of vertices farther than D. */
static long cover_cost(void) {
    int V = 4 * gM;
    int srcs[4] = {0, gM, 2 * gM, 3 * gM};
    long c = 0;
    for (int s = 0; s < 4; s++) c += (long)(V - bfs_reach(srcs[s]));
    return c;
}

static void random_init(void) {
    for (int a = 0; a < 2; a++)
        for (int b = 0; b < 2; b++)
            for (int i = 0; i < sz[a][b]; i++) {
                int x;
                do { x = rndint(gM); } while (in_class(a, b, x, i));
                set_el(a, b, i, x);
            }
}

/* Iterated annealing: round 1 from random sets; later rounds perturb the incumbent
 * (two elements replaced) at a lower starting temperature.
 * Returns 1 with S holding a cost-0 set, or 0 on timeout. */
static int search_group(double until) {
    int M_ = gM;
    const int iters = 3000;
    int cls[4][2], ncls = 0;
    for (int a = 0; a < 2; a++)
        for (int b = 0; b < 2; b++)
            if (sz[a][b] > 0) { cls[ncls][0] = a; cls[ncls][1] = b; ncls++; }
    int have = 0;
    long bestc = 0;
    static int inc[2][2][MAXD];
    while (now() < until) {
        if (!have) {
            random_init();
        } else {
            for (int k = 0; k < ncls; k++) {
                int a = cls[k][0], b = cls[k][1];
                for (int i = 0; i < sz[a][b]; i++) set_el(a, b, i, inc[a][b][i]);
            }
            for (int t = 0; t < 2; t++) {
                int k = rndint(ncls), a = cls[k][0], b = cls[k][1];
                int i = rndint(sz[a][b]);
                int x;
                do { x = rndint(M_); } while (in_class(a, b, x, sz[a][b]));
                set_el(a, b, i, x);
            }
        }
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.03 : 0.08) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 7) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int k = rndint(ncls), a = cls[k][0], b = cls[k][1];
            int i = rndint(sz[a][b]);
            int x;
            do { x = rndint(M_); } while (in_class(a, b, x, sz[a][b]));
            int old = S[a][b][i];
            set_el(a, b, i, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                if (cost == 0) return 1;
            } else {
                set_el(a, b, i, old);
            }
        }
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(inc, S, sizeof(S));
        }
    }
    return 0;
}

/* ------------------------------------------------------------ number theory helpers */

static char isp[MAXM + 1];

static void print_result(void) {
    int M_ = gM;
    printf("%d %d\n", 4 * M_, 2 * M_ * d);
    for (int a = 0; a < 2; a++)
        for (int g = 0; g < M_; g++)
            for (int b = 0; b < 2; b++)
                for (int i = 0; i < sz[a][b]; i++)
                    printf("%d %d\n", a * M_ + g, 2 * M_ + b * M_ + Fw[a][b][i][g]);
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
    t_end = t0 + limit * 0.95 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (lo < d + 1) lo = d + 1;
    if (hi > MAXM) hi = MAXM;
    if (lo > hi) {
        printf("0 0\n");
        return 0;
    }

    for (int n = 0; n <= MAXM; n++) isp[n] = (n >= 2);
    for (int p = 2; p * p <= MAXM; p++)
        if (isp[p])
            for (int m = p * p; m <= MAXM; m += p) isp[m] = 0;

    /* Candidates in ascending order of M: affine groups Z_q x| Z_c first; cyclic Z_M only
     * when no affine group of that order exists. */
    static Cand cand[MAXCAND];
    int nc = 0;
    for (int M = lo; M <= hi; M++) {
        int cnt = 0;
        for (int c = 2; c <= M / 3; c++) {
            if (M % c) continue;
            int q = M / c;
            if (q >= 3 && isp[q] && (q - 1) % c == 0) {
                if (nc < MAXCAND) {
                    Cand cd = {1, q, c, M};
                    cand[nc++] = cd;
                }
                cnt++;
            }
        }
        if (!cnt && nc < MAXCAND) {
            Cand cd = {0, 0, M, M};
            cand[nc++] = cd;
        }
    }

    /* Ascending attempts; each candidate with M above the best gets a quarter of the
     * remaining time (at least 1 s). */
    int bestM = 0;
    static int bestSet[2][2][MAXD];
    int bestSz[2][2];
    Cand bestCand = {0, 0, 0, 0};
    for (int ci = 0; ci < nc; ci++) {
        double rem = t_end - now();
        if (rem < 0.5) break;
        Cand cd = cand[ci];
        if (cd.M <= bestM) continue;
        double slice = 0.25 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_group(cd.type, cd.q, cd.c, cd.M);
        int s = 1 + rndint(d - 1);   /* |S00| = s, |S01| = d-s, |S10| = d-s, |S11| = s */
        sz[0][0] = s;
        sz[0][1] = d - s;
        sz[1][0] = d - s;
        sz[1][1] = s;
        if (search_group(now() + slice)) {
            bestM = cd.M;
            bestCand = cd;
            memcpy(bestSet, S, sizeof(S));
            memcpy(bestSz, sz, sizeof(sz));
        }
    }

    if (bestM == 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(bestCand.type, bestCand.q, bestCand.c, bestCand.M);
    memcpy(sz, bestSz, sizeof(sz));
    for (int a = 0; a < 2; a++)
        for (int b = 0; b < 2; b++)
            for (int i = 0; i < sz[a][b]; i++)
                set_el(a, b, i, bestSet[a][b][i]);
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

    # Search: four-orbit bi-affine lifts. Vertex count is 4M, so M = n/4.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        lo_M = max(best[0] // 4 + 1, d + 1, mb // 15)
        hi_M = min(mb // 4, 2400)
        if budget > 2.0 and lo_M <= hi_M:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo_M, hi_M],
                                 stdin_graph=None, timeout=budget + 6.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
