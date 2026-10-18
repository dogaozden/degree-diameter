"""Multi-class bi-Cayley lifts over semidirect groups (bold variant).

Construction family, new in this version:
  G = Z_m x|_r Z_k, the semidirect product with r^k = 1 mod m. The base graph has
  NC left classes and NC right classes, with NC in {1, 2}. Left class i and right
  class j are joined by M[i][j] darts. A dart with voltage w joins (L,i,x) to
  (R,j,x*w). For NC = 2 the base matrix is [[a, d-a], [d-a, a]] with 1 <= a <= d/2.
  Voltages are distinct inside each block, so the graph is simple. Every vertex has
  degree d, the graph is bipartite, and it has 2*NC*|G| vertices.

  G acts by left multiplication on every class at once, so the diameter is decided
  by one BFS from the identity of each class (2*NC BFS runs). NC = 1 is the Haar
  lift family used before, and NC = 2 is the new part: several base vertices per
  side, searched over voltages with simulated annealing.

Search: candidates (NC, a, m, k, r) with vertex count in [lo, hi] are tried in
ascending order, with random tie-breaking inside each vertex-count level. Each
candidate gets a bounded time slice. Once one succeeds, only larger counts are tried.
The leftover time goes to fresh random restarts.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-class bi-Cayley lift search over semidirect groups Z_m x|_r Z_k.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo, hi bound the output vertex count n = 2*NC*|G|.
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 4096
#define MAXV 16384
#define MAXE 40
#define MAXD 20
#define MAXCAND 300000
#define ITERS 6000
#define STAMP_LIMIT 2000000000

typedef struct { int nclass, a, m, k, r, g, V; unsigned key; } Cand;

static int d, D;
static int NC;          /* number of left classes = number of right classes */
static int DA;          /* parameter a of the NC = 2 base matrix */
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

static int powmod(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* ------------------------------------------------------------ group Z_m x| Z_k */

static int GM, GK, GG;
static int pw[MAXG];

static void setup_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (pw[b - 1] * r) % m;
}

/* Element (a, b) is coded a*k + b. Product (a,b)(c,t) = (a + r^b c, b + t). */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, t = y % GK;
    int na = (a + pw[b] * c) % GM;
    int nb = (b + t) % GK;
    return na * GK + nb;
}

static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int t = (GK - b) % GK;
    int c = (GM - (pw[t] * a) % GM) % GM;
    return c * GK + t;
}

/* ------------------------------------------------------------ dart layout */

static int E;                       /* number of darts = NC * d */
static int dl[MAXE], dr[MAXE], bk[MAXE];
static int LD[2][MAXD], RD[2][MAXD], Ln[2], Rn[2];
static int vol[MAXE], vinv[MAXE];
static int fwdT[MAXE * MAXG], bwdT[MAXE * MAXG];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static void setup_cand(const Cand *c) {
    NC = c->nclass;
    DA = c->a;
    setup_group(c->m, c->k, c->r);
    E = 0;
    Ln[0] = Ln[1] = 0;
    Rn[0] = Rn[1] = 0;
    for (int i = 0; i < NC; i++)
        for (int j = 0; j < NC; j++) {
            int cnt = (NC == 1) ? d : (i == j ? DA : d - DA);
            for (int t = 0; t < cnt; t++) {
                dl[E] = i;
                dr[E] = j;
                bk[E] = i * NC + j;
                vol[E] = -1;
                vinv[E] = -1;
                LD[i][Ln[i]++] = E;
                RD[j][Rn[j]++] = E;
                E++;
            }
        }
}

static void set_dart(int e, int w) {
    vol[e] = w;
    vinv[e] = ginv(w);
    int *f = fwdT + e * MAXG, *b = bwdT + e * MAXG;
    for (int x = 0; x < GG; x++) {
        f[x] = gmul(x, w);
        b[x] = gmul(x, vinv[e]);
    }
}

static int block_used(int e, int w) {
    for (int f = 0; f < E; f++)
        if (f != e && bk[f] == bk[e] && vol[f] == w) return 1;
    return 0;
}

/* Left vertex (i,x) = i*GG + x; right vertex (j,y) = (NC+j)*GG + y.
 * Edges: (L,i,x) ~ (R,j,x*w) for each dart e = (i,j,w). */
static int bfs_unreached(int src) {
    int Ag = NC * GG;
    if (++stamp_ >= STAMP_LIMIT) {
        memset(vis, 0, sizeof vis);
        stamp_ = 1;
    }
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < Ag) {
                int i = v / GG, x = v % GG;
                for (int t = 0; t < Ln[i]; t++) {
                    int e = LD[i][t];
                    int u = (NC + dr[e]) * GG + fwdT[e * MAXG + x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int j = v / GG - NC, y = v % GG;
                for (int t = 0; t < Rn[j]; t++) {
                    int e = RD[j][t];
                    int u = dl[e] * GG + bwdT[e * MAXG + y];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return 2 * Ag - tail;
}

/* G acts on every side by left multiplication, so one BFS per class decides the diameter. */
static long cost_all(void) {
    long c = 0;
    for (int i = 0; i < NC; i++) {
        c += bfs_unreached(i * GG);
        c += bfs_unreached((NC + i) * GG);
    }
    return c;
}

/* Simulated annealing over the voltages of the current candidate.
 * Returns 1 when diameter <= D is reached, 0 at the deadline. */
static int search_cand(double until) {
    while (now() < until) {
        for (int e = 0; e < E; e++) vol[e] = -1;
        for (int e = 0; e < E; e++) {
            int w;
            do { w = rndint(GG); } while (block_used(e, w));
            set_dart(e, w);
        }
        long cost = cost_all();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < ITERS && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / ITERS);
            int e = rndint(E);
            int w = -1, tries = 0;
            do {
                w = rndint(GG);
                tries++;
            } while ((w == vol[e] || block_used(e, w)) && tries < 1000);
            if (w == vol[e] || block_used(e, w)) continue;
            int old = vol[e];
            set_dart(e, w);
            long c2 = cost_all();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_dart(e, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ candidates */

static Cand cand[MAXCAND];
static int nc = 0;

static void add_cand(int na, int a, int m, int k, int r) {
    if (nc >= MAXCAND) return;
    Cand c;
    c.nclass = na;
    c.a = a;
    c.m = m;
    c.k = k;
    c.r = r;
    c.g = m * k;
    c.V = 2 * na * c.g;
    c.key = (unsigned)rnd();
    cand[nc++] = c;
}

static int cmp_cand(const void *x, const void *y) {
    const Cand *a = x, *b = y;
    if (a->V != b->V) return a->V < b->V ? -1 : 1;
    if (a->key != b->key) return a->key < b->key ? -1 : 1;
    return 0;
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
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }

    for (int na = 1; na <= 2; na++) {
        long glo = (lo + 2L * na - 1) / (2L * na);
        long ghi = hi / (2L * na);
        if (glo < 2L * d) glo = 2L * d;
        if (ghi > MAXG) ghi = MAXG;
        for (long g = glo; g <= ghi; g++) {
            for (int k = 1; k <= g; k++) {
                if (g % k) continue;
                int m = (int)(g / k);
                if (m < 2) continue;
                int amin = 0, amax = 0;
                if (na == 2) {
                    amin = 1;
                    amax = d / 2;
                }
                for (int r = 1; r < m; r++) {
                    if (powmod(r, k, m) != 1) continue;
                    for (int a = amin; a <= amax; a++) add_cand(na, a, m, k, r);
                }
            }
        }
    }
    if (nc == 0) {
        printf("0 0\n");
        return 0;
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    int bestV = 0, found = 0;
    Cand bestC;
    int bestVol[MAXE];
    for (int pass = 0; pass < 1000000; pass++) {
        int any = 0;
        for (int ci = 0; ci < nc; ci++) {
            Cand c = cand[ci];
            if (c.V <= bestV) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            any = 1;
            double slice = 0.05 * rem;
            if (slice < 0.5) slice = 0.5;
            if (slice > 3.0) slice = 3.0;
            if (slice > rem) slice = rem;
            setup_cand(&c);
            if (search_cand(now() + slice)) {
                bestV = c.V;
                bestC = c;
                found = 1;
                for (int e = 0; e < E; e++) bestVol[e] = vol[e];
            }
        }
        if (!any || t_end - now() < 0.3) break;
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    setup_cand(&bestC);
    for (int e = 0; e < E; e++) set_dart(e, bestVol[e]);
    int n = 2 * NC * GG;
    long mcount = (long)E * GG;
    printf("%d %ld\n", n, mcount);
    for (int e = 0; e < E; e++) {
        int i = dl[e], j = dr[e], w = vol[e];
        for (int x = 0; x < GG; x++)
            printf("%d %d\n", i * GG + x, (NC + j) * GG + gmul(x, w));
    }
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

    # Search: multi-class bi-Cayley lifts over Z_m x| Z_k, vertex counts in [mb/4, mb/3].
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, mb // 4)
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
