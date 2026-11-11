"""Multi-vertex voltage lifts over semidirect groups for the bipartite degree-diameter problem.

Change in this version: the parent searched only Haar graphs, which are lifts of a
single base edge-bundle (one vertex per side) over an affine-type group Z_q x| Z_c. This
version lifts a base bipartite multigraph with B vertices per side (B = 1..4) over a
general semidirect group Z_m x|_r Z_k, for any m, k, r with r^k = 1 mod m. The base is a
d-regular bipartite multigraph given by d permutations sigma_k of {0..B-1}, so the lift
is d-regular and bipartite. Each dart k carries a voltage g_{i,k} in the group. The lift
has 2*B*|G| vertices. The group acts on each fibre by left multiplication, so the
diameter test needs only 2B BFS runs, one from each fibre identity. Simulated annealing
moves voltages and swaps permutation images. Repeated darts between the same pair must
get distinct voltages to keep the graph simple, and this is a penalty term.

The search climbs a ladder: it tries random (B, group, order) candidates just above the
current best order, and each success raises the bar. Python keeps the projective-plane,
Araujo-Lopez, W(q) and K_{d,d} baselines, and every returned graph is checked with
lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-vertex semidirect voltage lift search.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo, hi bound the total vertex count 2*B*|G|.
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXB 4
#define MAXDD 32
#define MAXV 65536
#define COLL_W 40
#define ITERS 6000

static int d, D, B, GM, GK, GN, GR, V;
static int PW[MAXV];
static int G[MAXB][MAXDD];     /* voltage of left vertex i on dart k */
static int SG[MAXDD][MAXB];    /* dart k: left i -> right SG[k][i]   */
static int *adj, *vis, *que;
static int stampv = 0;
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

/* Group Z_M x|_R Z_K, element a*K+b, (a,b)(c,e) = (a + R^b c, b + e). Identity is 0. */
static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GN = m * k;
    GR = (m == 1) ? 0 : r % m;
    PW[0] = 1 % m;
    for (int j = 1; j < k; j++) PW[j] = (int)((long long)PW[j - 1] * GR % m);
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int na = (int)((a + (long long)PW[b] * c) % GM);
    int nb = b + e;
    if (nb >= GK) nb -= GK;
    return na * GK + nb;
}

static inline int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int na = (int)((GM - (long long)PW[nb] * a % GM) % GM);
    return na * GK + nb;
}

static void setup(int bb, int m, int k, int r) {
    B = bb;
    set_group(m, k, r);
    V = 2 * B * GN;
}

/* Vertex index = fibre * GN + x. Left fibres 0..B-1, right fibres B..2B-1.
 * Left (i,x) joined to right (SG[k][i], x*g) for g = G[i][k]. */
static void update_dart(int k, int i) {
    int j = SG[k][i];
    int g = G[i][k];
    int gi = ginv(g);
    int lbase = i * GN, rbase = (B + j) * GN;
    for (int x = 0; x < GN; x++) {
        adj[(lbase + x) * d + k] = rbase + gmul(x, g);
        adj[(rbase + x) * d + k] = lbase + gmul(x, gi);
    }
}

static void full_build(void) {
    for (int k = 0; k < d; k++)
        for (int i = 0; i < B; i++)
            update_dart(k, i);
}

/* Number of vertices NOT within distance D of src. */
static int bfs_unreached(int src) {
    if (stampv == 0x7fffffff) {
        memset(vis, 0, sizeof(int) * (size_t)V);
        stampv = 0;
    }
    stampv++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stampv;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            const int *a = adj + (long)v * d;
            for (int k = 0; k < d; k++) {
                int u = a[k];
                if (vis[u] != stampv) {
                    vis[u] = stampv;
                    que[tail++] = u;
                }
            }
        }
    }
    return V - tail;
}

/* Left-translation acts transitively on each fibre, so BFS from each fibre identity suffices. */
static long eval_cost(void) {
    long c = 0;
    for (int u = 0; u < 2 * B; u++) c += bfs_unreached(u * GN);
    for (int i = 0; i < B; i++)
        for (int k = 0; k < d; k++)
            for (int k2 = k + 1; k2 < d; k2++)
                if (SG[k][i] == SG[k2][i] && G[i][k] == G[i][k2]) c += COLL_W;
    return c;
}

static void randomize(void) {
    for (int i = 0; i < B; i++)
        for (int k = 0; k < d; k++)
            G[i][k] = rndint(GN);
    for (int k = 0; k < d; k++) {
        for (int i = 0; i < B; i++) SG[k][i] = i;
        for (int i = B - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = SG[k][i];
            SG[k][i] = SG[k][j];
            SG[k][j] = t;
        }
    }
    full_build();
}

/* Simulated annealing on the current group and base size. Returns 1 at cost 0 (state kept). */
static int search_group(double until) {
    while (now() < until) {
        randomize();
        long cost = eval_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < ITERS; it++) {
            if ((it & 7) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / ITERS);
            if (B > 1 && rnd01() < 0.15) {
                int k = rndint(d);
                int i1 = rndint(B), i2 = rndint(B - 1);
                if (i2 >= i1) i2++;
                int t = SG[k][i1];
                SG[k][i1] = SG[k][i2];
                SG[k][i2] = t;
                update_dart(k, i1);
                update_dart(k, i2);
                long c2 = eval_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    t = SG[k][i1];
                    SG[k][i1] = SG[k][i2];
                    SG[k][i2] = t;
                    update_dart(k, i1);
                    update_dart(k, i2);
                }
            } else {
                int i = rndint(B), k = rndint(d);
                int old = G[i][k];
                int nv = rndint(GN);
                if (nv == old) continue;
                G[i][k] = nv;
                update_dart(k, i);
                long c2 = eval_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    G[i][k] = old;
                    update_dart(k, i);
                }
            }
            if (cost == 0) return 1;
        }
    }
    return 0;
}

/* Random r with r^k = 1 mod m (uniform over such r in [1, m)). Returns 1 if none beyond identity. */
static int pick_r(int m, int k) {
    if (m == 1) return 0;
    int cnt = 0, pick = 1;
    for (int r = 1; r < m; r++) {
        long long x = 1 % m, base = r;
        int e = k;
        while (e) {
            if (e & 1) x = x * base % m;
            base = base * base % m;
            e >>= 1;
        }
        if (x == 1 % m) {
            cnt++;
            if (rndint(cnt) == 0) pick = r;
        }
    }
    return pick;
}

static int pick_divisor(int n) {
    int cnt = 0, pick = 1;
    for (int k = 1; k <= n; k++)
        if (n % k == 0) {
            cnt++;
            if (rndint(cnt) == 0) pick = k;
        }
    return pick;
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
    long lo = atol(argv[5]), hi = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.93 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (hi > MAXV) hi = MAXV;
    if (lo < 4) lo = 4;

    adj = (int *)malloc(sizeof(int) * (size_t)MAXV * MAXDD);
    vis = (int *)calloc((size_t)MAXV, sizeof(int));
    que = (int *)malloc(sizeof(int) * (size_t)MAXV);
    if (!adj || !vis || !que) {
        printf("0 0\n");
        return 0;
    }

    long best_V = 0;
    int bestG[MAXB][MAXDD], bestSG[MAXDD][MAXB];
    int bB = 0, bm = 1, bk = 1, br = 0;

    while (now() < t_end) {
        if (lo > hi) break;
        int ok = 0;
        int b_ = 1, m_ = 1, k_ = 1, r_ = 0;
        for (int trial = 0; trial < 50 && !ok; trial++) {
            int bb = 1 + rndint(MAXB);
            long Nmin = (lo + 2L * bb - 1) / (2L * bb);
            long Nmax = hi / (2L * bb);
            if (Nmin > Nmax || Nmax < 1) continue;
            long span = Nmax - Nmin;
            if (span > 24) span = 24;
            long Nn = Nmin + rndint((int)span + 1);
            int kk = pick_divisor((int)Nn);
            int mm = (int)Nn / kk;
            b_ = bb;
            m_ = mm;
            k_ = kk;
            r_ = pick_r(mm, kk);
            ok = 1;
        }
        if (!ok) break;

        setup(b_, m_, k_, r_);
        double rem = t_end - now();
        double slice = rem / 6.0;
        if (slice < 1.5) slice = 1.5;
        if (slice > rem) slice = rem;
        if (search_group(now() + slice)) {
            long Vn = (long)V;
            if (Vn > best_V) {
                best_V = Vn;
                memcpy(bestG, G, sizeof(G));
                memcpy(bestSG, SG, sizeof(SG));
                bB = B;
                bm = GM;
                bk = GK;
                br = GR;
                lo = best_V + 1;
            }
        }
    }

    if (best_V == 0) {
        printf("0 0\n");
        return 0;
    }
    setup(bB, bm, bk, br);
    memcpy(G, bestG, sizeof(G));
    memcpy(SG, bestSG, sizeof(SG));
    full_build();
    int edges = B * GN * d;
    printf("%d %d\n", V, edges);
    for (int v = 0; v < B * GN; v++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", v, adj[v * d + k]);
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

    # Multi-vertex semidirect voltage lifts: search only orders strictly above the baseline.
    if 2 <= d <= 32 and D >= 3:
        mb = lib.moore_bound(d, D)
        lo = best[0] + 1
        hi = min(mb, 65536)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
        if budget > 3.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 6.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass  # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
