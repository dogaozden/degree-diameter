"""Multi-orbit group lifts for the bipartite degree-diameter problem.

Construction: pick a finite group G = Z_m x|_r Z_t (order G = m*t) and K >= 1.
The graph has 2KG vertices: fibres A_i = {A(i,x)} and B_j = {B(j,y)}, for i, j < K.
Each A-row i has d darts (j, g), and A(i,x) is joined to B(j, x*g). Every B_j
receives exactly d darts overall, so the graph is bipartite and d-regular.

Left multiplication by G is an automorphism that acts regularly on every fibre.
Diameter <= D therefore reduces to 2K BFS runs, one from each A(i,e) and B(j,e).
This is a different family from the parent's single-orbit Haar graphs over F_q x| H:
the base graph has K >= 1 orbits per side, and the group ranges over Z_m x| Z_t
for small t. Simulated annealing moves dart labels and swaps targets between darts,
which keeps the regularity. The cost is the number of vertices not reached within D
from the 2K base vertices.

Search is a bandit over candidate (K, G, t, r) tuples with 2KG in [lo, hi]. Each
candidate gets a short annealing slice. After a success, only larger orders are
considered. Python keeps the projective-plane, Araujo-Lopez and W(q) baselines and
the K_{d,d} fallback, and checks every returned graph with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit semidirect group lift search.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXK 4
#define MAXD 32
#define MAXG 4096
#define MAXV (2 * MAXK * MAXG)
#define MAXT 8
#define MAXCAND 300000

typedef struct { int K, m, t, r, G; } Cand;

static int d, D, K, G;
static double t_start, t_end;
static uint64_t rs = 88172645463325252ULL;
static uint64_t stamp_ = 0;

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

/* ------------------------------------------------------------ group Z_m x| Z_t */

static int gm, gt, gr;
static int gpw[MAXT];
static int ginvT[MAXG];

/* Element (a, b) is coded a*t + b. Product (a,b)(c,e) = (a + r^b c, b + e). */
static inline int gmul(int x, int y) {
    int a = x / gt, b = x - a * gt;
    int c = y / gt, e = y - c * gt;
    int na = (a + gpw[b] * c) % gm;
    int nb = b + e;
    if (nb >= gt) nb -= gt;
    return na * gt + nb;
}

static int ginv_el(int x) {
    int a = x / gt, b = x - a * gt;
    int nb = (gt - b) % gt;
    int na = (int)(((long)gm - ((long)gpw[nb] * a) % gm) % gm);
    return na * gt + nb;
}

static void setup_group(const Cand *c) {
    K = c->K;
    gm = c->m;
    gt = c->t;
    gr = c->r;
    G = c->G;
    gpw[0] = 1 % gm;
    for (int b = 1; b < gt; b++) gpw[b] = (int)((long)gpw[b - 1] * gr % gm);
    for (int g = 0; g < G; g++) ginvT[g] = ginv_el(g);
}

/* ------------------------------------------------------------ dart state */

/* Row i has d darts (dj, dg). A(i,x) ~ B(dj, x*dg). Every B_j gets exactly d darts. */
static int dj[MAXK][MAXD], dg[MAXK][MAXD];
static int fwdp[MAXK][MAXD][MAXG];   /* fwdp[i][t][x] = x * g        (A -> B) */
static int bwdp[MAXK][MAXD][MAXG];   /* bwdp[i][t][y] = y * g^{-1}   (B -> A) */
static int inc[MAXK][MAXD];          /* inc[j][s] = i*d + t of darts into j */
static int vis[MAXV], que[MAXV];

static void set_dart(int i, int t, int j, int g) {
    dj[i][t] = j;
    dg[i][t] = g;
    int gi = ginvT[g];
    for (int x = 0; x < G; x++) {
        fwdp[i][t][x] = gmul(x, g);
        bwdp[i][t][x] = gmul(x, gi);
    }
}

static void rebuild_inc(void) {
    int cnt[MAXK];
    for (int j = 0; j < K; j++) cnt[j] = 0;
    for (int i = 0; i < K; i++)
        for (int t = 0; t < d; t++) {
            int j = dj[i][t];
            inc[j][cnt[j]++] = i * d + t;
        }
}

static int row_ok(int i) {
    for (int a = 0; a < d; a++)
        for (int b = a + 1; b < d; b++)
            if (dj[i][a] == dj[i][b] && dg[i][a] == dg[i][b]) return 0;
    return 1;
}

/* Number of vertices within distance D of src. Vertices: A(i,x) = i*G + x,
 * B(j,y) = K*G + j*G + y. */
static int bfs_reach(int src) {
    int KG = K * G;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = (int)stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < KG) {
                int i = v / G, x = v - i * G;
                for (int t = 0; t < d; t++) {
                    int u = KG + dj[i][t] * G + fwdp[i][t][x];
                    if (vis[u] != (int)stamp_) { vis[u] = (int)stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - KG;
                int j = w / G, y = w - j * G;
                for (int s = 0; s < d; s++) {
                    int code = inc[j][s];
                    int i = code / d, t = code - i * d;
                    int u = i * G + bwdp[i][t][y];
                    if (vis[u] != (int)stamp_) { vis[u] = (int)stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left translation acts transitively on each fibre, so BFS from one A and one B per
 * orbit decides the diameter. */
static long cover_cost(void) {
    int V = 2 * K * G, KG = K * G;
    long c = 0;
    for (int i = 0; i < K; i++) c += (long)(V - bfs_reach(i * G));
    for (int j = 0; j < K; j++) c += (long)(V - bfs_reach(KG + j * G));
    return c;
}

static void random_init(void) {
    static int tg[MAXK * MAXD];
    int n = K * d;
    for (int j = 0; j < K; j++)
        for (int s = 0; s < d; s++) tg[j * d + s] = j;
    for (int a = n - 1; a > 0; a--) {
        int b = rndint(a + 1);
        int tmp = tg[a];
        tg[a] = tg[b];
        tg[b] = tmp;
    }
    for (int i = 0; i < K; i++)
        for (int t = 0; t < d; t++) {
            int j = tg[i * d + t];
            dj[i][t] = j;
            int g, ok;
            do {
                g = rndint(G);
                ok = 1;
                for (int a = 0; a < t; a++)
                    if (dj[i][a] == j && dg[i][a] == g) { ok = 0; break; }
            } while (!ok);
            dg[i][t] = g;
        }
    for (int i = 0; i < K; i++)
        for (int t = 0; t < d; t++) set_dart(i, t, dj[i][t], dg[i][t]);
    rebuild_inc();
}

/* Simulated annealing over darts. Returns 1 when cost 0 is reached, 0 on timeout. */
static int anneal(double until) {
    const int iters = 4000;
    while (now() < until) {
        random_init();
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.2 * c0 + 2.0, Te = 0.3;
        for (int it = 0; it < iters; it++) {
            if ((it & 31) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            if (rndint(2) == 0) {
                /* Change the group label of one dart. */
                int i = rndint(K), t = rndint(d);
                int j = dj[i][t], oldg = dg[i][t];
                int ng = rndint(G);
                if (ng == oldg) continue;
                set_dart(i, t, j, ng);
                if (!row_ok(i)) { set_dart(i, t, j, oldg); continue; }
                long c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    set_dart(i, t, j, oldg);
                }
            } else {
                /* Swap the targets of two darts (keeps every B_j at count d). */
                int i1 = rndint(K), t1 = rndint(d), i2 = rndint(K), t2 = rndint(d);
                if (i1 == i2 && t1 == t2) continue;
                int j1 = dj[i1][t1], j2 = dj[i2][t2];
                if (j1 == j2) continue;
                int g1 = dg[i1][t1], g2 = dg[i2][t2];
                set_dart(i1, t1, j2, g1);
                set_dart(i2, t2, j1, g2);
                rebuild_inc();
                if (!row_ok(i1) || (i2 != i1 && !row_ok(i2))) {
                    set_dart(i1, t1, j1, g1);
                    set_dart(i2, t2, j2, g2);
                    rebuild_inc();
                    continue;
                }
                long c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    set_dart(i1, t1, j1, g1);
                    set_dart(i2, t2, j2, g2);
                    rebuild_inc();
                }
            }
            if (cost == 0) return 1;
        }
    }
    return 0;
}

/* ------------------------------------------------------------ candidates */

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int powmod_(int r, int e, int m) {
    long x = 1 % m;
    for (int i = 0; i < e; i++) x = x * r % m;
    return (int)x;
}

static Cand cand[MAXCAND];
static int idxbuf[MAXCAND];

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
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    t_start = now();
    t_end = t_start + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (hi > MAXV) hi = MAXV;
    if (lo < 2 * d) lo = 2 * d;
    if (lo > hi) {
        printf("0 0\n");
        return 0;
    }

    int nc = 0;
    for (int Kk = 1; Kk <= MAXK; Kk++) {
        long Glo = (lo + 2L * Kk - 1) / (2L * Kk);
        long Ghi = hi / (2L * Kk);
        if (Ghi > MAXG) Ghi = MAXG;
        for (long GG = Glo; GG <= Ghi; GG++) {
            if (GG < 4) continue;
            for (int t = 1; t <= MAXT; t++) {
                if (GG % t) continue;
                int m = (int)(GG / t);
                if (m < 2) continue;
                for (int r = 1; r < m; r++) {
                    if (t == 1 && r != 1) continue;
                    if (powmod_(r, t, m) != 1 % m) continue;
                    if (gcd_i(r, m) != 1) continue;
                    if (nc < MAXCAND) {
                        cand[nc].K = Kk;
                        cand[nc].m = m;
                        cand[nc].t = t;
                        cand[nc].r = r;
                        cand[nc].G = (int)GG;
                        nc++;
                    }
                }
            }
        }
    }

    static int bDj[MAXK][MAXD], bDg[MAXK][MAXD];
    Cand bestC;
    int have = 0;
    long bestN = lo - 1;

    double slice = (t_end - t_start) / 14.0;
    if (slice < 1.0) slice = 1.0;

    while (nc > 0 && now() < t_end - 0.2) {
        int ne = 0;
        for (int c = 0; c < nc; c++)
            if (2L * cand[c].K * cand[c].G > bestN) idxbuf[ne++] = c;
        if (ne == 0) break;
        int c = idxbuf[rndint(ne)];
        double rem = t_end - now();
        double sl = slice < rem ? slice : rem;
        setup_group(&cand[c]);
        if (anneal(now() + sl)) {
            bestN = 2L * K * G;
            bestC = cand[c];
            memcpy(bDj, dj, sizeof dj);
            memcpy(bDg, dg, sizeof dg);
            have = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    setup_group(&bestC);
    for (int i = 0; i < K; i++)
        for (int t = 0; t < d; t++) set_dart(i, t, bDj[i][t], bDg[i][t]);
    int V = 2 * K * G, KG = K * G;
    printf("%d %d\n", V, KG * d);
    for (int i = 0; i < K; i++)
        for (int x = 0; x < G; x++)
            for (int t = 0; t < d; t++)
                printf("%d %d\n", i * G + x, KG + dj[i][t] * G + fwdp[i][t][x]);
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

    # New search: multi-orbit lifts over Z_m x| Z_t with K orbits per side.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
        lo = max(best[0] + 1, mb // 4)
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
