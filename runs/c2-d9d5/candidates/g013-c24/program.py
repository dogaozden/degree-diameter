"""General voltage lifts over semidirect groups, with searched base patterns.

This version replaces the fixed two-orbit pattern with a general search. The base
graph has B left orbits and B right orbits (B = 2, 3 or 4), each of size N, and
every vertex has degree d. Each left orbit i has d darts. Dart (i,t) goes to right
orbit tgt[i][t] with voltage vol[i][t] in a group G of order N. Every right orbit
receives exactly d darts, so the graph is d-regular and bipartite. Vertex count is
2*B*N.

The group G = Z_m x|_r Z_k is enumerated inside C for each order N. The search
uses simulated annealing over both voltages and target patterns. Pattern moves
swap the targets of two darts, which keeps all column sums at d. Simplicity is
handled as a penalty: two darts from the same left orbit to the same right orbit
must have different voltages.

Left translations are automorphisms that act transitively on each orbit. So
diameter <= D is decided by BFS from the 2B representatives L(i,e) and R(j,e).
The C engine re-checks the final graph with a full BFS from every vertex before
printing. Python validates the result again and keeps a valid fallback
(K_{d,d}, the projective plane, or the Araujo-Lopez graph where applicable).
"""
import itertools
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXB 4
#define MAXN 5000
#define MAXV 5000
#define MAXQ (2 * MAXB * MAXN)
#define MAXGR 128
#define MAXCAND 8000
#define PEN 50

typedef struct { int m, k, r; } Grp;
typedef struct { int B, N, V; } Cand;

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

/* ---- group G = Z_m x|_r Z_k, element code a*k+b, (a,b)(c,e) = (a + r^b c, b+e) ---- */
static int GM, GK, GR, N;
static int powr[MAXN];

static void setgroup(int m, int k, int r) {
    GM = m; GK = k; GR = r; N = m * k;
    powr[0] = 1 % m;
    for (int b = 1; b < k; b++) powr[b] = (powr[b - 1] * r) % m;
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int na = (a + powr[b] * c) % GM;
    return na * GK + (b + e) % GK;
}

static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int na = (GM - (powr[nb] * a) % GM) % GM;
    return na * GK + nb;
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static Grp opts[MAXGR];
static int nopt;

static void enum_groups(int n) {
    nopt = 0;
    for (int k = 1; k <= n; k++) {
        if (n % k) continue;
        int m = n / k;
        for (int r = 0; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            long x = 1 % m;
            for (int i = 0; i < k; i++) x = (x * r) % m;
            if (x != 1 % m) continue;
            if (nopt < MAXGR) {
                opts[nopt].m = m; opts[nopt].k = k; opts[nopt].r = r;
                nopt++;
            }
        }
    }
}

/* ---- lift state ---- */
static int B;
static int tgt[MAXB][MAXD], vol[MAXB][MAXD];
static int fw[MAXB][MAXD][MAXN], bw[MAXB][MAXD][MAXN];
static int incI[MAXB][MAXD], incT[MAXB][MAXD];
static int vis[MAXQ], que[MAXQ];
static int stampc = 0;

static void set_vol(int i, int t, int x) {
    vol[i][t] = x;
    int xi = ginv(x);
    for (int g = 0; g < N; g++) {
        fw[i][t][g] = gmul(g, x);
        bw[i][t][g] = gmul(g, xi);
    }
}

static void rebuild_inc(void) {
    int cnt[MAXB] = {0, 0, 0, 0};
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            int j = tgt[i][t];
            incI[j][cnt[j]] = i;
            incT[j][cnt[j]] = t;
            cnt[j]++;
        }
}

/* Number of vertices within distance D of src. */
static int bfs_reach(int src) {
    int BN = B * N;
    stampc++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stampc;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int i = v / N, g = v % N;
                for (int t = 0; t < d; t++) {
                    int u = BN + tgt[i][t] * N + fw[i][t][g];
                    if (vis[u] != stampc) { vis[u] = stampc; que[tail++] = u; }
                }
            } else {
                int w = v - BN, j = w / N, y = w % N;
                for (int k = 0; k < d; k++) {
                    int i = incI[j][k], t = incT[j][k];
                    int u = i * N + bw[i][t][y];
                    if (vis[u] != stampc) { vis[u] = stampc; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

static long violations(void) {
    long v = 0;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++)
            for (int s = t + 1; s < d; s++)
                if (tgt[i][t] == tgt[i][s] && vol[i][t] == vol[i][s]) v++;
    return v;
}

static long cover_cost(void) {
    int V = 2 * B * N;
    long c = 0;
    for (int i = 0; i < B; i++) c += (long)(V - bfs_reach(i * N));
    for (int j = 0; j < B; j++) c += (long)(V - bfs_reach(B * N + j * N));
    return c + PEN * violations();
}

/* ---- random restart + simulated annealing ---- */
static int perm[MAXB * MAXD];

static void random_state(void) {
    int tot = B * d;
    for (int j = 0; j < B; j++)
        for (int c = 0; c < d; c++) perm[j * d + c] = j;
    for (int a = tot - 1; a > 0; a--) {
        int b = rndint(a + 1);
        int t = perm[a]; perm[a] = perm[b]; perm[b] = t;
    }
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) tgt[i][t] = perm[i * d + t];
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) set_vol(i, t, rndint(N));
    rebuild_inc();
}

static int run_restart(double until) {
    random_state();
    long cost = cover_cost();
    if (cost == 0) return 1;
    double c0 = (double)cost;
    double Ts = 0.05 * c0 + 1.0, Te = 0.3;
    const int iters = 12000;
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 15) == 0 && now() > until) return 0;
        double T = Ts * pow(Te / Ts, (double)it / iters);
        if (rnd01() < 0.6) {
            int i = rndint(B), t = rndint(d);
            int old = vol[i][t], x = rndint(N);
            if (x == old) continue;
            set_vol(i, t, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else set_vol(i, t, old);
        } else {
            int i1 = rndint(B), t1 = rndint(d), i2 = rndint(B), t2 = rndint(d);
            if (tgt[i1][t1] == tgt[i2][t2]) continue;
            int a = tgt[i1][t1];
            tgt[i1][t1] = tgt[i2][t2];
            tgt[i2][t2] = a;
            rebuild_inc();
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else {
                a = tgt[i1][t1];
                tgt[i1][t1] = tgt[i2][t2];
                tgt[i2][t2] = a;
                rebuild_inc();
            }
        }
    }
    return cost == 0;
}

/* ---- best state bookkeeping ---- */
static int bestV = 0, bestB, bestN, bestGM, bestGK, bestGR;
static int bestTgt[MAXB][MAXD], bestVol[MAXB][MAXD];

static void record(void) {
    int V = 2 * B * N;
    if (V <= bestV) return;
    bestV = V; bestB = B; bestN = N;
    bestGM = GM; bestGK = GK; bestGR = GR;
    memcpy(bestTgt, tgt, sizeof tgt);
    memcpy(bestVol, vol, sizeof vol);
}

/* Try to find a feasible lift with B orbits per side and group order Nv. */
static int attempt(int Bv, int Nv, double until) {
    enum_groups(Nv);
    if (nopt == 0) return 0;
    B = Bv;
    while (now() < until) {
        Grp g = opts[rndint(nopt)];
        setgroup(g.m, g.k, g.r);
        if (run_restart(until)) {
            record();
            return 1;
        }
    }
    return 0;
}

/* ---- candidates ---- */
static Cand cand[MAXCAND];
static int nc;

static int cmpc(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    return x->V - y->V;
}

static void build_cands(int lo, int hi) {
    nc = 0;
    int Bs[3] = {2, 3, 4};
    for (int bi = 0; bi < 3; bi++) {
        int Bv = Bs[bi];
        for (int n = d; n <= MAXN; n++) {
            int V = 2 * Bv * n;
            if (V < lo) continue;
            if (V > hi) break;
            if (nc < MAXCAND) {
                cand[nc].B = Bv; cand[nc].N = n; cand[nc].V = V;
                nc++;
            }
        }
    }
    qsort(cand, nc, sizeof(Cand), cmpc);
}

/* ---- full verification and output ---- */
static int adjv[MAXV][MAXD];

static int full_check(int V) {
    for (int s = 0; s < V; s++) {
        stampc++;
        int head = 0, tail = 0;
        que[tail++] = s;
        vis[s] = stampc;
        for (int lvl = 0; lvl < D && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int v = que[head++];
                for (int k = 0; k < d; k++) {
                    int u = adjv[v][k];
                    if (vis[u] != stampc) { vis[u] = stampc; que[tail++] = u; }
                }
            }
        }
        if (tail != V) return 0;
    }
    return 1;
}

static int output_best(void) {
    if (bestV == 0) return 0;
    B = bestB;
    setgroup(bestGM, bestGK, bestGR);
    memcpy(tgt, bestTgt, sizeof tgt);
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) set_vol(i, t, bestVol[i][t]);
    rebuild_inc();
    int BN = B * N, V = 2 * BN;
    if (V > MAXV) return 0;
    for (int v = 0; v < BN; v++) {
        int i = v / N, g = v % N;
        for (int t = 0; t < d; t++)
            adjv[v][t] = BN + tgt[i][t] * N + fw[i][t][g];
    }
    for (int w = BN; w < V; w++) {
        int j = (w - BN) / N, y = (w - BN) % N;
        for (int k = 0; k < d; k++) {
            int i = incI[j][k], t = incT[j][k];
            adjv[w][k] = i * N + bw[i][t][y];
        }
    }
    if (!full_check(V)) return 0;
    printf("%d %d\n", V, BN * d);
    for (int v = 0; v < BN; v++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", v, adjv[v][t]);
    return 1;
}

/* ---- main ---- */
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

    if (d < 3 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (hi > MAXV) hi = MAXV;
    if (lo < 2 * d) lo = 2 * d;
    if (lo > hi) {
        printf("0 0\n");
        return 0;
    }
    build_cands(lo, hi);

    /* Binary search over candidate totals, then scan upward. */
    int a = 0, b = nc - 1;
    while (a <= b && now() < t_end) {
        int mid = (a + b) / 2;
        double rem = t_end - now();
        double slice = rem * 0.25;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (attempt(cand[mid].B, cand[mid].N, now() + slice)) a = mid + 1;
        else b = mid - 1;
    }
    int fails = 0;
    for (int idx = 0; idx < nc && now() < t_end && fails < 2; idx++) {
        if (cand[idx].V <= bestV) continue;
        double rem = t_end - now();
        double slice = rem * 0.5;
        if (slice > rem) slice = rem;
        if (attempt(cand[idx].B, cand[idx].N, now() + slice)) fails = 0;
        else fails++;
    }

    if (!output_best()) printf("0 0\n");
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

    # General voltage lifts over semidirect groups with searched base patterns.
    if d >= 3 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        lo = best[0] + 1
        hi = min(mb, 5000)
        if budget > 3.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 10.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass  # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
