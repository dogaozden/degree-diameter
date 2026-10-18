"""Mixed-base lifts over semidirect groups Z_m x|_r Z_k for the bipartite degree-diameter problem.

Change from the parent: instead of one-vertex-per-side Haar graphs, the C engine searches
base graphs with s = 1, 2 or 3 left vertices and s right vertices. Each left base vertex has
d darts, and the dart targets form a random s x s matrix with all row and column sums d.
Each dart carries a group voltage, and the lift is

    (i, x) ~ (j, x*g)   for each dart (i -> j, g).

Left translations are automorphisms, so the diameter check needs only BFS from the 2s base
vertices. Candidate orders n = 2*s*|G| are scanned in ascending order, starting from a band
well below the record, so an early valid result is kept as a safety net. Simulated annealing
moves change voltages and swap dart targets between slots, which keeps every degree at d.
If the engine finds nothing valid, the Python side falls back to the best construction it has,
and K_{d,d} is the last resort.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Mixed-base voltage lift search over Z_m x|_r Z_k.
 * Usage: prog d D seed time_limit lo_n hi_n     (stdin ignored)
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXS 3
#define MAXD 32
#define MAXV (2 * MAXS * MAXN)
#define MAXCAND 300000

typedef struct { int m, k, r, s; long n; uint32_t key; } Cand;

static int d, D, NS, sN, VN;
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

static long gcdl(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}
static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* ------------------------------------------------------------ group Z_m x|_r Z_k */

static int gm, gk, gr, gN;
static int pw[MAXN];

/* Element (a, b) is coded a*k + b. Product: (a,b)(c,e) = (a + r^b c, b + e). */
static void setup_group(int m, int k, int r) {
    gm = m;
    gk = k;
    gr = r;
    gN = m * k;
    long p = 1 % m;
    for (int b = 0; b < k; b++) {
        pw[b] = (int)p;
        p = (p * r) % m;
    }
}

static inline int gmul(int x, int y) {
    int a = x / gk, b = x - a * gk;
    int c = y / gk, e = y - c * gk;
    int na = (a + (int)(((long)pw[b] * c) % gm)) % gm;
    int nb = b + e;
    if (nb >= gk) nb -= gk;
    return na * gk + nb;
}

static int ginv_(int x) {
    int a = x / gk, b = x - a * gk;
    int nb = (gk - b) % gk;
    int na = (int)(((long)pw[nb] * a) % gm);
    na = (gm - na) % gm;
    return na * gk + nb;
}

/* ------------------------------------------------------------ lift state */

static int tgt[MAXS][MAXD], vol[MAXS][MAXD];
static int btgt[MAXS][MAXD], bvol[MAXS][MAXD];
static int RI[MAXS][MAXD], RG[MAXS][MAXD];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

/* Vertices: left (i, x) = i*gN + x; right (j, y) = sN + j*gN + y.
 * Dart (i -> j, g) joins (i, x) to (j, x*g). */
static void build_right(void) {
    int cnt[MAXS];
    for (int j = 0; j < NS; j++) cnt[j] = 0;
    for (int i = 0; i < NS; i++)
        for (int k = 0; k < d; k++) {
            int j = tgt[i][k];
            int c = cnt[j]++;
            if (c >= d) continue;   /* caps are kept at d by construction */
            RI[j][c] = i;
            RG[j][c] = ginv_(vol[i][k]);
        }
}

/* Number of vertices within distance D of src. */
static int ball_count(int src) {
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < sN) {
                int i = v / gN, x = v - i * gN;
                for (int k = 0; k < d; k++) {
                    int u = sN + tgt[i][k] * gN + gmul(x, vol[i][k]);
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int idx = v - sN;
                int j = idx / gN, y = idx - j * gN;
                for (int c = 0; c < d; c++) {
                    int u = RI[j][c] * gN + gmul(y, RG[j][c]);
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Sum of unreached counts from the 2s base vertices (enough by left-translation symmetry). */
static long cost_state(void) {
    build_right();
    long c = 0;
    for (int i = 0; i < NS; i++) c += VN - ball_count(i * gN);
    for (int j = 0; j < NS; j++) c += VN - ball_count(sN + j * gN);
    return c;
}

/* Slot (i,k) voltage must differ from every other slot with the same target. */
static int slot_ok(int i, int k) {
    int j = tgt[i][k], g = vol[i][k];
    for (int i2 = 0; i2 < NS; i2++)
        for (int k2 = 0; k2 < d; k2++) {
            if (i2 == i && k2 == k) continue;
            if (tgt[i2][k2] == j && vol[i2][k2] == g) return 0;
        }
    return 1;
}

/* Random dart targets with row sums d and column sums d, then distinct voltages per cell. */
static int init_state(void) {
    int cap[MAXS];
    for (int j = 0; j < NS; j++) cap[j] = d;
    for (int i = 0; i < NS; i++)
        for (int k = 0; k < d; k++) {
            int j;
            do { j = rndint(NS); } while (cap[j] == 0);
            cap[j]--;
            tgt[i][k] = j;
        }
    for (int i = 0; i < NS; i++)
        for (int k = 0; k < d; k++) vol[i][k] = rndint(gN);
    for (int round = 0; round < 500; round++) {
        int bad = 0;
        for (int i = 0; i < NS; i++)
            for (int k = 0; k < d; k++)
                if (!slot_ok(i, k)) { vol[i][k] = rndint(gN); bad = 1; }
        if (!bad) return 1;
    }
    return 0;
}

/* Simulated annealing over voltages and dart-target swaps. Returns 1 with tgt/vol at a
 * zero-cost (diameter <= D) state, 0 on timeout. */
static int search_cand(double until) {
    const int ITER = 2500;
    while (now() < until) {
        if (!init_state()) continue;
        long cost = cost_state();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < ITER && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) break;
            double T = Ts * pow(Te / Ts, (double)it / ITER);
            if (rndint(2) == 0) {
                int i = rndint(NS), k = rndint(d);
                int old = vol[i][k];
                int g = rndint(gN);
                if (g == old) continue;
                vol[i][k] = g;
                if (!slot_ok(i, k)) { vol[i][k] = old; continue; }
                long c2 = cost_state();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else vol[i][k] = old;
            } else {
                int i = rndint(NS), k = rndint(d);
                int i2 = rndint(NS), k2 = rndint(d);
                int j1 = tgt[i][k], j2 = tgt[i2][k2];
                if (j1 == j2) continue;
                tgt[i][k] = j2;
                tgt[i2][k2] = j1;
                if (!slot_ok(i, k) || !slot_ok(i2, k2)) {
                    tgt[i][k] = j1;
                    tgt[i2][k2] = j2;
                    continue;
                }
                long c2 = cost_state();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else {
                    tgt[i][k] = j1;
                    tgt[i2][k2] = j2;
                }
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ candidates */

static Cand cand[MAXCAND];
static int nc = 0;

static void add_cand(int m, int k, int r, int s, long n) {
    if (nc >= MAXCAND) return;
    cand[nc].m = m;
    cand[nc].k = k;
    cand[nc].r = r;
    cand[nc].s = s;
    cand[nc].n = n;
    cand[nc].key = (uint32_t)(rnd() >> 33);
    nc++;
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->n != y->n) return x->n < y->n ? -1 : 1;
    if (x->key != y->key) return x->key < y->key ? -1 : 1;
    return 0;
}

static void apply_cand(const Cand *c) {
    setup_group(c->m, c->k, c->r);
    NS = c->s;
    sN = NS * gN;
    VN = 2 * sN;
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
    t_end = t0 + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (lo < 2) lo = 2;

    for (int s = 1; s <= MAXS; s++) {
        long Nlo = (lo + 2L * s - 1) / (2L * s), Nhi = hi / (2L * s);
        if (Nlo < d + 1) Nlo = d + 1;
        if (Nhi > MAXN) Nhi = MAXN;
        for (long N = Nlo; N <= Nhi; N++) {
            for (long m = 1; m <= N; m++) {
                if (N % m) continue;
                long k = N / m;
                if (m == 1) {
                    add_cand(1, (int)k, 0, s, 2L * s * N);
                    continue;
                }
                for (long r = 1; r < m; r++) {
                    if (gcdl(r, m) != 1) continue;
                    if (powmod(r, k, m) != 1) continue;
                    add_cand((int)m, (int)k, (int)r, s, 2L * s * N);
                }
            }
        }
    }
    if (nc == 0) {
        printf("0 0\n");
        return 0;
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    long bestn = 0;
    Cand bestc;
    memset(&bestc, 0, sizeof bestc);
    for (int pass = 0; pass < 1000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            if (cand[ci].n <= bestn) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = 0.15 * rem;
            if (slice < 0.8) slice = 0.8;
            if (slice > rem) slice = rem;
            apply_cand(&cand[ci]);
            if (search_cand(now() + slice)) {
                bestn = cand[ci].n;
                bestc = cand[ci];
                memcpy(btgt, tgt, sizeof tgt);
                memcpy(bvol, vol, sizeof vol);
            }
        }
        if (!tried || t_end - now() < 0.3) break;
    }

    if (bestn == 0) {
        printf("0 0\n");
        return 0;
    }
    apply_cand(&bestc);
    memcpy(tgt, btgt, sizeof tgt);
    memcpy(vol, bvol, sizeof vol);
    printf("%d %d\n", VN, sN * d);
    for (int i = 0; i < NS; i++)
        for (int k = 0; k < d; k++) {
            int j = tgt[i][k], g = vol[i][k];
            for (int x = 0; x < gN; x++)
                printf("%d %d\n", i * gN + x, sN + j * gN + gmul(x, g));
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

    # Search: mixed-base voltage lifts over Z_m x|_r Z_k, ascending in order from a band
    # below the record, so an early valid result is kept as a safety net.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.80 * time_limit - (time.monotonic() - t0) - 3.0
        lo = max(best[0] + 1, mb // 5)
        hi = mb // 2
        if budget > 3.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the best valid graph found so far

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
