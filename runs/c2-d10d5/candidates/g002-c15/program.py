"""Bi-Cayley lift search with a C annealing engine.

The bi-Cayley annealer over Z_m x| Z_k2 runs inside the C engine. Its diameter
check is a bit-parallel reach from the 2K block identities (one uint32 per
vertex). This version adds snapshot restarts: when an annealing run stagnates,
it returns to the best state it saw and perturbs a few darts, instead of
discarding the run and starting from a random lift. Python handles the exact
constructions (PG, GQ, cycle, K_{d,d}) and validates every output.
"""
import itertools
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

/* Bi-Cayley lift annealer over Z_m x| Z_k2.
 * Vertices: A_{i,g} = i*G+g (i<K), B_{j,h} = (K+j)*G+h, G = Z_m x| Z_k2 order.
 * Layer l: A_{i,g} ~ B_{lay[l][i], g*vol[l][i]}. Each layer is a perfect matching
 * between A-blocks and B-blocks, so degree is exactly L unless duplicate darts occur
 * (penalised). Left multiplication is an automorphism, so diameter <= D is equivalent
 * to: every vertex is within D of every block identity. That is checked with
 * bit-parallel reach masks (bit b of reach[v] = identity of block b within distance t).
 *
 * Restarts: the annealer keeps a snapshot (lay, vol) of the lowest-cost state seen in
 * the current run. On stagnation it reloads the snapshot, perturbs a few darts and
 * continues, up to MAXRE times.
 */

#define KMAX 4
#define PEN 1000.0
#define ITERS 12000L
#define PATIENCE 2500L
#define MAXRE 3
#define NPERTURB 4

static uint64_t rs = 1;
static uint64_t rnd64(void) {
    uint64_t z = (rs += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static clock_t t0;
static double budget_s;
static double elapsed(void) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

static int dd, Dd;          /* degree and diameter */
static int gm, gk2, Gord;   /* group Z_gm x| Z_gk2, order Gord = gm*gk2 */
static int *pw;             /* pw[b] = r^b mod gm */
static int K, NV, L;
static int *lay, *ilay, *vol, *nbr;
static int *slay, *svol;    /* snapshot of lay and vol */
static uint32_t *stR, *candR, *scrA, *scrB;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;
static int trials[KMAX + 1], wins[KMAX + 1];

static int popc32(uint32_t x) {
    x = x - ((x >> 1) & 0x55555555u);
    x = (x & 0x33333333u) + ((x >> 2) & 0x33333333u);
    x = (x + (x >> 4)) & 0x0F0F0F0Fu;
    return (int)((x * 0x01010101u) >> 24);
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* (a,b)*(c,e) = (a + r^b c, b + e), element index a*k2+b. */
static int gmul(int x, int y) {
    int a1 = x / gk2, b1 = x % gk2, a2 = y / gk2, b2 = y % gk2;
    int a = (int)(((long long)a1 + (long long)pw[b1] * a2) % gm);
    int b = (b1 + b2) % gk2;
    return a * gk2 + b;
}

/* Inverse of (a,b) is (-r^{-b} a, -b). */
static int ginv(int x) {
    int a = x / gk2, b = x % gk2;
    int nb = (gk2 - b) % gk2;
    long long t = ((long long)pw[nb] * a) % gm;
    int na = (int)((gm - t) % gm);
    return na * gk2 + nb;
}

static void sample_group(int target, int *om, int *ok2, int *orr) {
    static const int K2S[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    for (int att = 0; att < 200; att++) {
        int k2 = K2S[rndint(20)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rnd01() < 0.3) {
            r = (m >= 3) ? m - 1 : 1;   /* dihedral: (m-1)^2 = 1 mod m always */
        } else {
            r = -1;
            if (m > 2) {
                for (int t = 0; t < 60; t++) {
                    int c = 2 + rndint(m - 2);
                    if (gcdi(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
                }
            }
            if (r < 0) continue;
        }
        *om = m; *ok2 = k2; *orr = r;
        return;
    }
    *om = (target < 2) ? 2 : target;
    *ok2 = 1;
    *orr = 1;
}

static void setup_group(int m, int k2, int r, int k) {
    gm = m; gk2 = k2; Gord = m * k2;
    K = k; L = dd; NV = 2 * K * Gord;
    pw = (int *)malloc(sizeof(int) * (size_t)k2);
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    lay = (int *)malloc(sizeof(int) * (size_t)(L * K));
    ilay = (int *)malloc(sizeof(int) * (size_t)(L * K));
    vol = (int *)malloc(sizeof(int) * (size_t)(L * K));
    slay = (int *)malloc(sizeof(int) * (size_t)(L * K));
    svol = (int *)malloc(sizeof(int) * (size_t)(L * K));
    nbr = (int *)malloc(sizeof(int) * (size_t)L * (size_t)NV);
    stR = (uint32_t *)malloc(sizeof(uint32_t) * (size_t)NV);
    candR = (uint32_t *)malloc(sizeof(uint32_t) * (size_t)NV);
    scrA = (uint32_t *)malloc(sizeof(uint32_t) * (size_t)NV);
    scrB = (uint32_t *)malloc(sizeof(uint32_t) * (size_t)NV);
}

static void free_group(void) {
    free(pw); free(lay); free(ilay); free(vol); free(slay); free(svol); free(nbr);
    free(stR); free(candR); free(scrA); free(scrB);
    pw = NULL; lay = NULL; ilay = NULL; vol = NULL; slay = NULL; svol = NULL; nbr = NULL;
    stR = NULL; candR = NULL; scrA = NULL; scrB = NULL;
}

/* Write layer l neighbours of A-block i and B-block lay[l][i] from voltage vol[l][i]. */
static void set_dart(int l, int i) {
    int j = lay[l * K + i], s = vol[l * K + i];
    int *nb = nbr + (size_t)l * NV;
    int is = ginv(s);
    for (int g = 0; g < Gord; g++) {
        nb[i * Gord + g] = (K + j) * Gord + gmul(g, s);
        nb[(K + j) * Gord + g] = i * Gord + gmul(g, is);
    }
}

static void swap_lay(int l, int i1, int i2) {
    int *lp = lay + l * K;
    int *ip = ilay + l * K;
    int j1 = lp[i1], j2 = lp[i2];
    lp[i1] = j2; lp[i2] = j1;
    ip[j2] = i1; ip[j1] = i2;
}

static void take_snapshot(void) {
    memcpy(slay, lay, sizeof(int) * (size_t)(L * K));
    memcpy(svol, vol, sizeof(int) * (size_t)(L * K));
}

static void load_snapshot(void) {
    for (int l = 0; l < L; l++)
        for (int i = 0; i < K; i++) {
            int j = slay[l * K + i];
            lay[l * K + i] = j;
            ilay[l * K + j] = i;
            vol[l * K + i] = svol[l * K + i];
        }
    for (int l = 0; l < L; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

static void random_init(void) {
    int *perm = (int *)malloc(sizeof(int) * (size_t)K);
    for (int l = 0; l < L; l++) {
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            lay[l * K + i] = perm[i];
            ilay[l * K + perm[i]] = i;
            vol[l * K + i] = rndint(Gord);
        }
    }
    free(perm);
    for (int l = 0; l < L; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < L; l1++)
            for (int l2 = l1 + 1; l2 < L; l2++)
                if (lay[l1 * K + i] == lay[l2 * K + i] && vol[l1 * K + i] == vol[l2 * K + i]) c++;
    return c;
}

static double total_cost(const uint32_t *r) {
    long long s = 0;
    for (int v = 0; v < NV; v++) s += 2 * K - popc32(r[v]);
    return (double)s + PEN * (double)dupcount();
}

/* Reach masks after Dd rounds, written to out. */
static void compute_reach(uint32_t *out) {
    uint32_t *X = scrA, *Y = scrB;
    memset(X, 0, sizeof(uint32_t) * (size_t)NV);
    for (int b = 0; b < 2 * K; b++) X[(size_t)b * Gord] = 1u << b;
    for (int t = 0; t < Dd; t++) {
        int changed = 0;
        for (int v = 0; v < NV; v++) {
            uint32_t x = X[v];
            for (int l = 0; l < L; l++) x |= X[nbr[(size_t)l * NV + v]];
            Y[v] = x;
            changed |= (x != X[v]);
        }
        uint32_t *tmp = X; X = Y; Y = tmp;
        if (!changed) break;
    }
    memcpy(out, X, sizeof(uint32_t) * (size_t)NV);
}

static int accept(double c2, double c, double temp) {
    if (c2 <= c) return 1;
    return rnd01() < exp(-(c2 - c) / temp);
}

/* One annealing run from a random lift, with snapshot restarts on stagnation.
 * Returns 1 when the lift is valid (state kept). */
static int sa_run(void) {
    random_init();
    compute_reach(stR);
    double cost = total_cost(stR);
    double c0 = cost > 1.0 ? cost : 1.0;
    double bestc = cost;
    double snapc = cost;
    long last = 0;
    int restarts = 0;
    uint32_t full = (uint32_t)((1ull << (2 * K)) - 1ull);
    take_snapshot();

    for (long t = 0; t < ITERS; t++) {
        if (cost == 0.0) break;
        if ((t & 31) == 0 && elapsed() > budget_s) break;
        if (t - last > PATIENCE) {
            if (restarts >= MAXRE) break;
            restarts++;
            load_snapshot();
            for (int p = 0; p < NPERTURB; p++) {
                int l = rndint(L), i = rndint(K);
                vol[l * K + i] = rndint(Gord);
                set_dart(l, i);
            }
            compute_reach(stR);
            cost = total_cost(stR);
            bestc = cost;
            last = t;
            continue;
        }
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)ITERS);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(L);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            swap_lay(l, i1, i2);
            set_dart(l, i1);
            set_dart(l, i2);
            compute_reach(candR);
            double c2 = total_cost(candR);
            if (accept(c2, cost, temp)) {
                uint32_t *tmp = stR; stR = candR; candR = tmp;
                cost = c2;
                if (cost < bestc) { bestc = cost; last = t; }
                if (cost < snapc) { snapc = cost; take_snapshot(); }
            } else {
                swap_lay(l, i1, i2);
                set_dart(l, i1);
                set_dart(l, i2);
            }
            continue;
        }

        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            int off = rndint(NV);
            for (int q = 0; q < NV; q++) {
                int v = off + q;
                if (v >= NV) v -= NV;
                if (stR[v] != full) {
                    int b = v / Gord;
                    l = rndint(L);
                    if (b < K) i = b;
                    else i = ilay[l * K + (b - K)];
                    break;
                }
            }
        }
        if (l < 0) {
            l = rndint(L);
            i = rndint(K);
        }
        int old = vol[l * K + i];
        int nw = rndint(Gord);
        if (nw == old) continue;
        vol[l * K + i] = nw;
        set_dart(l, i);
        compute_reach(candR);
        double c2 = total_cost(candR);
        if (accept(c2, cost, temp)) {
            uint32_t *tmp = stR; stR = candR; candR = tmp;
            cost = c2;
            if (cost < bestc) { bestc = cost; last = t; }
            if (cost < snapc) { snapc = cost; take_snapshot(); }
        } else {
            vol[l * K + i] = old;
            set_dart(l, i);
        }
    }
    return cost == 0.0;
}

static int pick_K(void) {
    if (rnd01() < 0.2) return 1 + rndint(KMAX);
    int bk = 1;
    double bs = -1.0;
    for (int k = 1; k <= KMAX; k++) {
        double s = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (s > bs) { bs = s; bk = k; }
    }
    return bk;
}

static void store_current(void) {
    int m = K * Gord * L;
    int *e = (int *)malloc(sizeof(int) * 2 * (size_t)m);
    int c = 0;
    for (int u = 0; u < K * Gord; u++)
        for (int l = 0; l < L; l++) {
            e[2 * c] = u;
            e[2 * c + 1] = nbr[(size_t)l * NV + u];
            c++;
        }
    free(best_e);
    best_e = e;
    best_m = m;
    best_n = NV;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    Dd = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    budget_s = atof(argv[4]);
    rs = seed * 0x2545F4914F6CDD1DULL + 0x1234567ULL;
    t0 = clock();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 > 0 && m0 > 0) {
        best_e = (int *)malloc(sizeof(int) * 2 * (size_t)m0);
        int c = 0;
        for (int q = 0; q < m0; q++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) break;
            best_e[2 * c] = u;
            best_e[2 * c + 1] = v;
            c++;
        }
        best_n = n0;
        best_m = c;
    }

    if (dd >= 1 && Dd >= 1) {
        while (elapsed() < budget_s) {
            int k = pick_K();
            int base = best_n / (2 * k);
            int spread = base / 8 + 1;
            if (spread < 2) spread = 2;
            int target = base + 1 + rndint(spread);
            if (target < 2) target = 2;
            int m, k2, r;
            sample_group(target, &m, &k2, &r);
            if (2LL * k * m * k2 <= best_n) continue;
            trials[k]++;
            setup_group(m, k2, r, k);
            int ok = sa_run();
            if (ok) {
                wins[k]++;
                if (NV > best_n) store_current();
            }
            free_group();
        }
    }

    printf("%d %d\n", best_n, best_m);
    for (int q = 0; q < best_m; q++) printf("%d %d\n", best_e[2 * q], best_e[2 * q + 1]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions (Python).
# ----------------------------------------------------------------------------

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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()

    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle: degree 2, diameter D, bipartite
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe baseline: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() - t_start < 0.4 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # C annealer: start from the best graph so far, budget leaves margin for
    # compilation, output parsing and validation.
    remaining = time_limit - (time.monotonic() - t_start)
    budget = min(0.8 * time_limit - 2.0, remaining - 6.0)
    if budget >= 2.0:
        try:
            text = lib.run_c(
                C_SOURCE,
                [d, D, int(seed) % (1 << 31), round(budget, 2)],
                stdin_graph=best,
                timeout=max(1.0, remaining - 2.0),
            )
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
