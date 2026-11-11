"""Multi-orbit voltage lifts over semidirect groups for the bipartite degree-diameter problem.

Construction. Pick a group G of order |G| = m*kk, given as Z_m x|_r Z_kk with r^kk = 1 mod m.
Pick a block size K in {1, 2, 3} and a K x K pattern M of nonnegative integers whose rows and
columns each sum to d (a random sum of d permutation matrices). Block (i, j) gets M[i][j]
distinct connection elements of G. Vertices are A_{i,g} = i*G + g and B_{j,h} = K*G + j*G + h.
The edges are A_{i,g} ~ B_{j, g*x} for each element x in block (i, j).

Every vertex has degree d, and the graph is bipartite and simple. Left multiplication is an
automorphism that is transitive on each of the 2K vertex classes, so the diameter is at most D
exactly when BFS from the 2K representatives A_{i,e} and B_{j,e} reaches every vertex within D
steps. Simulated annealing over the block elements and the pattern minimises the number of
unreached (representative, vertex) pairs.

Compared with the single-block Haar lift this family adds two things: several vertex orbits
per side (K = 2 or 3), and the freedom of the pattern M. Candidate (K, group) pairs are sorted
by total order, and a binary search with equal time slices looks for the largest feasible order.
Python keeps the projective-plane, Araujo-Lopez and W(q) baselines and the K_{d,d} fallback.
Every returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit voltage-lift search over Z_m x|_r Z_kk.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo, hi bound the total vertex count. Output: "n m" then m lines "u v", or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 2800
#define MAXK 3
#define MAXD 32
#define MAXKK 48
#define MAXSLOT (MAXK * MAXD)
#define MAXV (2 * MAXK * MAXG)
#define MAXCAND 120000

typedef struct { int m, r, kk, K, V, key; } Cand;

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

static long pw_mod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}
static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

/* ------------------------------------------------------------ group tables */

static uint16_t MT[MAXG][MAXG];
static int INVT[MAXG];
static int G, K, nslot, CURM, CURR, CURKK;

/* Element (a, b) is coded a*kk + b; (a,b)(c,e) = (a + r^b c, b + e). */
static void setup_group(int m, int r, int kk) {
    G = m * kk;
    CURM = m;
    CURR = r;
    CURKK = kk;
    int PWv[MAXKK];
    for (int b = 0; b < kk; b++) PWv[b] = (int)pw_mod(r, b, m);
    for (int x = 0; x < G; x++) {
        int a = x / kk, b = x % kk;
        for (int y = 0; y < G; y++) {
            int c = y / kk, e = y % kk;
            int na = (a + PWv[b] * c) % m;
            int nb = (b + e) % kk;
            int z = na * kk + nb;
            MT[x][y] = (uint16_t)z;
            if (z == 0) INVT[x] = y;
        }
    }
}

/* ------------------------------------------------------------ structure state */

static int sx[MAXSLOT], sbi[MAXSLOT], sbj[MAXSLOT];
static int rowSlot[MAXK][MAXD], colSlot[MAXK][MAXD];
static int fwd[MAXSLOT][MAXG], bwd[MAXSLOT][MAXG];
static int Mpat[MAXK][MAXK];
static int vis[MAXV], que[MAXV], stampv = 0;

static void set_slot(int s, int x) {
    sx[s] = x;
    int xi = INVT[x];
    for (int g = 0; g < G; g++) {
        fwd[s][g] = MT[g][x];
        bwd[s][g] = MT[g][xi];
    }
}

/* Vertices: A_{i,g} = i*G + g, B_{j,h} = K*G + j*G + h. */
static int reach_count(int src) {
    int KG = K * G;
    stampv++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stampv;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < KG) {
                int i = v / G, g = v - i * G;
                for (int t = 0; t < d; t++) {
                    int s = rowSlot[i][t];
                    int u = KG + sbj[s] * G + fwd[s][g];
                    if (vis[u] != stampv) { vis[u] = stampv; que[tail++] = u; }
                }
            } else {
                int w = v - KG;
                int j = w / G, h = w - j * G;
                for (int t = 0; t < d; t++) {
                    int s = colSlot[j][t];
                    int u = sbi[s] * G + bwd[s][h];
                    if (vis[u] != stampv) { vis[u] = stampv; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Sum over the 2K orbit representatives of the number of vertices beyond distance D. */
static long cover_cost(void) {
    long V = 2L * K * G, c = 0;
    for (int i = 0; i < K; i++) c += V - reach_count(i * G);
    for (int j = 0; j < K; j++) c += V - reach_count(K * G + j * G);
    return c;
}

/* Random nonnegative K x K pattern with all row and column sums d (sum of d permutations). */
static void random_pattern(void) {
    memset(Mpat, 0, sizeof Mpat);
    for (int rep = 0; rep < d; rep++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < K; i++) Mpat[i][perm[i]]++;
    }
}

static void build_structure(void) {
    int cr[MAXK] = {0}, cc[MAXK] = {0};
    nslot = 0;
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            for (int c = 0; c < Mpat[i][j]; c++) {
                sbi[nslot] = i;
                sbj[nslot] = j;
                rowSlot[i][cr[i]++] = nslot;
                colSlot[j][cc[j]++] = nslot;
                nslot++;
            }
}

/* True if element x is already used by a slot t < lim in the same block as s. */
static int conflicts(int s, int x, int lim) {
    for (int t = 0; t < lim; t++)
        if (t != s && sbi[t] == sbi[s] && sbj[t] == sbj[s] && sx[t] == x) return 1;
    return 0;
}

static void random_elements(void) {
    for (int s = 0; s < nslot; s++) {
        int x;
        do { x = rndint(G); } while (conflicts(s, x, s));
        set_slot(s, x);
    }
}

/* Annealing over the pattern restarts and block elements for the current group.
 * Returns 1 when the cost reaches 0 (diameter <= D); the state is then the solution. */
static int search_group(double until) {
    while (now() < until) {
        random_pattern();
        build_structure();
        random_elements();
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        const int iters = 3000;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 7) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int s = rndint(nslot);
            int x = rndint(G);
            if (x == sx[s] || conflicts(s, x, nslot)) continue;
            int old = sx[s];
            set_slot(s, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else set_slot(s, old);
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ best solution */

static int bestV = 0, bestK, bestM, bestR, bestKK, bestNslot;
static int bestSbi[MAXSLOT], bestSbj[MAXSLOT], bestSx[MAXSLOT];

static void copy_best(int V) {
    bestV = V;
    bestK = K;
    bestM = CURM;
    bestR = CURR;
    bestKK = CURKK;
    bestNslot = nslot;
    for (int s = 0; s < nslot; s++) {
        bestSbi[s] = sbi[s];
        bestSbj[s] = sbj[s];
        bestSx[s] = sx[s];
    }
}

static void print_best(void) {
    if (bestV == 0) { printf("0 0\n"); return; }
    setup_group(bestM, bestR, bestKK);
    K = bestK;
    int V = 2 * K * G;
    long E = (long)bestNslot * G;
    printf("%d %ld\n", V, E);
    for (int s = 0; s < bestNslot; s++) {
        int i = bestSbi[s], j = bestSbj[s], x = bestSx[s];
        for (int g = 0; g < G; g++)
            printf("%d %d\n", i * G + g, K * G + j * G + (int)MT[g][x]);
    }
}

/* ------------------------------------------------------------ candidates */

static Cand *cand;
static int nc = 0;

static void add_cand(int m, int r, int kk, int k, int V) {
    if (nc >= MAXCAND) return;
    cand[nc].m = m;
    cand[nc].r = r;
    cand[nc].kk = kk;
    cand[nc].K = k;
    cand[nc].V = V;
    cand[nc].key = (int)(rnd() >> 40);
    nc++;
}

static int cmp_cand(const void *A, const void *B) {
    const Cand *x = A, *y = B;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
    if (x->key != y->key) return x->key < y->key ? -1 : 1;
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
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }

    cand = malloc(sizeof(Cand) * MAXCAND);
    if (!cand) { printf("0 0\n"); return 0; }

    /* Groups Z_m x|_r Z_kk with r^kk = 1 mod m, for every block size K in 1..MAXK. */
    for (int kk = 1; kk <= MAXKK; kk++)
        for (int m = 2; m * kk <= MAXG; m++) {
            int G0 = m * kk;
            int any = 0;
            for (int k = 1; k <= MAXK; k++) {
                int V = 2 * k * G0;
                if (V >= lo && V <= hi) any = 1;
            }
            if (!any) continue;
            int want = (kk == 1) ? 1 : 2, got = 0;
            int start = rndint(m);
            for (int t = 0; t < m && got < want; t++) {
                int r = (start + t) % m;
                if (r == 0) continue;
                if (gcd_l(r, m) != 1) continue;
                if (pw_mod(r, kk, m) != 1 % m) continue;
                got++;
                for (int k = 1; k <= MAXK; k++) {
                    int V = 2 * k * G0;
                    if (V >= lo && V <= hi) add_cand(m, r, kk, k, V);
                }
            }
        }

    if (nc == 0) {
        printf("0 0\n");
        return 0;
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Phase 1: binary search over candidates sorted by order. Each probe gets an equal
     * share of the remaining time for the probes still needed. */
    int a = 0, b = nc - 1;
    while (a <= b && now() < t_end) {
        int mid = (a + b) / 2;
        int span = b - a + 1;
        int probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = t_end - now();
        double slice = rem / (probes + 1);
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        Cand c = cand[mid];
        setup_group(c.m, c.r, c.kk);
        K = c.K;
        if (search_group(now() + slice)) {
            if (c.V > bestV) copy_best(c.V);
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }

    /* Phase 2: spend leftover time on the next few candidates above the best. */
    int fails = 0, idx = a;
    while (idx < nc && now() < t_end && fails < 3) {
        Cand c = cand[idx];
        idx++;
        if (c.V <= bestV) continue;
        double rem = t_end - now();
        double slice = rem * 0.35;
        if (slice < 0.5) break;
        setup_group(c.m, c.r, c.kk);
        K = c.K;
        if (search_group(now() + slice)) {
            copy_best(c.V);
            fails = 0;
        } else {
            fails++;
        }
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

    # Multi-orbit voltage lifts over semidirect groups. The vertex count is at most the
    # Moore bound, and the search window is capped at 3600 to focus the probes.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, mb // 8)
        hi = min(mb, 3600)
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
