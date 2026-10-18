"""Multi-orbit affine lifts for the bipartite degree-diameter problem.

New construction in this version: the B-orbit pattern is no longer a fixed
two-orbit split. Each side is split into B orbits of the affine group
G = F_q x| H, |G| = N = q*c. The pattern matrix M, where M[i][j] is the number
of darts from left orbit i to right orbit j, is a sum of d random permutation
matrices of size B. Every row and column of M then sums to d, so the lift is
d-regular and bipartite. Each dart (i,t) carries a voltage x in G, with
L_(i,g) ~ R_(j, g*x). The graph has 2BN vertices.

Left and right translations by G are automorphisms, so the diameter is at most
D iff BFS from one representative per orbit (2B BFS runs) reaches every vertex
within D steps. Simulated annealing searches the voltages, and every restart
draws a fresh random pattern. The two-orbit fixed pattern is the special case
B = 2. The C engine tries B = 3, 1, 2, 4 in turn, then extends the best B to
larger N. Before output it runs a full BFS check when the graph is small.
Python checks the result with lib.is_valid and keeps a valid fallback.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit affine lifts.
 * Group G = F_q x| H, |G| = N = q*c with c >= 2 and c | q-1.
 * B orbits per side (1 <= B <= 4). Left vertex (i,g) ~ right vertex (j, g*v)
 * for each dart (i,t) with tgt[i][t] = j and voltage v = vol[i][t].
 * Pattern: M = sum of d random permutation matrices of size B.
 * Usage: prog d D seed time_limit lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4
 * Output: "n m" then m lines "u v", or "0 0".
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
#define MAXN 4800
#define MAXD 32
#define MAXB 4
#define MAXCAND 16384

typedef struct { int q, p, k, c, N; } Cand;

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

/* ------------------------------------------------------------ group G = F_q x| H */

static int GQ, GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

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

/* ------------------------------------------------------------ multi-orbit lift state */

static int curB;
static int tgt[MAXB][MAXD], vol[MAXB][MAXD];
static int fw[MAXB][MAXD][MAXN], bw[MAXB][MAXD][MAXN];
static int incI[MAXB][MAXD], incT[MAXB][MAXD];
static int vis[2 * MAXB * MAXN], que[2 * MAXB * MAXN];
static int stamp_ = 0;

static int bestTotal = 0, bestB, bestN, bestQ, bestP, bestK, bestC;
static int bestTgt[MAXB][MAXD], bestVol[MAXB][MAXD];

/* Right orbit j receives darts (incI[j][k], incT[j][k]); the count is d. */
static void build_incidence(int B) {
    for (int j = 0; j < B; j++) {
        int cnt = 0;
        for (int i = 0; i < B; i++)
            for (int t = 0; t < d; t++)
                if (tgt[i][t] == j && cnt < MAXD) {
                    incI[j][cnt] = i;
                    incT[j][cnt] = t;
                    cnt++;
                }
    }
}

/* New pattern: M = sum of d random permutation matrices of size B.
 * Row and column sums equal d, so each side is d-regular. */
static void set_random_pattern(int B) {
    int M[MAXB][MAXB];
    memset(M, 0, sizeof M);
    for (int k = 0; k < d; k++) {
        int p[MAXB];
        for (int i = 0; i < B; i++) p[i] = i;
        for (int i = B - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < B; i++) M[i][p[i]]++;
    }
    for (int i = 0; i < B; i++) {
        int t = 0;
        for (int j = 0; j < B; j++)
            for (int c = 0; c < M[i][j]; c++) tgt[i][t++] = j;
    }
    build_incidence(B);
}

/* Voltage of dart (i,t) is x; fw maps L-coordinate g to R-coordinate g*x,
 * bw maps R-coordinate y to L-coordinate y*x^-1. */
static void set_dart(int i, int t, int x) {
    vol[i][t] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fw[i][t][g] = gmul(g, x);
        bw[i][t][g] = gmul(g, xi);
    }
}

/* Darts of the same (i, target) class need distinct voltages so the graph is simple. */
static int valid_value(int i, int t, int x, int limit) {
    for (int t2 = 0; t2 < limit; t2++)
        if (t2 != t && tgt[i][t2] == tgt[i][t] && vol[i][t2] == x) return 0;
    return 1;
}

/* BFS up to depth D; returns number of vertices reached. */
static int bfs_count(int src) {
    int N = GN, BN = curB * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int i = v / N, g = v % N;
                for (int t = 0; t < d; t++) {
                    int u = BN + tgt[i][t] * N + fw[i][t][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - BN, j = w / N, x = w % N;
                for (int k = 0; k < d; k++) {
                    int i = incI[j][k], t = incT[j][k];
                    int u = i * N + bw[i][t][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached pairs from the 2B orbit representatives. */
static long cover_cost(void) {
    int N = GN, V = 2 * curB * N;
    long cost = 0;
    for (int i = 0; i < curB; i++) cost += (long)(V - bfs_count(i * N));
    for (int j = 0; j < curB; j++) cost += (long)(V - bfs_count((curB + j) * N));
    return cost;
}

/* Simulated annealing over the voltages; each restart draws a fresh random pattern.
 * Returns 1 with a cost-0 state in tgt/vol, 0 on timeout. */
static int search_group(double until) {
    int N = GN, B = curB;
    const int iters = 8000;
    while (now() < until) {
        set_random_pattern(B);
        for (int i = 0; i < B; i++)
            for (int t = 0; t < d; t++) {
                int x, tries = 0;
                do { x = rndint(N); tries++; } while (!valid_value(i, t, x, t) && tries < 100000);
                set_dart(i, t, x);
            }
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(B), t = rndint(d);
            int x, tries = 0;
            do { x = rndint(N); tries++; } while (!valid_value(i, t, x, d) && tries < 1000);
            if (tries >= 1000) continue;
            int old = vol[i][t];
            set_dart(i, t, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_dart(i, t, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ candidates and phases */

static Cand cand[MAXCAND];
static int nc = 0;

static void build_cands(int lo, int hi) {
    nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            if (nc < MAXCAND) {
                Cand cd = {q, p, k, c, (int)N};
                cand[nc++] = cd;
            }
        }
    }
    for (int i = 1; i < nc; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].N > t.N) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = t;
    }
}

/* Save the current state if it beats the best total. */
static void record(int B, Cand cd) {
    int total = 2 * B * cd.N;
    if (total <= bestTotal) return;
    bestTotal = total;
    bestB = B;
    bestN = cd.N;
    bestQ = cd.q;
    bestP = cd.p;
    bestK = cd.k;
    bestC = cd.c;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            bestTgt[i][t] = tgt[i][t];
            bestVol[i][t] = vol[i][t];
        }
}

/* Binary search over orders for the largest feasible N, then extend above it. */
static void search_phase(int B, int lo, int hi, double until) {
    build_cands(lo, hi);
    curB = B;
    int bestIdx = -1, bestNp = 0;
    int a = 0, b = nc - 1;
    while (a <= b && now() < until) {
        int mid = (a + b) / 2;
        double rem = until - now();
        double slice = rem * 0.2;
        if (slice < 1.5) slice = 1.5;
        if (slice > rem) slice = rem;
        setup_group(cand[mid].q, cand[mid].p, cand[mid].k, cand[mid].c);
        if (search_group(now() + slice)) {
            record(B, cand[mid]);
            if (cand[mid].N > bestNp) { bestNp = cand[mid].N; bestIdx = mid; }
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }
    if (bestIdx < 0) return;
    int fails = 0, idx = bestIdx + 1;
    while (idx < nc && now() < until && fails < 2) {
        if (cand[idx].N <= bestNp) { idx++; continue; }
        double rem = until - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        setup_group(cand[idx].q, cand[idx].p, cand[idx].k, cand[idx].c);
        if (search_group(now() + slice)) {
            record(B, cand[idx]);
            bestNp = cand[idx].N;
            bestIdx = idx;
            idx++;
            fails = 0;
        } else {
            idx++;
            fails++;
        }
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 13) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo[MAXB + 1], hi[MAXB + 1];
    for (int B = 1; B <= 4; B++) {
        lo[B] = atoi(argv[3 + 2 * B]);
        hi[B] = atoi(argv[4 + 2 * B]);
    }
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    for (int B = 1; B <= 4; B++) {
        if (lo[B] < 2 * d) lo[B] = 2 * d;
        if (hi[B] > MAXN - 1) hi[B] = MAXN - 1;
    }

    /* Phases: B = 3 first, then the B = 1 lift (the fallback that found the
     * previous best), then B = 2 and B = 4. Each takes a share of the time left. */
    static const int order[4] = {3, 1, 2, 4};
    static const double frac[4] = {0.40, 0.35, 0.45, 0.50};
    for (int k = 0; k < 4; k++) {
        int B = order[k];
        if (lo[B] > hi[B] || now() >= t_end) continue;
        double rem = t_end - now();
        search_phase(B, lo[B], hi[B], now() + frac[k] * rem);
    }
    if (bestTotal == 0) {
        for (int k = 0; k < 4 && now() < t_end; k++) {
            int B = order[k];
            if (lo[B] <= hi[B]) search_phase(B, lo[B], hi[B], t_end);
        }
    } else {
        /* Extend the best orbit count to larger orders with the remaining time. */
        int B = bestB;
        int nlo = bestN + 1;
        if (nlo < lo[B]) nlo = lo[B];
        if (nlo <= hi[B] && now() < t_end) search_phase(B, nlo, hi[B], t_end);
    }

    if (bestTotal == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Rebuild the best graph. */
    setup_group(bestQ, bestP, bestK, bestC);
    curB = bestB;
    for (int i = 0; i < bestB; i++)
        for (int t = 0; t < d; t++) tgt[i][t] = bestTgt[i][t];
    build_incidence(bestB);
    for (int i = 0; i < bestB; i++)
        for (int t = 0; t < d; t++) set_dart(i, t, bestVol[i][t]);

    int N = GN, BN = bestB * N, V = 2 * BN, E = BN * d;
    static int adj[2 * MAXB * MAXN][MAXD];
    for (int v = 0; v < BN; v++) {
        int i = v / N, g = v % N;
        for (int t = 0; t < d; t++) adj[v][t] = BN + tgt[i][t] * N + fw[i][t][g];
    }
    for (int w = BN; w < V; w++) {
        int j = (w - BN) / N, x = (w - BN) % N;
        for (int k = 0; k < d; k++) {
            int i = incI[j][k], t = incT[j][k];
            adj[w][k] = i * N + bw[i][t][x];
        }
    }

    /* Full check from every vertex when cheap; the symmetry argument is the fallback. */
    if (V <= 5000) {
        for (int s = 0; s < V; s++) {
            stamp_++;
            int head = 0, tail = 0;
            que[tail++] = s;
            vis[s] = stamp_;
            for (int lvl = 0; lvl < D && head < tail; lvl++) {
                int end = tail;
                while (head < end) {
                    int v = que[head++];
                    for (int k = 0; k < d; k++) {
                        int u = adj[v][k];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
                }
            }
            if (tail != V) {
                printf("0 0\n");
                return 0;
            }
        }
    }

    printf("%d %d\n", V, E);
    for (int v = 0; v < BN; v++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", v, adj[v][t]);
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

    # Multi-orbit affine lifts. Order N with B orbits per side gives 2BN vertices.
    # A B-orbit candidate must beat the current best: 2BN > best.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        if budget > 2.0:
            args = [d, D, seed, round(budget, 2)]
            for B in (1, 2, 3, 4):
                lo = max(2 * d, best[0] // (2 * B) + 1, mb // (8 * B))
                hi = min(mb // (2 * B), 4799)
                args += [lo, hi]
            try:
                text = lib.run_c(C_SOURCE, args, stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
