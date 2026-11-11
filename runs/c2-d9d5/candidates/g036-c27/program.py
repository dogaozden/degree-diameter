"""Bi-Cayley lifts over affine groups for the bipartite degree-diameter problem.

Change from the parent: the parent searched only Haar graphs (base = two vertices,
one per side, so |V| = 2|G|). This version searches a different family. The base
graph has B vertices per side (B = 1 or 2), and the lift over G = F_q x| H is a
bi-regular voltage graph:

  left (i, g) ~ right (j, g*s)   for every s in S_ij,

where the block sizes |S_ij| form a matrix with all row and column sums equal to d.
For B = 2 the matrix is [[a, d-a], [d-a, a]], with a chosen at random on each restart.
The graph has 2*B*|G| vertices and is d-regular. Left multiplication by G is an
automorphism, so the diameter test needs one BFS from each of the 2B representatives
(i, e) and (j, e). The C engine searches the sets S_ij by simulated annealing.

Stage A runs B = 2 (non-Haar, the new family). Stage B runs B = 1 (the parent's Haar
family) and only accepts orders that beat the best so far. The Python K_{d,d}, projective
plane, Araujo-Lopez and W(q) baselines are kept. Every returned graph passes lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley lift search over affine groups F_q x| H.
 * Usage: prog d D seed time_limit lo hi B
 *   B = base size per side (1 or 2); lo/hi bound the group order N = |G|.
 * Output: "n m" then m lines "u v" for the best valid graph, or "0 0".
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
#define MAXN 8192
#define MAXD 32
#define MAXCAND 8192
#define MAXV (4 * MAXN)

typedef struct { int q, p, k, c, N; } Cand;

static int d, D, B;
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

/* Element (a, h_j) is coded as a*c + j with h_j = g^(j*(q-1)/c).
 * Product: (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). */
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

/* ------------------------------------------------------------ bi-Cayley state */

/* Block (i, j) holds cnt[i][j] group elements S_ij[k]. Left (i,g) ~ right (j, g*s).
 * fwd[i][j][k][g] = g*s, bwd[i][j][k][h] = h*s^-1. */
static int E[2][2][MAXD];
static int fwd[2][2][MAXD][MAXN];
static int bwd[2][2][MAXD][MAXN];
static int cnt[2][2];
static int curA = 0;
static int bestE[2][2][MAXD];
static int bestA = 0;

static void set_counts(int a) {
    memset(cnt, 0, sizeof cnt);
    curA = a;
    if (B == 1) {
        cnt[0][0] = d;
    } else {
        cnt[0][0] = a;
        cnt[0][1] = d - a;
        cnt[1][0] = d - a;
        cnt[1][1] = a;
    }
}

static void set_slot(int i, int j, int k, int x) {
    E[i][j][k] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fwd[i][j][k][g] = gmul(g, x);
        bwd[i][j][k][g] = gmul(g, xi);
    }
}

static int in_block(int x, int i, int j, int upto) {
    for (int t = 0; t < upto; t++)
        if (E[i][j][t] == x) return 1;
    return 0;
}

static void random_state(void) {
    for (int i = 0; i < B; i++)
        for (int j = 0; j < B; j++)
            for (int k = 0; k < cnt[i][j]; k++) {
                int x;
                do { x = rndint(GN); } while (in_block(x, i, j, k));
                set_slot(i, j, k, x);
            }
}

/* ------------------------------------------------------------ cost via BFS */

static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int N = GN;
    int BN = B * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int i = v / N, g = v - i * N;
                for (int j = 0; j < B; j++) {
                    int c = cnt[i][j];
                    for (int k = 0; k < c; k++) {
                        int u = BN + j * N + fwd[i][j][k][g];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
                }
            } else {
                int w = v - BN;
                int j = w / N, h = w - j * N;
                for (int i = 0; i < B; i++) {
                    int c = cnt[i][j];
                    for (int k = 0; k < c; k++) {
                        int u = i * N + bwd[i][j][k][h];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
                }
            }
        }
    }
    return tail;
}

/* Left and right actions are transitive on each side's orbit, so the diameter
 * test needs one BFS from each representative (left i, e) and (right j, e). */
static long cover_cost(void) {
    int N = GN, BN = B * N, V = 2 * BN;
    long c = 0;
    for (int i = 0; i < B; i++) c += (long)(V - bfs_count(i * N));
    for (int j = 0; j < B; j++) c += (long)(V - bfs_count(BN + j * N));
    return c;
}

/* Simulated annealing over the block elements in the current group.
 * Returns 1 when cost 0 is reached, 0 on timeout. */
static int search_group(double until) {
    int N = GN;
    const int iters = 8000;
    while (now() < until) {
        int a = (B == 2) ? rndint(d + 1) : d;
        set_counts(a);
        random_state();
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i, j;
            do { i = rndint(B); j = rndint(B); } while (cnt[i][j] == 0);
            int k = rndint(cnt[i][j]);
            int old = E[i][j][k];
            int x;
            do { x = rndint(N); } while (in_block(x, i, j, cnt[i][j]));
            set_slot(i, j, k, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_slot(i, j, k, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void save_best(void) {
    memcpy(bestE, E, sizeof E);
    bestA = curA;
}

static void print_result(void) {
    int N = GN, BN = B * N;
    printf("%d %d\n", 2 * BN, BN * d);
    for (int i = 0; i < B; i++)
        for (int g = 0; g < N; g++) {
            int v = i * N + g;
            for (int j = 0; j < B; j++)
                for (int k = 0; k < cnt[i][j]; k++)
                    printf("%d %d\n", v, BN + j * N + fwd[i][j][k][g]);
        }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    B = atoi(argv[7]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3 || (B != 1 && B != 2)) {
        printf("0 0\n");
        return 0;
    }
    if (hi > MAXN) hi = MAXN;
    if (lo < 2 * d) lo = 2 * d;

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 1; c <= q - 1; c++) {
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

    int best_idx = -1, bestN = 0;

    /* Phase 1: binary search for the largest feasible order. Each probe gets an
     * equal share of the remaining time over the probes still needed. */
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
        setup_group(cand[mid].q, cand[mid].p, cand[mid].k, cand[mid].c);
        if (search_group(now() + slice)) {
            if (cand[mid].N > bestN) {
                bestN = cand[mid].N;
                best_idx = mid;
                save_best();
            }
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }

    /* Phase 2: spend leftover time on the next few orders above the best. */
    int fails = 0;
    int idx = best_idx < 0 ? 0 : best_idx + 1;
    while (idx < nc && now() < t_end && fails < 2) {
        if (cand[idx].N <= bestN) { idx++; continue; }
        double rem = t_end - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        setup_group(cand[idx].q, cand[idx].p, cand[idx].k, cand[idx].c);
        if (search_group(now() + slice)) {
            bestN = cand[idx].N;
            best_idx = idx;
            save_best();
            idx++;
            fails = 0;
        } else {
            idx++;
            fails++;
        }
    }

    if (best_idx < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(cand[best_idx].q, cand[best_idx].p, cand[best_idx].k, cand[best_idx].c);
    set_counts(bestA);
    for (int i = 0; i < B; i++)
        for (int j = 0; j < B; j++)
            for (int k = 0; k < cnt[i][j]; k++)
                set_slot(i, j, k, bestE[i][j][k]);
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


def _lift_search(d, D, seed, budget, lo, hi, base):
    """Run the C bi-Cayley search with base size `base` (1 or 2) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi, base],
                     stdin_graph=None, timeout=budget + 8.0)
    return lib.parse_graph_text(text)


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

    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)

        def remaining():
            # Reserve time for compiling, parsing and validating the returned graphs.
            return 0.8 * time_limit - (time.monotonic() - t0) - 6.0

        # Stage A: non-Haar bi-Cayley lifts with two base vertices per side.
        # |V| = 4N, so N ranges over [best/4, mb/4].
        budget = 0.6 * remaining()
        if budget > 3.0:
            lo = max(best[0] // 4 + 1, mb // 16, 2 * d)
            hi = mb // 4
            if lo <= hi:
                try:
                    consider(_lift_search(d, D, seed, budget, lo, hi, 2))
                except Exception:
                    pass   # keep the valid graph found so far

        # Stage B: Haar lifts (base size 1) with the remaining time. Only orders
        # that beat the current best are accepted.
        budget = remaining()
        if budget > 3.0:
            lo = max(best[0] // 2 + 1, mb // 8, 2 * d)
            hi = mb // 2
            if lo <= hi:
                try:
                    consider(_lift_search(d, D, seed + 1, budget, lo, hi, 1))
                except Exception:
                    pass

    return best
