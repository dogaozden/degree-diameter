"""Multi-fibre voltage lifts over mixed groups for the bipartite degree-diameter problem.

New idea in this version: the parent searches only Haar graphs, which have a single
left and a single right fibre. This version lifts a base bipartite d-regular multigraph
on K + K vertices (K = 1..4). Each base vertex u on the left is joined to right base
vertices through d permutation layers, and each dart carries a voltage in a group G of
order N. The lift has 2KN vertices and is d-regular, up to voltage collisions that
the output step removes.

G ranges over the affine groups F_q x| H (H the subgroup of F_q^* of order c) and the
cyclic groups Z_N. Left translations act transitively on each fibre, so the diameter
check needs only 2K BFS runs, one from each base vertex.

Search: simulated annealing over the voltages and, with probability 0.3 per move when
K >= 2, over the base permutations (swapping two targets within one layer). Restarts
begin from random bases and voltages. Candidate orders are tried in ascending order,
with random tie-breaking, so the search ratchets upward from the current best. Each
candidate gets 15% of the remaining time (at least 1 s), and passes repeat until time
runs out.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-fibre voltage lift search over affine and cyclic groups.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 1600
#define MAXG 2048
#define MAXK 4
#define MAXD 32
#define MAXV (2 * MAXK * MAXG)
#define MAXCAND 20000

typedef struct { int type, q, p, k, c, N, K, n; uint32_t tie; } Cand;

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

/* ------------------------------------------------------------ group tables */

static int GN;
static unsigned short GMT[MAXG * MAXG]; /* product table, identity = 0 */
static int GINV[MAXG];

static void finish_group(void) {
    int N = GN;
    for (int x = 0; x < N; x++) {
        GINV[x] = 0;
        for (int y = 0; y < N; y++)
            if (GMT[x * N + y] == 0) { GINV[x] = y; break; }
    }
}

/* G = F_q x| H, element (a, h_j) coded a*c + j, with h_j = g^(j*(q-1)/c). */
static void build_affine(int q, int p, int k, int c) {
    build_field(q, p, k);
    int g = -1;
    for (int g0 = 2; g0 < q && g < 0; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) g = g0;
    }
    if (g < 0) return;
    static int pwg[MAXQ], Hel[MAXQ], hidx[MAXQ];
    pwg[0] = 1;
    for (int i = 1; i < q - 1; i++) pwg[i] = MULT[pwg[i - 1]][g];
    int step = (q - 1) / c;
    for (int j = 0; j < q; j++) hidx[j] = -1;
    for (int t = 0; t < c; t++) {
        Hel[t] = pwg[(t * step) % (q - 1)];
        hidx[Hel[t]] = t;
    }
    int N = q * c;
    GN = N;
    for (int x = 0; x < N; x++) {
        int a = x / c, j = x % c;
        for (int y = 0; y < N; y++) {
            int b = y / c, t = y % c;
            int na = ADDT[a][MULT[Hel[j]][b]];
            int nj = hidx[MULT[Hel[j]][Hel[t]]];
            GMT[x * N + y] = (unsigned short)(na * c + nj);
        }
    }
    finish_group();
}

static void build_cyclic(int N) {
    GN = N;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            GMT[x * N + y] = (unsigned short)((x + y) % N);
    finish_group();
}

/* ------------------------------------------------------------ lift state */

static int K;
static int PERM[MAXD][MAXK], PINV[MAXD][MAXK], AV[MAXD][MAXK];
static int bestPERM[MAXD][MAXK], bestAV[MAXD][MAXK];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

/* Vertices: left (u, x) = u*N + x; right (v, y) = (K + v)*N + y.
 * Dart (u, j) joins left (u, x) to right (PERM[j][u], x * AV[j][u]). */
static int bfs_reach(int src) {
    int N = GN;
    int LEFT = K * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < LEFT) {
                int u = v / N, x = v % N;
                for (int j = 0; j < d; j++) {
                    int w = (K + PERM[j][u]) * N + GMT[x * N + AV[j][u]];
                    if (vis[w] != stamp_) { vis[w] = stamp_; que[tail++] = w; }
                }
            } else {
                int r = v / N - K, y = v % N;
                for (int j = 0; j < d; j++) {
                    int u = PINV[j][r];
                    int w = u * N + GMT[y * N + GINV[AV[j][u]]];
                    if (vis[w] != stamp_) { vis[w] = stamp_; que[tail++] = w; }
                }
            }
        }
    }
    return tail;
}

/* Sum over the 2K base fibres of unreached vertices (0 iff diameter <= D). */
static long lift_cost(void) {
    long c = 0;
    int V = 2 * K * GN;
    for (int s = 0; s < 2 * K; s++)
        c += (long)(V - bfs_reach(s * GN));
    return c;
}

static void fix_pinv(void) {
    for (int j = 0; j < d; j++)
        for (int u = 0; u < K; u++)
            PINV[j][PERM[j][u]] = u;
}

static void swap_perm(int j, int u1, int u2) {
    int t = PERM[j][u1];
    PERM[j][u1] = PERM[j][u2];
    PERM[j][u2] = t;
    PINV[j][PERM[j][u1]] = u1;
    PINV[j][PERM[j][u2]] = u2;
}

static void init_state(void) {
    int N = GN;
    for (int j = 0; j < d; j++) {
        for (int u = 0; u < K; u++) PERM[j][u] = u;
        for (int u = K - 1; u > 0; u--) {
            int r = rndint(u + 1);
            int t = PERM[j][u];
            PERM[j][u] = PERM[j][r];
            PERM[j][r] = t;
        }
        for (int u = 0; u < K; u++) {
            PINV[j][PERM[j][u]] = u;
            AV[j][u] = rndint(N);
        }
    }
}

/* Simulated annealing over voltages and base permutations.
 * Returns 1 when cost 0 is reached, 0 on timeout. */
static int search_lift(double until) {
    const int iters = 1500;
    while (now() < until) {
        init_state();
        long cost = lift_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.1 * c0 + 1.0, Te = 0.2;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            if (K >= 2 && rnd01() < 0.3) {
                int j = rndint(d), u1 = rndint(K), u2 = rndint(K);
                if (u1 == u2) continue;
                swap_perm(j, u1, u2);
                long c2 = lift_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T))
                    cost = c2;
                else
                    swap_perm(j, u1, u2);
            } else {
                int j = rndint(d), u = rndint(K);
                int old = AV[j][u], nw = rndint(GN);
                if (nw == old) continue;
                AV[j][u] = nw;
                long c2 = lift_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T))
                    cost = c2;
                else
                    AV[j][u] = old;
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void print_result(void) {
    int N = GN;
    int n = 2 * K * N;
    long cap = (long)K * N * d + 1;
    int *eu = malloc(sizeof(int) * (size_t)cap);
    int *ev = malloc(sizeof(int) * (size_t)cap);
    long m = 0;
    for (int u = 0; u < K; u++)
        for (int x = 0; x < N; x++)
            for (int j = 0; j < d; j++) {
                int r = PERM[j][u];
                int dup = 0;
                for (int jj = 0; jj < j; jj++)
                    if (PERM[jj][u] == r && AV[jj][u] == AV[j][u]) { dup = 1; break; }
                if (dup) continue;
                int y = GMT[x * N + AV[j][u]];
                eu[m] = u * N + x;
                ev[m] = (K + r) * N + y;
                m++;
            }
    printf("%d %ld\n", n, m);
    for (long i = 0; i < m; i++) printf("%d %d\n", eu[i], ev[i]);
    free(eu);
    free(ev);
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    if (x->n != y->n) return x->n - y->n;
    if (x->tie != y->tie) return (x->tie < y->tie) ? -1 : 1;
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
    t_end = t0 + limit - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (lo < 2) lo = 2;
    if (hi > 3500) hi = 3500;

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int KK = 1; KK <= MAXK; KK++) {
        for (int q = 3; q < MAXQ; q++) {
            int p, k;
            if (!factor_pp(q, &p, &k)) continue;
            for (int c = 1; c <= q - 1; c++) {
                if ((q - 1) % c) continue;
                if (c == 1 && k == 1) continue;   /* same as cyclic Z_q */
                int N = q * c;
                if (N > MAXG) continue;
                int n = 2 * KK * N;
                if (n < lo || n > hi) continue;
                if (nc < MAXCAND) {
                    Cand cd = {0, q, p, k, c, N, KK, n, (uint32_t)rnd()};
                    cand[nc++] = cd;
                }
            }
        }
        for (int N = 2; N <= MAXG; N++) {
            int n = 2 * KK * N;
            if (n < lo || n > hi) continue;
            if (nc < MAXCAND) {
                Cand cd = {1, 0, 0, 0, 0, N, KK, n, (uint32_t)rnd()};
                cand[nc++] = cd;
            }
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    int bestn = lo - 1, best_ci = -1, bestK = 0;
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            if (cand[ci].n <= bestn) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = 0.15 * rem;
            if (slice < 1.0) slice = 1.0;
            if (slice > rem) slice = rem;
            Cand *cd = &cand[ci];
            if (cd->type == 0) build_affine(cd->q, cd->p, cd->k, cd->c);
            else build_cyclic(cd->N);
            K = cd->K;
            if (search_lift(now() + slice)) {
                bestn = cd->n;
                best_ci = ci;
                bestK = K;
                memcpy(bestPERM, PERM, sizeof PERM);
                memcpy(bestAV, AV, sizeof AV);
            }
        }
        if (!tried || t_end - now() < 0.3) break;
    }

    if (best_ci < 0) {
        printf("0 0\n");
        return 0;
    }
    Cand *cd = &cand[best_ci];
    if (cd->type == 0) build_affine(cd->q, cd->p, cd->k, cd->c);
    else build_cyclic(cd->N);
    K = bestK;
    memcpy(PERM, bestPERM, sizeof PERM);
    memcpy(AV, bestAV, sizeof AV);
    fix_pinv();
    if (lift_cost() != 0) {
        printf("0 0\n");
        return 0;
    }
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

    # Search: multi-fibre voltage lifts over mixed affine / cyclic groups.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.9 * time_limit - (time.monotonic() - t0) - 3.0
        lo = max(best[0] + 1, mb // 6)
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
