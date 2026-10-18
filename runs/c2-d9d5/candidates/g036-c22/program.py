"""Multi-orbit affine voltage lifts for the bipartite degree-diameter problem.

The parent searched only Haar graphs (one left orbit and one right orbit) over affine
groups F_q x| H. This version adds a substantially different family: a 2+2 base
voltage lift. Each side has two orbits of size N, so the graph has 4N vertices. For
a split a in 1..d-1, the dart counts are [[a, d-a], [d-a, a]], which makes the graph
d-regular. Each dart carries a group element, and edges join L_{i,x} to R_{j,x*g}.

Left multiplication by a group element is an automorphism that fixes each orbit, so
diameter <= D reduces to four BFS runs, one from each orbit's identity vertex.

The C engine runs in two modes:
  K = 1: the parent's Haar family, kept as a safety net (2N vertices).
  K = 2: the new 4-orbit family (4N vertices).

Python runs K = 1 first with about 45% of the budget, then K = 2 with the rest. Every
candidate is checked with lib.is_valid, and the largest valid graph is returned. The
constructions from the parent (projective planes, Araujo-Pardo-Lopez, W(q)) and the
K_{d,d} fallback are unchanged.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit affine voltage lift search (bipartite, degree d, diameter <= D).
 * Usage: prog d D seed time_limit lo hi K     (stdin ignored)
 * K = 1: Haar graph over F_q x| H                         (2N vertices)
 * K = 2: 2 left orbits and 2 right orbits, each of size N  (4N vertices)
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
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
#define MAXN 2400
#define MAXD 32
#define MAXV (4 * MAXN)
#define MAXCAND 8192

typedef struct { int q, p, k, c, N; } Cand;

static int d, D, K;
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

static int GC, GN, N, V;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Element (a, h_j) is coded a*c + j, with h_j = g^(j*(q-1)/c).
 * Product: (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). Identity is 0. */
static void setup_cand(const Cand *cd) {
    int q = cd->q, c = cd->c;
    build_field(q, cd->p, cd->k);
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
    GC = c;
    GN = q * c;
    N = GN;
    V = 2 * K * N;
}

static inline int gmul(int x, int y) {
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

/* ------------------------------------------------------------ voltage lift state */

/* Left orbit i has vertices i*N + x. Right orbit j has vertices (K + j)*N + y.
 * Block (i, j) holds cnt[i][j] darts g; each gives edges L_{i,x} -- R_{j, x*g}.
 * Row and column sums of cnt are d, so the graph is d-regular and bipartite. */
static int cnt[2][2];
static int E[2][2][MAXD];
static int bcnt[2][2];
static int bE[2][2][MAXD];
static int adjv[MAXV][MAXD];
static int deg[MAXV];
static int stampv[MAXV], stamp_now = 0, que[MAXV];
static int bestCi = -1, bestN = 0;
static Cand cand[MAXCAND];
static int nc = 0;

static int dup_upto(int i, int j, int t, int x) {
    for (int s = 0; s < t; s++)
        if (E[i][j][s] == x) return 1;
    return 0;
}

static int dup_except(int i, int j, int t, int x) {
    for (int s = 0; s < cnt[i][j]; s++)
        if (s != t && E[i][j][s] == x) return 1;
    return 0;
}

static void random_state(void) {
    memset(cnt, 0, sizeof cnt);
    if (K == 1) {
        cnt[0][0] = d;
    } else {
        int a = 1 + rndint(d - 1);
        cnt[0][0] = a;
        cnt[0][1] = d - a;
        cnt[1][0] = d - a;
        cnt[1][1] = a;
    }
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            for (int t = 0; t < cnt[i][j]; t++) {
                int x;
                do { x = rndint(N); } while (dup_upto(i, j, t, x));
                E[i][j][t] = x;
            }
}

static void build_adj(void) {
    for (int v = 0; v < V; v++) deg[v] = 0;
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            for (int t = 0; t < cnt[i][j]; t++) {
                int g = E[i][j][t];
                for (int x = 0; x < N; x++) {
                    int a = i * N + x;
                    int b = (K + j) * N + gmul(x, g);
                    adjv[a][deg[a]++] = b;
                    adjv[b][deg[b]++] = a;
                }
            }
}

/* Number of vertices within distance D of src. */
static int reach_count(int src) {
    stamp_now++;
    int head = 0, tail = 0;
    que[tail++] = src;
    stampv[src] = stamp_now;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            for (int t = 0; t < d; t++) {
                int u = adjv[v][t];
                if (stampv[u] != stamp_now) {
                    stampv[u] = stamp_now;
                    que[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* Orbit-transitivity: one BFS per orbit identity decides diameter <= D. */
static long cover_cost(void) {
    long c = 0;
    for (int o = 0; o < 2 * K; o++)
        c += (long)(V - reach_count(o * N));
    return c;
}

static void save_state(void) {
    memcpy(bcnt, cnt, sizeof cnt);
    memcpy(bE, E, sizeof E);
}

/* Simulated annealing over the dart elements for the current group.
 * Returns 1 when cost 0 is reached (state left in cnt/E), 0 on timeout. */
static int search_group(double until) {
    const int iters = 4000;
    while (now() < until) {
        random_state();
        build_adj();
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(K), j = rndint(K);
            if (cnt[i][j] == 0) continue;
            int t = rndint(cnt[i][j]);
            int old = E[i][j][t];
            int x;
            do { x = rndint(N); } while (dup_except(i, j, t, x));
            E[i][j][t] = x;
            build_adj();
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                E[i][j][t] = old;
                build_adj();
            }
            if (cost == 0) return 1;
        }
    }
    return 0;
}

static void print_best(void) {
    setup_cand(&cand[bestCi]);
    memcpy(cnt, bcnt, sizeof cnt);
    memcpy(E, bE, sizeof E);
    long m = 0;
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            m += (long)cnt[i][j] * N;
    printf("%d %ld\n", 2 * K * N, m);
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            for (int t = 0; t < cnt[i][j]; t++) {
                int g = E[i][j][t];
                for (int x = 0; x < N; x++)
                    printf("%d %d\n", i * N + x, (K + j) * N + gmul(x, g));
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
    K = atoi(argv[7]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3 || (K != 1 && K != 2)) {
        printf("0 0\n");
        return 0;
    }
    if (hi > MAXN) hi = MAXN;
    if (lo < d + 1) lo = d + 1;

    /* Candidate affine groups F_q x| H with lo <= q*c <= hi (c = 1 gives translations). */
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 1; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long Nl = (long)q * c;
            if (Nl < lo || Nl > hi) continue;
            if (nc < MAXCAND) {
                Cand cd = {q, p, k, c, (int)Nl};
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

    /* Ascending sweep. Each candidate gets an equal share of the time left in this
     * pass (at least 0.3 s). Later passes retry the candidates that failed. */
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            if (cand[ci].N <= bestN) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            int left = 0;
            for (int cj = ci; cj < nc; cj++)
                if (cand[cj].N > bestN) left++;
            tried = 1;
            double slice = rem / (left > 0 ? left : 1);
            if (slice < 0.3) slice = 0.3;
            if (slice > rem) slice = rem;
            setup_cand(&cand[ci]);
            if (search_group(now() + slice)) {
                bestN = cand[ci].N;
                bestCi = ci;
                save_state();
            }
        }
        if (!tried || t_end - now() < 0.3) break;
    }

    if (bestCi < 0) {
        printf("0 0\n");
        return 0;
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


def _run_engine(d, D, seed, budget, lo, hi, K):
    """Run the C lift search with K orbits per side. Returns (n, edges) or None."""
    if budget < 2.0 or lo > hi:
        return None
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi, K],
                         stdin_graph=None, timeout=budget + 8.0)
        return lib.parse_graph_text(text)
    except Exception:
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

    def left():
        return 0.82 * time_limit - (time.monotonic() - t0) - 3.0

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
        # Engine A (K = 1): the parent's Haar family, kept as the safety net.
        lo_a = max(best[0] // 2 + 1, mb // 8)
        hi_a = mb // 2
        budget_a = 0.45 * left()
        consider(_run_engine(d, D, seed, budget_a, lo_a, hi_a, 1))
        # Engine B (K = 2): the new 2+2 orbit lift, with 4N vertices.
        lo_b = max(mb // 16, best[0] // 4 + 1)
        hi_b = mb // 4
        consider(_run_engine(d, D, seed + 1, left(), lo_b, hi_b, 2))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
