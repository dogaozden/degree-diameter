"""Two-orbit affine lifts for the bipartite degree-diameter problem.

New idea: the parent searches Haar graphs on one affine group G = F_q x| H, with
one left orbit and one right orbit. This version uses a 2+2 base: left orbits
A_0, A_1 and right orbits B_0, B_1, each a copy of G. Block (a, b) joins
L^a_g to R^b_{g s} for s in a connection set S_ab. Left translations act
transitively on every orbit, so the diameter check needs one BFS from each of
the four orbit representatives. The block sizes form a 2x2 matrix
[[x, d-x], [d-x, x]], so every vertex keeps degree d. The graph has 4|G| vertices,
which is more than the parent's 2|G| at the same order.

Phase A runs the parent's single-orbit (K = 1) search for a fallback graph, using
25% of the time. Phase B runs the two-orbit (K = 2) search over group orders
N > best_N / 2, so that 4N beats the fallback. Simulated annealing swaps one
connection element at a time, and each swap is checked by BFS from the 2K
representatives. Python keeps the projective-plane, Araujo-Lopez, W(q) and K_{d,d}
baselines, and every returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Two-orbit affine lift search.
 * Usage: prog d D seed time_limit
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
 * Vertices: left orbit a, element g -> a*N+g ; right orbit b, element h -> K*N+b*N+h.
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
#define MAXN 4700
#define MAXV (4 * MAXN)
#define MAXD 32
#define MAXCAND 8192

typedef struct { int q, p, k, c, N; } Cand;
typedef struct { int q, p, pk, c, N, K, X; int S[2][2][MAXD]; } State;

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
static int CUR_Q, CUR_P, CUR_PK, CUR_C;

/* Element (a, h_j) is coded as a*c + j, with h_j = g^(j*(q-1)/c).
 * Product: (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). Left multiplication acts
 * on the group by graph automorphisms of the lift. */
static void setup_group(int q, int p, int k, int c) {
    build_field(q, p, k);
    GQ = q;
    GC = c;
    GN = q * c;
    CUR_Q = q;
    CUR_P = p;
    CUR_PK = k;
    CUR_C = c;
    int g = -1;
    for (int g0 = 2; g0 < q && g < 0; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) g = g0;
    }
    if (q == 3) g = 2;
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

/* ------------------------------------------------------------ 2-orbit lift state */

static int K = 1, X_cur = 0;
static int Mx[2][2], roff[2][2], cof[2][2];
static int Sset[2][2][MAXD];
static int nb[MAXV][MAXD];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;
static State probe_st;

/* Block sizes: K=1 gives [[d]]; K=2 gives [[x, d-x], [d-x, x]] (row and column sums d). */
static void set_M(int kk, int X) {
    K = kk;
    X_cur = X;
    if (kk == 1) {
        Mx[0][0] = d;
        roff[0][0] = 0;
        cof[0][0] = 0;
        return;
    }
    Mx[0][0] = X;
    Mx[0][1] = d - X;
    Mx[1][0] = d - X;
    Mx[1][1] = X;
    for (int a = 0; a < 2; a++) {
        roff[a][0] = 0;
        roff[a][1] = Mx[a][0];
    }
    for (int b = 0; b < 2; b++) {
        cof[0][b] = 0;
        cof[1][b] = Mx[0][b];
    }
}

/* Block (a,b) element t = s: L^a_g ~ R^b_{g s} for all g. Overwrites every slot it owns. */
static void set_elem(int a, int b, int t, int x) {
    Sset[a][b][t] = x;
    int N = GN;
    int ro = roff[a][b] + t, co = cof[a][b] + t;
    for (int g = 0; g < N; g++) {
        int h = gmul(g, x);
        int L = a * N + g;
        int R = K * N + b * N + h;
        nb[L][ro] = R;
        nb[R][co] = L;
    }
}

static int in_prefix(int a, int b, int upto, int x) {
    for (int t = 0; t < upto; t++)
        if (Sset[a][b][t] == x) return 1;
    return 0;
}

static void init_random(void) {
    int N = GN;
    for (int a = 0; a < K; a++)
        for (int b = 0; b < K; b++)
            for (int t = 0; t < Mx[a][b]; t++) {
                int x;
                do { x = rndint(N); } while (in_prefix(a, b, t, x));
                set_elem(a, b, t, x);
            }
}

static int bfs_count(int src, int V) {
    (void)V;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            for (int s = 0; s < d; s++) {
                int u = nb[v][s];
                if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
            }
        }
    }
    return tail;
}

/* Vertex-transitivity on each orbit: one BFS per orbit representative decides the diameter. */
static long cover_cost(void) {
    int V = 2 * K * GN;
    long cost = 0;
    for (int a = 0; a < K; a++)
        cost += (long)(V - bfs_count(a * GN, V));
    for (int b = 0; b < K; b++)
        cost += (long)(V - bfs_count(K * GN + b * GN, V));
    return cost;
}

static long tot(int kk, long N) { return 2L * kk * N; }

/* Simulated annealing over the connection sets of the current group.
 * Returns 1 and saves probe_st when diameter <= D is reached, 0 on timeout. */
static int search_group(double until) {
    const int iters = 6000;
    int N = GN;
    while (now() < until) {
        int X = (K == 2) ? 1 + rndint(d - 1) : 0;
        set_M(K, X);
        init_random();
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int a = rndint(K), b = rndint(K);
            int t = rndint(Mx[a][b]);
            int x;
            do { x = rndint(N); } while (in_prefix(a, b, Mx[a][b], x));
            int old = Sset[a][b][t];
            set_elem(a, b, t, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T))
                cost = c2;
            else
                set_elem(a, b, t, old);
        }
        if (cost == 0) {
            probe_st.q = CUR_Q;
            probe_st.p = CUR_P;
            probe_st.pk = CUR_PK;
            probe_st.c = CUR_C;
            probe_st.N = N;
            probe_st.K = K;
            probe_st.X = X_cur;
            memcpy(probe_st.S, Sset, sizeof(Sset));
            return 1;
        }
    }
    return 0;
}

static int make_cands(Cand *cand, long lo, long hi) {
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
    return nc;
}

/* Binary search over candidate orders (feasibility assumed roughly monotone), then
 * spend leftover time on the orders above. Each probe gets an equal share of the
 * remaining time over the probes still needed. */
static void run_phase(int kk, Cand *cand, int nc, double tend, State *best) {
    K = kk;
    int a = 0, b = nc - 1;
    while (a <= b && now() < tend) {
        int mid = (a + b) / 2;
        int span = b - a + 1, probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = tend - now();
        double slice = rem / (probes + 1);
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_group(cand[mid].q, cand[mid].p, cand[mid].k, cand[mid].c);
        K = kk;
        if (search_group(now() + slice)) {
            if (tot(kk, cand[mid].N) > tot(best->K, best->N)) *best = probe_st;
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }
    int idx = a, fails = 0;
    while (idx < nc && now() < tend && fails < 2) {
        if (tot(kk, cand[idx].N) <= tot(best->K, best->N)) { idx++; continue; }
        double rem = tend - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        setup_group(cand[idx].q, cand[idx].p, cand[idx].k, cand[idx].c);
        K = kk;
        if (search_group(now() + slice)) {
            *best = probe_st;
            fails = 0;
        } else {
            fails++;
        }
        idx++;
    }
}

static Cand c1[MAXCAND], c2[MAXCAND];

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    if (d < 3 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double s = 0.0, pw = 1.0;
    for (int i = 0; i < D; i++) { s += pw; pw *= (d - 1); }
    long mb = (long)(2.0 * s);
    double T = t_end - t0;
    if (T < 1.0) {
        printf("0 0\n");
        return 0;
    }

    State best;
    memset(&best, 0, sizeof(best));

    /* Phase A: single-orbit Haar lifts (K = 1), fallback graph. */
    long lo1 = 2L * d;
    if (mb / 8 > lo1) lo1 = mb / 8;
    long hi1 = mb / 2;
    if (hi1 > MAXN) hi1 = MAXN;
    if (lo1 <= hi1) {
        int nc1 = make_cands(c1, lo1, hi1);
        run_phase(1, c1, nc1, t0 + 0.25 * T, &best);
    }

    /* Phase B: two-orbit lifts (K = 2) with total 4N > 2*best.N, so N > best.N/2. */
    long lo2 = 2L * d;
    long t2 = (long)best.N / 2 + 1;
    if (t2 > lo2) lo2 = t2;
    if (best.N == 0 && mb / 16 > lo2) lo2 = mb / 16;
    long hi2 = mb / 4;
    if (hi2 > MAXN) hi2 = MAXN;
    if (lo2 <= hi2) {
        int nc2 = make_cands(c2, lo2, hi2);
        run_phase(2, c2, nc2, t_end, &best);
    }

    if (best.N == 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(best.q, best.p, best.pk, best.c);
    set_M(best.K, best.X);
    for (int a = 0; a < best.K; a++)
        for (int b = 0; b < best.K; b++)
            for (int t = 0; t < Mx[a][b]; t++)
                set_elem(a, b, t, best.S[a][b][t]);
    int KN = K * GN;
    printf("%d %d\n", 2 * KN, KN * d);
    for (int L = 0; L < KN; L++)
        for (int s2 = 0; s2 < d; s2++)
            printf("%d %d\n", L, nb[L][s2]);
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

    # Two-orbit affine lifts (the C search also runs the single-orbit baseline first).
    if d >= 3 and D >= 3:
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        if budget > 4.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
