"""Multi-orbit Haar lifts with random block multiplicities for the bipartite degree-diameter problem.

New idea: the parent searches only Haar graphs (one base vertex per side), so every
candidate is vertex-transitive on each side. This version lifts a bipartite base graph
with K left and K right base vertices over a group G of order N (cyclic, or an affine
group F_q x| H). The base multiplicity matrix M (K x K, row and column sums d) is the sum of
d random permutation matrices. Each block (i, j) with M_ij darts gets distinct voltages.
The lift has 2KN vertices and is d-regular and simple.

Left translations are automorphisms, so the diameter check needs only one BFS from each
base vertex (2K BFS runs). Simulated annealing over the voltages, with random restarts
that also redraw M, looks for cost 0. Candidate orders run from just above the best so far
up to a cap, in ascending order, with repeated passes, as in the parent.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit lift search over cyclic and affine groups.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo, hi bound the total vertex count 2*K*N.
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
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
#define MAXN 2048
#define MAXV 8192
#define MAXD 16
#define MAXK 4
#define MAXND (MAXK * MAXD)
#define MAXCAND 60000

typedef struct { int typ, q, p, k, c, N, K, V; } Cand;

static int d, D, K, N, V, nd;
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

static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];
static int MT[MAXN * MAXN];   /* MT[x*N+y] = x*y; identity is 0 in both group types */

/* Cyclic Z_N (typ 0), or F_q x| H with H of order c (typ 1), element (a, h_j) coded a*c+j. */
static void build_group(const Cand *cd) {
    N = cd->N;
    if (cd->typ == 0) {
        for (int x = 0; x < N; x++)
            for (int y = 0; y < N; y++)
                MT[x * N + y] = (x + y) % N;
        return;
    }
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
    for (int x = 0; x < N; x++) {
        int a = x / c, j = x % c;
        for (int y = 0; y < N; y++) {
            int b = y / c, t = y % c;
            int na = ADDT[a][MULT[Hel[j]][b]];
            MT[x * N + y] = na * c + HM[j * c + t];
        }
    }
}

/* ------------------------------------------------------------ multi-orbit lift state */

/* Node ids: left base vertex i, group element g -> i*N+g (i < K);
 * right base vertex j, element h -> (K+j)*N+h.
 * Dart t joins left block dart_i[t] to right block dart_j[t] with voltage dart_v[t]:
 * L(i,g) ~ R(j, g*v). Left translation by x is an automorphism. */
static int Mat[MAXK][MAXK];
static int dart_i[MAXND], dart_j[MAXND], dart_v[MAXND], lslot[MAXND], rslot[MAXND];
static int adj[MAXV * MAXD];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;
static int bestAdj[MAXV * MAXD];
static int bestK = 0, bestN = 0, bestV = 0;

/* Multiplicity matrix: sum of d random permutation matrices, so every row and column sums to d. */
static void random_matrix(void) {
    memset(Mat, 0, sizeof Mat);
    for (int t = 0; t < d; t++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        for (int i = 0; i < K; i++) Mat[i][perm[i]]++;
    }
}

static void build_darts(void) {
    int cntL[MAXK] = {0}, cntR[MAXK] = {0};
    nd = 0;
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            for (int c = 0; c < Mat[i][j]; c++) {
                dart_i[nd] = i;
                dart_j[nd] = j;
                lslot[nd] = cntL[i]++;
                rslot[nd] = cntR[j]++;
                nd++;
            }
}

static void set_volt(int t, int v) {
    int i = dart_i[t], j = dart_j[t];
    dart_v[t] = v;
    int L = i * N, R = (K + j) * N;
    for (int g = 0; g < N; g++) {
        int h = MT[g * N + v];
        int x = L + g, y = R + h;
        adj[x * d + lslot[t]] = y;
        adj[y * d + rslot[t]] = x;
    }
}

/* True if voltage v is already used by another dart of the same block among darts 0..limit-1. */
static int conflict(int t, int v, int limit) {
    for (int s = 0; s < limit; s++)
        if (s != t && dart_i[s] == dart_i[t] && dart_j[s] == dart_j[t] && dart_v[s] == v)
            return 1;
    return 0;
}

/* Number of vertices NOT within distance D of src. */
static int bfs_missing(int src) {
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            const int *a = &adj[v * d];
            for (int s = 0; s < d; s++) {
                int u = a[s];
                if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
            }
        }
    }
    return V - tail;
}

/* One BFS per base vertex (2K runs) decides the diameter. */
static long total_cost(void) {
    long c = 0;
    for (int b = 0; b < 2 * K; b++) c += bfs_missing(b * N);
    return c;
}

/* Annealing over voltages with random restarts that redraw the multiplicity matrix.
 * Returns 1 when cost 0 is reached (adj then holds the valid graph), 0 on timeout. */
static int search_cand(double until) {
    const int iters = 6000;
    while (now() < until) {
        random_matrix();
        build_darts();
        for (int t = 0; t < nd; t++) {
            int v;
            do { v = rndint(N); } while (conflict(t, v, t));
            set_volt(t, v);
        }
        long cost = total_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int t = rndint(nd);
            int old = dart_v[t];
            int v;
            do { v = rndint(N); } while (v == old || conflict(t, v, nd));
            set_volt(t, v);
            long c2 = total_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else set_volt(t, old);
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->V != y->V) return x->V - y->V;
    return x->typ - y->typ;
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
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    if (hi > MAXV) hi = MAXV;
    if (lo < 2) lo = 2;

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int Kk = 1; Kk <= MAXK; Kk++) {
        long Nlo = (lo + 2L * Kk - 1) / (2L * Kk);
        long Nhi = hi / (2L * Kk);
        if (Nlo < d + 1) Nlo = d + 1;
        if (Nhi > MAXN) Nhi = MAXN;
        for (long n = Nlo; n <= Nhi; n++) {
            if (nc < MAXCAND) {
                Cand cd = {0, 0, 0, 0, 0, (int)n, Kk, (int)(2 * Kk * n)};
                cand[nc++] = cd;
            }
            for (int q = 3; q < MAXQ; q++) {
                int p, k;
                if (n % q) continue;
                if (!factor_pp(q, &p, &k)) continue;
                int c = (int)(n / q);
                if (c < 1 || (q - 1) % c) continue;
                if (nc < MAXCAND) {
                    Cand cd = {1, q, p, k, c, (int)n, Kk, (int)(2 * Kk * n)};
                    cand[nc++] = cd;
                }
            }
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Repeated passes in ascending order. Each attempt gets 20% of the remaining
     * time (at least 1 s). Candidates that failed earlier are retried with fresh starts. */
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            if (cand[ci].V <= bestV) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = 0.2 * rem;
            if (slice < 1.0) slice = 1.0;
            if (slice > rem) slice = rem;
            K = cand[ci].K;
            build_group(&cand[ci]);
            V = cand[ci].V;
            if (search_cand(now() + slice)) {
                bestV = V;
                bestK = K;
                bestN = N;
                memcpy(bestAdj, adj, sizeof(int) * (size_t)(V * d));
            }
        }
        if (!tried || t_end - now() < 0.3) break;
    }

    if (bestV == 0) {
        printf("0 0\n");
        return 0;
    }
    int L = bestK * bestN;
    printf("%d %d\n", bestV, L * d);
    for (int x = 0; x < L; x++)
        for (int s = 0; s < d; s++)
            printf("%d %d\n", x, bestAdj[x * d + s]);
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

    # Multi-orbit lift search: aim above the best known order, with a bounded window.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 2, mb // 8)
        hi = min(mb // 2, 4 * lo)
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
