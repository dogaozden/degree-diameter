"""Multi-fiber voltage-lift search for the bipartite degree-diameter problem.

Bold change from the parent. The parent searched only single-fiber Haar graphs
(one left and one right vertex class) over F_q x| H. This version searches a
different family: a base bipartite multigraph with B vertices per side (B = 1, 2, 3),
where every base vertex has degree d, lifted by a finite group G of order N.
Dart (i, j, g) joins (i, x) to (B + j, x*g) for all x in G. The base degree matrix
M is a sum of d random permutation matrices, so every row and column sums to d.
Groups are affine F_q x| H (as in the parent) or metacyclic Z_m x|_r Z_k.

Left multiplication by G is an automorphism, so each fiber is vertex-transitive.
The diameter check therefore needs BFS runs from one vertex per fiber (2B runs).
Simulated annealing moves single darts. Configurations are tried in ascending
order of vertex count, with random restarts over repeated passes.

Fallbacks are K_{d,d}, the projective-plane incidence graph (exact Moore graph
for D = 3), the Araujo-Lopez graph, and W(q) for D = 4. Every candidate is
checked with lib.is_valid before it is returned.
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

#define MAXQ 256
#define MAXN 2048
#define MAXD 32
#define MAXB 3
#define MAXDART (MAXB * MAXD)
#define MAXV (2 * MAXB * MAXN)
#define MAXCFG 60000
#define MAXEDGE (MAXV * MAXD / 2 + 16)
#define MAXK 16
#define ITERS 6000

typedef struct { int type, B, N, f1, f2, f3, f4; unsigned key; } Cfg;

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

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

/* ------------------------------------------------------------ groups */

static int Hel[MAXQ], hidx[MAXQ], PWG[MAXQ];
static int HM[MAXQ * MAXQ];
static int GT[MAXN * MAXN];
static int GI[MAXN];
static int cur_N;

/* Affine group F_q x| H, |H| = c, element (a, h_j) coded a*c + j. */
static void build_affine(int q, int p, int k, int c) {
    build_field(q, p, k);
    int N = q * c;
    int g = (q == 2) ? 1 : -1;
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
            GT[x * N + y] = na * c + HM[j * c + t];
        }
    }
    cur_N = N;
}

/* Metacyclic group Z_m x|_r Z_kk, element (a, b) coded a*kk + b. */
static void build_meta(int m, int kk, int r) {
    int N = m * kk;
    int pw[MAXK];
    pw[0] = 1 % m;
    for (int b = 1; b < kk; b++) pw[b] = (int)(((long)pw[b - 1] * r) % m);
    for (int x = 0; x < N; x++) {
        int a = x / kk, b = x % kk;
        for (int y = 0; y < N; y++) {
            int c = y / kk, e = y % kk;
            int na = (int)((a + (long)pw[b] * c) % m);
            GT[x * N + y] = na * kk + (b + e) % kk;
        }
    }
    cur_N = N;
}

static void setup_cfg(const Cfg *c) {
    if (c->type == 0) build_affine(c->f1, c->f2, c->f3, c->f4);
    else build_meta(c->f1, c->f2, c->f3);
    int N = cur_N;
    for (int x = 0; x < N; x++) {
        GI[x] = 0;
        for (int y = 0; y < N; y++)
            if (GT[x * N + y] == 0) { GI[x] = y; break; }
    }
}

/* ------------------------------------------------------------ lift state */

static int B_ = 1, N_ = 1;
static int dpi[MAXDART], dpj[MAXDART], dg[MAXDART];
static int Lout[MAXB][MAXD], Rin[MAXB][MAXD];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static int conflict(int s, int g) {
    for (int s2 = 0; s2 < B_ * d; s2++)
        if (s2 != s && dpi[s2] == dpi[s] && dpj[s2] == dpj[s] && dg[s2] == g)
            return 1;
    return 0;
}

static int conflict_pre(int s, int g) {
    for (int s2 = 0; s2 < s; s2++)
        if (dpi[s2] == dpi[s] && dpj[s2] == dpj[s] && dg[s2] == g)
            return 1;
    return 0;
}

/* Random base degree matrix (sum of d random permutation matrices), then random darts. */
static void randomize_structure(void) {
    int B = B_;
    int M[MAXB][MAXB];
    memset(M, 0, sizeof(M));
    for (int rep = 0; rep < d; rep++) {
        int perm[MAXB];
        for (int i = 0; i < B; i++) perm[i] = i;
        for (int i = B - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        for (int i = 0; i < B; i++) M[i][perm[i]]++;
    }
    int t = 0;
    for (int i = 0; i < B; i++)
        for (int j = 0; j < B; j++)
            for (int r = 0; r < M[i][j]; r++) {
                dpi[t] = i;
                dpj[t] = j;
                t++;
            }
    int cl[MAXB] = {0}, cr[MAXB] = {0};
    for (int s = 0; s < B * d; s++) {
        int i = dpi[s], j = dpj[s];
        Lout[i][cl[i]++] = s;
        Rin[j][cr[j]++] = s;
    }
    for (int s = 0; s < B * d; s++) {
        int g;
        do { g = rndint(N_); } while (conflict_pre(s, g));
        dg[s] = g;
    }
}

/* Sum over the 2B fiber representatives of vertices NOT within distance D. */
static long cost_eval(void) {
    int B = B_, N = N_, BN = B * N, V = 2 * BN;
    long total = 0;
    for (int f = 0; f < 2 * B; f++) {
        int src = f * N;
        stamp_++;
        int head = 0, tail = 0;
        que[tail++] = src;
        vis[src] = stamp_;
        for (int lvl = 0; lvl < D && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int v = que[head++];
                if (v < BN) {
                    int i = v / N, x = v - i * N;
                    for (int s = 0; s < d; s++) {
                        int t = Lout[i][s];
                        int u = (B + dpj[t]) * N + GT[x * N + dg[t]];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
                } else {
                    int w = v - BN;
                    int j = w / N, y = w - j * N;
                    for (int s = 0; s < d; s++) {
                        int t = Rin[j][s];
                        int u = dpi[t] * N + GT[y * N + GI[dg[t]]];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

static int nE = 0, bestV = 0;
static int Eu[MAXEDGE], Ev[MAXEDGE];

static void store_best(void) {
    int B = B_, N = N_;
    nE = 0;
    for (int i = 0; i < B; i++)
        for (int x = 0; x < N; x++)
            for (int s = 0; s < d; s++) {
                int t = Lout[i][s];
                Eu[nE] = i * N + x;
                Ev[nE] = (B + dpj[t]) * N + GT[x * N + dg[t]];
                nE++;
            }
    bestV = 2 * B * N;
}

#define SA_DUMMY 0

/* Simulated annealing over dart values for the current group. Returns 1 on diameter <= D. */
static int search(double until) {
    int BD = B_ * d;
    while (now() < until) {
        randomize_structure();
        long cost = cost_eval();
        if (cost == 0) return 1;
        double Ts = 0.05 * (double)cost + 1.0, Te = 0.3;
        for (int it = 0; it < ITERS; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / ITERS);
            int s = rndint(BD);
            int g;
            do { g = rndint(N_); } while (conflict(s, g));
            int old = dg[s];
            dg[s] = g;
            long c2 = cost_eval();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                if (cost == 0) return 1;
            } else {
                dg[s] = old;
            }
        }
    }
    return 0;
}

/* ------------------------------------------------------------ configurations */

static Cfg cfgs[MAXCFG];
static int ncfg = 0;

static void add_cfg(int type, int B, int N, int f1, int f2, int f3, int f4) {
    if (ncfg >= MAXCFG) return;
    Cfg c;
    c.type = type; c.B = B; c.N = N;
    c.f1 = f1; c.f2 = f2; c.f3 = f3; c.f4 = f4;
    c.key = (unsigned)rnd();
    cfgs[ncfg++] = c;
}

static void enumerate(int vlo, int vhi) {
    for (int B = 1; B <= MAXB; B++) {
        int Nlo = (vlo + 2 * B - 1) / (2 * B);
        int Nhi = vhi / (2 * B);
        if (Nlo < 2 * d) Nlo = 2 * d;
        if (Nhi > MAXN) Nhi = MAXN;
        for (int N = Nlo; N <= Nhi; N++) {
            for (int q = 2; q < MAXQ; q++) {
                if (N % q) continue;
                int p, k;
                if (!factor_pp(q, &p, &k)) continue;
                int c = N / q;
                if ((q - 1) % c) continue;
                add_cfg(0, B, N, q, p, k, c);
            }
            for (int kk = 1; kk <= 8; kk++) {
                if (N % kk) continue;
                int m = N / kk;
                if (m == 1) { add_cfg(1, B, N, 1, kk, 0, 0); continue; }
                for (int r = 1; r < m; r++) {
                    if (gcd_i(r, m) != 1) continue;
                    if (powmod_l(r, kk, m) != 1) continue;
                    add_cfg(1, B, N, m, kk, r, 0);
                }
            }
        }
    }
}

static int cmp_cfg(const void *a, const void *b) {
    const Cfg *x = (const Cfg *)a, *y = (const Cfg *)b;
    int vx = 2 * x->B * x->N, vy = 2 * y->B * y->N;
    if (vx != vy) return vx < vy ? -1 : 1;
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
    int vlo = atoi(argv[5]), vhi = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (vlo < 4) vlo = 4;
    if (vhi > MAXV) vhi = MAXV;

    enumerate(vlo, vhi);
    qsort(cfgs, (size_t)ncfg, sizeof(Cfg), cmp_cfg);

    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < ncfg; ci++) {
            Cfg *c = &cfgs[ci];
            int V = 2 * c->B * c->N;
            if (V <= bestV) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = 0.06 * rem;
            if (slice < 1.0) slice = 1.0;
            if (slice > rem) slice = rem;
            setup_cfg(c);
            B_ = c->B;
            N_ = c->N;
            if (search(now() + slice)) {
                store_best();
            }
        }
        if (!tried || t_end - now() < 0.3) break;
    }

    if (bestV <= 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestV, nE);
    for (int e = 0; e < nE; e++) printf("%d %d\n", Eu[e], Ev[e]);
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

    # Search: multi-fiber voltage lifts over affine and metacyclic groups.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
        vlo = max(best[0] + 1, mb // 4)
        vhi = mb // 3
        if budget > 2.0 and vlo <= vhi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), vlo, vhi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
