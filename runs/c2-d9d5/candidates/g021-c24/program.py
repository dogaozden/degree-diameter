"""Bi-Cayley voltage-lift search for the bipartite degree-diameter problem.

Change from the parent: the parent searched only Haar graphs (one base vertex per side),
that is, one group with one connection set. This version searches bi-Cayley graphs with a
B x B base (B = 1, 2, 3) over a wider family of groups: cyclic, Z_m x|_r Z_k, and
F_p x| H for prime p. Each base block (i, j) carries a set S_ij of voltages, with
L_{i,x} ~ R_{j, x s} for s in S_ij. The block sizes come from a circulant pattern whose
row and column sums equal d. The graph is d-regular, bipartite and simple.

Diameter test: left multiplication by G is an automorphism, so every vertex is in the
orbit of some L_{i,e} or R_{j,e}. Diameter <= D is therefore equivalent to all 2B BFS
runs from those representatives reaching everything within D. The cost is the number of
unreached (source, vertex) pairs, minimised by simulated annealing over the voltages.

Candidates are tried in ascending order of order, starting above the current best, so
success at one order raises the bar for the next. A failed candidate gets a fresh random
start in later passes. The Python side keeps a valid fallback (K_{d,d}, PG(2,q),
Araujo-Pardo-Lopez, or W(q) for D = 4) and checks every result with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley voltage-lift search.
 * Usage: prog d D seed time_limit lo hi
 *   lo, hi bound the total vertex count 2*B*N of the output.
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 5000
#define MAXD 40
#define MAXB 3
#define MAXCAND 200000
#define MAXGL 256
#define MAXK 40

typedef struct { int B, type, m, k, r, q, c, N; } Cand;

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
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Primitive root of a prime q. */
static int prim_root(int q) {
    int n = q - 1, fac[32], nf = 0, t = n;
    for (int f = 2; (long long)f * f <= t; f++)
        if (t % f == 0) {
            fac[nf++] = f;
            while (t % f == 0) t /= f;
        }
    if (t > 1) fac[nf++] = t;
    for (int g = 2; g < q; g++) {
        int ok = 1;
        for (int i = 0; i < nf && ok; i++)
            if (powmod(g, n / fac[i], q) == 1) ok = 0;
        if (ok) return g;
    }
    return -1;
}

/* ------------------------------------------------------------ groups
 * type 0: cyclic Z_N.
 * type 1: Z_m x|_r Z_k, element a*k+b, product (a,b)(c,e) = (a + r^b c, b+e).
 * type 2: F_q x| H, |H| = c, element a*c+s, h_s = g^(s*(q-1)/c),
 *         product (a,s)(b,t) = (a + h_s b, s+t). Identity is code 0 in every type.
 */
static int GT, GM, GK, GR, GQ, GC, GN;
static int TAB[MAXN];

static void set_group(const Cand *cd) {
    GT = cd->type;
    GM = cd->m;
    GK = cd->k;
    GR = cd->r;
    GQ = cd->q;
    GC = cd->c;
    GN = cd->N;
    if (GT == 1) {
        TAB[0] = 1 % GM;
        for (int b = 1; b < GK; b++) TAB[b] = (int)((long long)TAB[b - 1] * GR % GM);
    } else if (GT == 2) {
        int g = prim_root(GQ);
        long long h = powmod(g, (GQ - 1) / GC, GQ);
        long long cur = 1;
        for (int s = 0; s < GC; s++) {
            TAB[s] = (int)cur;
            cur = cur * h % GQ;
        }
    }
}

static inline int gmul(int x, int y) {
    if (GT == 0) {
        int s = x + y;
        return s >= GN ? s - GN : s;
    }
    if (GT == 1) {
        int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
        int na = (int)((a + (long long)TAB[b] * c) % GM);
        int nb = b + e;
        if (nb >= GK) nb -= GK;
        return na * GK + nb;
    }
    int a = x / GC, s = x % GC, b = y / GC, t = y % GC;
    int na = (int)((a + (long long)TAB[s] * b) % GQ);
    int nt = s + t;
    if (nt >= GC) nt -= GC;
    return na * GC + nt;
}

static inline int ginv(int x) {
    if (GT == 0) return x == 0 ? 0 : GN - x;
    if (GT == 1) {
        int a = x / GK, b = x % GK;
        int nb = (GK - b) % GK;
        int na = (int)(((long long)(GM - TAB[nb]) % GM) * a % GM);
        return na * GK + nb;
    }
    int a = x / GC, s = x % GC;
    int ns = (GC - s) % GC;
    int na = (int)(((long long)(GQ - TAB[ns]) % GQ) * a % GQ);
    return na * GC + ns;
}

/* ------------------------------------------------------------ bi-Cayley state
 * Vertices: L_{i,x} = i*N + x, R_{j,y} = B*N + j*N + y, for i, j < B.
 * Block (i,j) has voltages SEL[i][j][0..PAT[i][j]-1].
 * L_{i,x} ~ R_{j, x*s}; R_{j,y} ~ L_{i, y*s^-1}.
 */
static int CB;
static int PAT[MAXB][MAXB];
static int SEL[MAXB][MAXB][MAXD];
static int PL[MAXB][MAXB][MAXD][MAXN];
static int PR[MAXB][MAXB][MAXD][MAXN];
static int vis[2 * MAXB * MAXN], que[2 * MAXB * MAXN];
static int stamp_ = 0;

static Cand bestCand;
static int bestTotal = 0;
static int bestPAT[MAXB][MAXB];
static int bestSEL[MAXB][MAXB][MAXD];

static void setel(int i, int j, int t, int x) {
    SEL[i][j][t] = x;
    int xi = ginv(x);
    int *pl = PL[i][j][t], *pr = PR[i][j][t];
    for (int y = 0; y < GN; y++) {
        pl[y] = gmul(y, x);
        pr[y] = gmul(y, xi);
    }
}

static int in_block(int i, int j, int upto, int x) {
    for (int t = 0; t < upto; t++)
        if (SEL[i][j][t] == x) return 1;
    return 0;
}

/* Number of vertices within distance D of src. */
static int reach_count(int src) {
    int B = CB, N = GN, BN = B * N;
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
                for (int j = 0; j < B; j++) {
                    int p = PAT[i][j];
                    for (int t = 0; t < p; t++) {
                        int u = BN + j * N + PL[i][j][t][x];
                        if (vis[u] != stamp_) {
                            vis[u] = stamp_;
                            que[tail++] = u;
                        }
                    }
                }
            } else {
                int w = v - BN;
                int j = w / N, y = w - j * N;
                for (int i = 0; i < B; i++) {
                    int p = PAT[i][j];
                    for (int t = 0; t < p; t++) {
                        int u = i * N + PR[i][j][t][y];
                        if (vis[u] != stamp_) {
                            vis[u] = stamp_;
                            que[tail++] = u;
                        }
                    }
                }
            }
        }
    }
    return tail;
}

/* Unreached (source, vertex) pairs over the 2B class representatives. 0 iff diameter <= D. */
static long cost_all(void) {
    int B = CB, N = GN, V = 2 * B * N;
    long c = 0;
    for (int i = 0; i < B; i++) c += V - reach_count(i * N);
    for (int j = 0; j < B; j++) c += V - reach_count(B * N + j * N);
    return c;
}

/* Circulant pattern PAT[i][j] = w[(j-i) mod B], with composition w of d into B parts.
 * Row and column sums are d. Requires the nonzero parts to generate Z_B, so the base is connected. */
static int make_pattern(int B) {
    for (int attempt = 0; attempt < 200; attempt++) {
        int w[MAXB];
        int rem = d;
        for (int k = 0; k < B - 1; k++) {
            w[k] = rndint(rem + 1);
            rem -= w[k];
        }
        w[B - 1] = rem;
        int g = B;
        for (int k = 0; k < B; k++)
            if (w[k] > 0) g = gcd_i(g, k);
        if (g != 1) continue;
        for (int i = 0; i < B; i++)
            for (int j = 0; j < B; j++)
                PAT[i][j] = w[((j - i) % B + B) % B];
        return 1;
    }
    return 0;
}

/* Simulated annealing over the voltages for one candidate. Returns 1 on success (diameter <= D). */
static int try_cand(const Cand *cd, double until) {
    set_group(cd);
    CB = cd->B;
    int B = CB, N = GN;
    int bi[MAXB * MAXB], bj[MAXB * MAXB];
    while (now() < until) {
        if (!make_pattern(B)) return 0;
        int nb = 0;
        for (int i = 0; i < B; i++)
            for (int j = 0; j < B; j++)
                if (PAT[i][j] > 0) {
                    bi[nb] = i;
                    bj[nb] = j;
                    nb++;
                }
        for (int b = 0; b < nb; b++) {
            int i = bi[b], j = bj[b], p = PAT[i][j];
            for (int t = 0; t < p; t++) {
                int x;
                do { x = rndint(N); } while (in_block(i, j, t, x));
                setel(i, j, t, x);
            }
        }
        long cost = cost_all();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        const int iters = 6000;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int b = rndint(nb);
            int i = bi[b], j = bj[b], p = PAT[i][j];
            int t = rndint(p);
            int old = SEL[i][j][t];
            int x;
            do { x = rndint(N); } while (in_block(i, j, p, x));
            setel(i, j, t, x);
            long c2 = cost_all();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                setel(i, j, t, old);
            }
        }
        if (cost == 0) {
            bestCand = *cd;
            bestTotal = 2 * B * N;
            memcpy(bestPAT, PAT, sizeof(PAT));
            memcpy(bestSEL, SEL, sizeof(SEL));
            return 1;
        }
    }
    return 0;
}

static Cand cand[MAXCAND];
static Cand gl[MAXGL];
static int ncand = 0;

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    long tx = 2L * x->B * x->N, ty = 2L * y->B * y->N;
    if (tx != ty) return tx < ty ? -1 : 1;
    if (x->B != y->B) return x->B - y->B;
    return x->type - y->type;
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

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }

    int nlo[MAXB + 1], nhi[MAXB + 1];
    long gmin = 1L << 30, gmax = 0;
    for (int B = 1; B <= MAXB; B++) {
        long a = (lo + 2L * B - 1) / (2L * B);
        long b = hi / (2L * B);
        if (a < d + 2) a = d + 2;
        if (b > MAXN) b = MAXN;
        nlo[B] = (int)a;
        nhi[B] = (int)b;
        if (a <= b) {
            if (a < gmin) gmin = a;
            if (b > gmax) gmax = b;
        }
    }

    /* Enumerate group candidates for each order N, then pair them with each B. */
    for (long NN = gmin; NN <= gmax; NN++) {
        int N = (int)NN;
        int anyB = 0;
        for (int B = 1; B <= MAXB; B++)
            if (N >= nlo[B] && N <= nhi[B]) anyB = 1;
        if (!anyB) continue;

        int ng = 0;
        Cand c0 = {0, 0, N, 0, 0, 0, 0, N};
        gl[ng++] = c0;
        for (int k = 2; k <= MAXK && 2 * k <= N; k++) {
            if (N % k) continue;
            int m = N / k;
            int cnt = 0;
            int r0 = 1 + rndint(m - 1);
            for (int s = 0; s < m - 1 && cnt < 3 && ng < MAXGL; s++) {
                int r = 1 + (r0 - 1 + s) % (m - 1);
                if (gcd_i(r, m) != 1) continue;
                if (powmod(r, k, m) != 1) continue;
                Cand c = {0, 1, m, k, r, 0, 0, N};
                gl[ng++] = c;
                cnt++;
            }
        }
        int t = N, pr[16], np = 0;
        for (int f = 2; (long long)f * f <= t; f++)
            if (t % f == 0) {
                pr[np++] = f;
                while (t % f == 0) t /= f;
            }
        if (t > 1) pr[np++] = t;
        for (int i = 0; i < np; i++) {
            int q = pr[i], c = N / q;
            if (c >= 2 && (q - 1) % c == 0 && ng < MAXGL) {
                Cand cc = {0, 2, 0, 0, 0, q, c, N};
                gl[ng++] = cc;
            }
        }
        for (int g = 0; g < ng; g++)
            for (int B = 1; B <= MAXB; B++) {
                if (N < nlo[B] || N > nhi[B]) continue;
                if (ncand >= MAXCAND) break;
                Cand cc = gl[g];
                cc.B = B;
                cand[ncand++] = cc;
            }
    }
    if (ncand == 0) {
        printf("0 0\n");
        return 0;
    }
    /* Shuffle so equal-order candidates are tried in random order, then sort ascending. */
    for (int i = ncand - 1; i > 0; i--) {
        int j = rndint(i + 1);
        Cand tmp = cand[i];
        cand[i] = cand[j];
        cand[j] = tmp;
    }
    qsort(cand, (size_t)ncand, sizeof(Cand), cmp_cand);

    /* Repeated passes in ascending order of total size. Candidates at or below the
     * current best are skipped. Each attempt gets 20% of the remaining time, clamped to [1, 4] s. */
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < ncand; ci++) {
            int tot = 2 * cand[ci].B * cand[ci].N;
            if (tot <= bestTotal) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = 0.2 * rem;
            if (slice < 1.0) slice = 1.0;
            if (slice > 4.0) slice = 4.0;
            if (slice > rem) slice = rem;
            try_cand(&cand[ci], now() + slice);
        }
        if (!tried || t_end - now() < 0.3) break;
    }

    if (bestTotal == 0) {
        printf("0 0\n");
        return 0;
    }
    CB = bestCand.B;
    set_group(&bestCand);
    int B = CB, N = GN;
    printf("%d %d\n", 2 * B * N, B * N * d);
    for (int i = 0; i < B; i++)
        for (int x = 0; x < N; x++)
            for (int j = 0; j < B; j++)
                for (int t = 0; t < bestPAT[i][j]; t++) {
                    int v = B * N + j * N + gmul(x, bestSEL[i][j][t]);
                    printf("%d %d\n", i * N + x, v);
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

    # Bold search: bi-Cayley lifts with B = 1..3 base vertices per side over several groups.
    # Only totals above the current best are searched, in ascending order.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
        lo = max(best[0] + 1, mb // 5)
        hi = mb
        if budget > 3.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
