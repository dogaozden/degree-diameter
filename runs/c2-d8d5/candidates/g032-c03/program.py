"""Bi-Cayley lift search in C: simulated annealing over base permutations and voltages on Z_m x| Z_k."""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact small constructions (calibration cases return immediately).
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
# C engine: bi-Cayley lifts over Z_m x| Z_k. Cost = number of (block representative,
# vertex) pairs at distance > D, which is zero iff the lift has diameter <= D
# (left multiplication by the group is an automorphism, so 2*base representatives suffice).
# Base: d permutations sigma_t on p+p vertices with voltages vg[t][i].
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 16
#define MAXG 2048
#define MAXP 6

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
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

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* Group Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k). */
static int gm, gk, gr, N, P, n;
static int rp[MAXG];
static unsigned short mulT[MAXG][MAXG];

static void setup_group(int m, int k, int r, int NN) {
    gm = m; gk = k; gr = r; N = NN;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) {
            int a = x / k, b = x % k, c = y / k, e = y % k;
            int z = (int)(((long)a + (long)rp[b] * c) % m) * k + (b + e) % k;
            mulT[x][y] = (unsigned short)z;
        }
}

/* Uniform choice among all valid (m, k, r) with m*k = NN. */
static int pick_group(int NN, int *pm, int *pk, int *pr) {
    long cnt = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= NN; m++) {
        if (NN % m) continue;
        int k = NN / m;
        if (m == 1) {
            cnt++;
            if (rndint((int)cnt) == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (!cnt) return 0;
    *pm = bm; *pk = bk; *pr = br;
    return 1;
}

static int sig[MAXD][MAXP], vg[MAXD][MAXP];
static int nbr[MAXN][MAXD], ndeg[MAXN];
static int dist_[MAXN], que[MAXN];

static void init_state(void) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < P; i++) sig[t][i] = i;
        for (int i = P - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = sig[t][i]; sig[t][i] = sig[t][j]; sig[t][j] = s;
        }
        for (int i = 0; i < P; i++) vg[t][i] = rndint(N);
    }
}

static void build_nbr(void) {
    n = 2 * P * N;
    for (int v = 0; v < n; v++) ndeg[v] = 0;
    for (int t = 0; t < d; t++)
        for (int i = 0; i < P; i++) {
            int j = sig[t][i], g = vg[t][i];
            for (int x = 0; x < N; x++) {
                int a = i * N + x;
                int b = (P + j) * N + mulT[x][g];
                nbr[a][ndeg[a]++] = b;
                nbr[b][ndeg[b]++] = a;
            }
        }
}

static int dup_count(void) {
    int c = 0;
    for (int i = 0; i < P; i++)
        for (int t1 = 0; t1 < d; t1++)
            for (int t2 = t1 + 1; t2 < d; t2++)
                if (sig[t1][i] == sig[t2][i] && vg[t1][i] == vg[t2][i]) c++;
    return c;
}

static long unreached_from(int src) {
    for (int v = 0; v < n; v++) dist_[v] = -1;
    int h = 0, t = 0;
    long cnt = 1;
    dist_[src] = 0;
    que[t++] = src;
    while (h < t) {
        int v = que[h++];
        if (dist_[v] >= D) continue;
        for (int k = 0; k < d; k++) {
            int u = nbr[v][k];
            if (dist_[u] < 0) {
                dist_[u] = dist_[v] + 1;
                que[t++] = u;
                cnt++;
            }
        }
    }
    return n - cnt;
}

static long full_cost(void) {
    build_nbr();
    long dc = dup_count();
    long tot = 0;
    for (int b = 0; b < 2 * P; b++) tot += unreached_from(b * N);
    return tot + 2L * n * dc;
}

static int run_sa(long iters) {
    init_state();
    long cur = full_cost();
    if (cur == 0) return 1;
    double T0 = 6.0, T1 = 0.3;
    for (long it = 0; it < iters; it++) {
        if ((it & 63) == 0 && now() > t_end) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int t = rndint(d);
        int mv, a = 0, b = 0, oldg = 0;
        if (P >= 2 && rnd01() < 0.4) {
            a = rndint(P);
            b = rndint(P - 1);
            if (b >= a) b++;
            int tmp = sig[t][a]; sig[t][a] = sig[t][b]; sig[t][b] = tmp;
            mv = 1;
        } else {
            a = rndint(P);
            oldg = vg[t][a];
            vg[t][a] = rndint(N);
            mv = 2;
        }
        long nc = full_cost();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            if (mv == 1) {
                int tmp = sig[t][a]; sig[t][a] = sig[t][b]; sig[t][b] = tmp;
            } else {
                vg[t][a] = oldg;
            }
        }
    }
    return cur == 0;
}

static int best_found = 0;
static int bP, bN, bm, bk, br;
static int bsig[MAXD][MAXP], bvg[MAXD][MAXP];

static void record(void) {
    bP = P; bN = N; bm = gm; bk = gk; br = gr;
    memcpy(bsig, sig, sizeof sig);
    memcpy(bvg, vg, sizeof vg);
    best_found = 1;
}

static void search(void) {
    static const int plist[12] = {1, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 6};
    long moore = moore_bound();
    while (now() < t_end) {
        int p = plist[rndint(12)];
        long bestn = best_found ? 2L * bP * bN : 0;
        if (bestn >= moore) break;
        long lim = MAXG;
        long l2 = MAXN / (2L * p);
        if (l2 < lim) lim = l2;
        long l3 = moore / (2L * p);
        if (l3 < lim) lim = l3;
        if (lim < 1) continue;
        long Nt = bestn / (2L * p) + 1 + rndint(3);
        if (Nt > lim) Nt = lim;
        if (Nt * p < d) continue;
        int m, k, r;
        if (!pick_group((int)Nt, &m, &k, &r)) continue;
        setup_group(m, k, r, (int)Nt);
        P = p;
        if (run_sa(15000)) record();
    }
}

static void print_k_dd(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static void print_best(void) {
    if (best_found) {
        P = bP;
        setup_group(bm, bk, br, bN);
        memcpy(sig, bsig, sizeof sig);
        memcpy(vg, bvg, sizeof vg);
        if (full_cost() == 0) {
            long m = (long)n * d / 2;
            printf("%d %ld\n", n, m);
            for (int v = 0; v < n; v++)
                for (int k = 0; k < d; k++) {
                    int u = nbr[v][k];
                    if (v < u) printf("%d %d\n", v, u);
                }
            return;
        }
    }
    print_k_dd();
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXD) {
        print_k_dd();
        return 0;
    }
    search();
    print_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Replace the best graph if (n, e) is a larger valid graph."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: C simulated annealing over bi-Cayley lifts, growing the order.
    if D >= 2:
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=None, timeout=c_budget + 8)
                n_out, e_out = lib.parse_graph_text(text)
                consider(n_out, e_out)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
