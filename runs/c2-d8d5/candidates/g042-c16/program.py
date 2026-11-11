"""Voltage-lift annealing: a different C engine that searches random lifts over small groups.

Exact diameter cost: a lift is fibre-transitive (left translation acts on every fibre), so
eccentricities only need checking from one representative per base vertex.
"""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact and small constructions (calibration cases return immediately).
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
# C engine: random voltage lifts of base graphs with p vertices per side over
# small groups Z_m x| Z_k. Simulated annealing on voltages and layer permutations,
# cost = unreached pairs from one representative per fibre (exact for lifts),
# plus a penalty for duplicate edges. A ladder keeps raising the lift order.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Voltage-lift annealing for bipartite degree-diameter graphs.
 * Usage:  prog d D seed time_limit   (stdin is ignored)
 * stdout: "n m" + edge lines, the largest valid graph found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 32
#define MAXP 8
#define MAXG 1024
#define MAXW (MAXN / 64)
#define PEN_DUP 500

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
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

/* ---------------- group Z_m x|_r Z_k, element a*k+b, identity 0 ---------------- */
static int GN, GM, GK, GR;
static int rp[MAXG];
static int tab[MAXG * MAXG];

static int gmul_raw(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    return (int)((a + (long)rp[b] * c) % GM) * GK + (b + e) % GK;
}

static void make_group(int N) {
    int divs[64], nd = 0;
    GN = N;
    for (int k = 1; k <= N && nd < 64; k++)
        if (N % k == 0) divs[nd++] = k;
    GK = divs[rndint(nd)];
    GM = N / GK;
    GR = 1;
    if (GM == 1) {
        GR = 0;
    } else if (GM > 2) {
        for (int t = 0; t < 80; t++) {
            int r = 2 + rndint(GM - 2);
            if (gcd(r, GM) == 1 && powmod(r, GK, GM) == 1 % GM) { GR = r; break; }
        }
    }
    rp[0] = 1 % GM;
    for (int b = 1; b < GK; b++) rp[b] = (int)((long)rp[b - 1] * GR % GM);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            tab[x * N + y] = gmul_raw(x, y);
}

/* ---------------- lift state ---------------- */
static int PP, NN;
static int perm[MAXD][MAXP], vol[MAXD][MAXP];
static int adj[MAXN][MAXD], deg[MAXN];

static int bdeg[MAXN], badj[MAXN][MAXD];
static int bestn = 0;

static void build(void) {
    int n = 2 * PP * NN;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int t = 0; t < d; t++)
        for (int i = 0; i < PP; i++) {
            int j = perm[t][i], s = vol[t][i];
            for (int x = 0; x < NN; x++) {
                int u = i * NN + x;
                int w = PP * NN + j * NN + tab[x * NN + s];
                adj[u][deg[u]++] = w;
                adj[w][deg[w]++] = u;
            }
        }
}

static int count_dups(void) {
    int c = 0;
    for (int t = 0; t < d; t++)
        for (int t2 = t + 1; t2 < d; t2++)
            for (int i = 0; i < PP; i++)
                if (perm[t][i] == perm[t2][i] && vol[t][i] == vol[t2][i]) c++;
    return c;
}

static int mark[MAXN], qbuf[MAXN];
static int stampv = 0;

/* Unreached pairs counted from one representative per fibre (exact for fibre-transitive lifts). */
static long reach_deficit(int n) {
    long unr = 0;
    for (int b = 0; b < 2 * PP; b++) {
        int src = b * NN;
        stampv++;
        int head = 0, tail = 0;
        qbuf[tail++] = src;
        mark[src] = stampv;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int v = qbuf[head++];
                for (int k = 0; k < d; k++) {
                    int u = adj[v][k];
                    if (mark[u] != stampv) {
                        mark[u] = stampv;
                        qbuf[tail++] = u;
                    }
                }
            }
        }
        unr += n - tail;
    }
    return unr;
}

static long cost_now(void) {
    build();
    long dup = count_dups();
    return reach_deficit(2 * PP * NN) + (long)PEN_DUP * dup;
}

static void random_state(void) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < PP; i++) perm[t][i] = i;
        for (int i = PP - 1; i > 0; i--) {
            int j = rndint(i + 1), s = perm[t][i];
            perm[t][i] = perm[t][j];
            perm[t][j] = s;
        }
        for (int i = 0; i < PP; i++) vol[t][i] = rndint(NN);
    }
}

/* Simulated annealing on voltages and layer permutations until cost 0 or time runs out. */
static int sa_run(double t_a, double t_b) {
    long cur = cost_now();
    double T = 1.0;
    long it = 0;
    while (cur > 0) {
        if ((it & 15) == 0) {
            double tn = now();
            if (tn > t_b) break;
            double frac = (tn - t_a) / (t_b - t_a);
            T = 2.0 * (1.0 - frac) + 0.05;
        }
        it++;
        int t = rndint(d), i = rndint(PP);
        int kind = (PP > 1 && rndint(2)) ? 1 : 0;
        int oldv = vol[t][i], i2 = -1;
        if (kind == 0) {
            int nv = rndint(NN);
            if (nv == oldv) continue;
            vol[t][i] = nv;
        } else {
            i2 = rndint(PP);
            if (i2 == i) continue;
            int tmp = perm[t][i];
            perm[t][i] = perm[t][i2];
            perm[t][i2] = tmp;
        }
        long nc = cost_now();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            if (kind == 0) {
                vol[t][i] = oldv;
            } else {
                int tmp = perm[t][i];
                perm[t][i] = perm[t][i2];
                perm[t][i2] = tmp;
            }
        }
    }
    return cur == 0;
}

/* Exact all-pairs check with bitsets. */
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

static long bad_pairs_adj(int n) {
    int W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s = cur + (size_t)adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        total += n - c;
    }
    return total / 2;
}

static int full_valid(void) {
    int n = 2 * PP * NN;
    if (n <= 0 || n > MAXN) return 0;
    build();
    for (int v = 0; v < n; v++) {
        if (deg[v] != d) return 0;
        int sv = v >= PP * NN;
        for (int k = 0; k < deg[v]; k++) {
            int u = adj[v][k];
            if (u < 0 || u >= n || u == v) return 0;
            if ((u >= PP * NN) == sv) return 0;
            for (int j = 0; j < k; j++)
                if (adj[v][j] == u) return 0;
        }
    }
    return bad_pairs_adj(n) == 0;
}

static void store_best(void) {
    int n = 2 * PP * NN;
    bestn = n;
    for (int v = 0; v < n; v++) {
        bdeg[v] = deg[v];
        memcpy(badj[v], adj[v], sizeof(int) * deg[v]);
    }
}

static void print_best(void) {
    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return;
    }
    if (bestn == 0) {
        printf("%d %d\n", 2 * d, d * d);
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
        return;
    }
    long m = 0;
    for (int u = 0; u < bestn; u++)
        for (int k = 0; k < bdeg[u]; k++)
            if (u < badj[u][k]) m++;
    printf("%d %ld\n", bestn, m);
    for (int u = 0; u < bestn; u++)
        for (int k = 0; k < bdeg[u]; k++)
            if (u < badj[u][k]) printf("%d %d\n", u, badj[u][k]);
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
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) {
        print_best();
        return 0;
    }

    long moore = moore_bound();
    int skips = 0;
    while (now() < t_end) {
        int r = rndint(12);
        int p = r < 2 ? 1 : r < 4 ? 2 : r < 6 ? 3 : r < 8 ? 4 : r < 10 ? 5 : 6;
        int base = bestn / (2 * p);
        int N = base + 1;
        if (rndint(3) == 0) N += rndint(base / 16 + 2);
        int minN = (d + p - 1) / p;
        if (N < minN) N = minN;
        if (N > MAXG) N = MAXG;
        long n = 2L * p * N;
        if (n > MAXN || n > moore || n <= bestn) {
            if (++skips > 5000) break;
            continue;
        }
        skips = 0;
        make_group(N);
        PP = p;
        NN = N;
        random_state();
        double rem = t_end - now();
        double slice = rem < 4.0 ? rem : 4.0;
        if (slice < 0.05) break;
        double ta = now();
        if (sa_run(ta, ta + slice) && full_valid()) store_best();
    }
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
        """Return the new graph if it is a larger valid graph, else None."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return best
        return None

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

    # Search: C voltage-lift annealing over small groups, climbing the order ladder.
    if D >= 2:
        budget = end - time.monotonic() - 0.5
        if budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                 stdin_graph=None, timeout=budget + 10)
                out = lib.parse_graph_text(text)
                consider(out[0], out[1])
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
