"""Multi-orbit voltage-lift search for the bipartite degree-diameter problem.

Change in this version: the parent searched only Haar graphs, which are one-orbit
lifts (B = 1) over one group. This version searches B-orbit lifts with B = 1..4
base vertices per side over metacyclic groups Z_m x|_r Z_k (r^k = 1 mod m). The
cyclic and affine groups used by the parent are included as special cases.

Graph: left vertices (i, x), right vertices (j, y), i, j < B, x, y in G, |G| = N.
Each of d "darts" t has a permutation sig[t] of the B base vertices and a voltage
vol[t][i] in G, giving edges (i, x) ~ (sig[t][i], x * vol[t][i]). The graph is
d-regular and bipartite on 2BN vertices. It is simple when, for each i, the pairs
(sig[t][i], vol[t][i]) are distinct over t. Left multiplication by G is an
automorphism, so diameter <= D iff BFS from the 2B vertices (i, e) and (j, e)
reaches everything within D. Simulated annealing minimises the number of
uncovered (source, vertex) pairs.

Python keeps the projective-plane, Araujo-Lopez, W(q) and K_{d,d} baselines, and
every returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit voltage-lift search over metacyclic groups.
 * Usage: prog d D seed time_limit best_n      (stdin ignored)
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1600
#define MAXB 4
#define MAXD 16
#define MAXV (2 * MAXB * MAXN)
#define MAXCAND 200000

typedef struct { int N, m, k, r; } Cand;

static Cand cand[MAXCAND];
static int ncand = 0;
static int cstart[MAXN + 2], ccount[MAXN + 2];

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

static long long powmod_ll(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Metacyclic groups Z_m x|_r Z_k: elements (a,b) coded a*k+b,
 * (a,b)(c,e) = (a + r^b c, b + e), valid when r^k = 1 mod m and gcd(r,m) = 1. */
static void enumerate_groups(void) {
    ncand = 0;
    for (int N = 1; N <= MAXN; N++) {
        cstart[N] = ncand;
        for (int k = 1; k <= N; k++) {
            if (N % k) continue;
            int m = N / k;
            for (int r = 0; r < m; r++) {
                if (gcd_i(r, m) != 1) continue;
                if (powmod_ll(r, k, m) != 1 % m) continue;
                if (ncand < MAXCAND) {
                    cand[ncand].N = N;
                    cand[ncand].m = m;
                    cand[ncand].k = k;
                    cand[ncand].r = r;
                    ncand++;
                }
            }
        }
        ccount[N] = ncand - cstart[N];
    }
}

/* ------------------------------------------------------------ group tables */

static int MT[MAXN * MAXN];
static int INVT[MAXN];
static int PWR[MAXN];
static int GN, GM, GK, GR;

static void build_group(int m, int k, int r) {
    int N = m * k;
    GN = N; GM = m; GK = k; GR = r;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        PWR[b] = (int)p;
        p = p * r % m;
    }
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            int na = (int)((a + (long long)PWR[b] * c) % m);
            int ne = (b + e) % k;
            MT[x * N + y] = na * k + ne;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INVT[x] = y; break; }
}

/* ------------------------------------------------------------ lift state */

static int B, N;
static int sig[MAXD][MAXB], vol[MAXD][MAXB];
static int isig[MAXD][MAXB], vinv[MAXD][MAXB];

static int row_ok(int i) {
    for (int t = 0; t < d; t++)
        for (int s = 0; s < t; s++)
            if (sig[t][i] == sig[s][i] && vol[t][i] == vol[s][i]) return 0;
    return 1;
}

static void prep(void) {
    for (int t = 0; t < d; t++)
        for (int i = 0; i < B; i++) {
            isig[t][sig[t][i]] = i;
            vinv[t][i] = INVT[vol[t][i]];
        }
}

static int init_state(void) {
    for (int t = 0; t < d; t++) {
        int p[MAXB];
        for (int i = 0; i < B; i++) p[i] = i;
        for (int i = B - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < B; i++) {
            sig[t][i] = p[i];
            vol[t][i] = rndint(N);
        }
    }
    for (int i = 0; i < B; i++) {
        long tries = 0;
        while (!row_ok(i)) {
            if (++tries > 200000) return 0;
            int t = rndint(d);
            vol[t][i] = rndint(N);
        }
    }
    prep();
    return 1;
}

/* ------------------------------------------------------------ BFS cost */

static int vis[MAXV], qu[MAXV];
static int stamp_ = 0;

/* Number of vertices within distance D of source s. */
static int reach_count(int s) {
    int BN = B * N;
    stamp_++;
    int head = 0, tail = 0;
    qu[tail++] = s;
    vis[s] = stamp_;
    for (int lvl = 0; lvl < D; lvl++) {
        int end = tail;
        if (head == end) break;
        while (head < end) {
            int v = qu[head++];
            if (v < BN) {
                int i = v / N, x = v - i * N;
                for (int t = 0; t < d; t++) {
                    int j = sig[t][i];
                    int y = MT[x * N + vol[t][i]];
                    int u = BN + j * N + y;
                    if (vis[u] != stamp_) { vis[u] = stamp_; qu[tail++] = u; }
                }
            } else {
                int w = v - BN, j = w / N, y = w - j * N;
                for (int t = 0; t < d; t++) {
                    int i = isig[t][j];
                    int x = MT[y * N + vinv[t][i]];
                    int u = i * N + x;
                    if (vis[u] != stamp_) { vis[u] = stamp_; qu[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* G acts regularly on each orbit, so checking the 2B identity sources suffices. */
static long cover_cost(void) {
    int V = 2 * B * N;
    long c = 0;
    for (int i = 0; i < B; i++) c += V - reach_count(i * N);
    for (int j = 0; j < B; j++) c += V - reach_count(B * N + j * N);
    return c;
}

/* ------------------------------------------------------------ best store */

static int saved = 0;
static int sbM, sbK, sbR, sbB, sbN;
static int ssig[MAXD][MAXB], svol[MAXD][MAXB];

static void save_state(void) {
    if (2 * B * N <= saved) return;
    saved = 2 * B * N;
    sbM = GM; sbK = GK; sbR = GR; sbB = B; sbN = N;
    memcpy(ssig, sig, sizeof sig);
    memcpy(svol, vol, sizeof vol);
}

/* Simulated annealing over random metacyclic groups of order Nv with Bv base
 * vertices. Returns 1 when a diameter-<=D lift is found before 'until'. */
static int search_block(int Nv, int Bv, double until) {
    if (ccount[Nv] <= 0) return 0;
    while (now() < until) {
        Cand c = cand[cstart[Nv] + rndint(ccount[Nv])];
        build_group(c.m, c.k, c.r);
        B = Bv;
        N = Nv;
        if (!init_state()) continue;
        long cost = cover_cost();
        if (cost == 0) { save_state(); return 1; }
        double Ts = 0.05 * (double)cost + 1.0, Te = 0.3;
        const int iters = 6000;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) break;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            if (B == 1 || rndint(2) == 0) {
                int t = rndint(d), i = rndint(B);
                int old = vol[t][i];
                int nv = rndint(N);
                if (nv == old) continue;
                vol[t][i] = nv;
                if (!row_ok(i)) { vol[t][i] = old; continue; }
                prep();
                long c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    vol[t][i] = old;
                    prep();
                }
            } else {
                int t = rndint(d), i1 = rndint(B), i2 = rndint(B);
                if (i1 == i2) continue;
                int tmp = sig[t][i1]; sig[t][i1] = sig[t][i2]; sig[t][i2] = tmp;
                if (!row_ok(i1) || !row_ok(i2)) {
                    tmp = sig[t][i1]; sig[t][i1] = sig[t][i2]; sig[t][i2] = tmp;
                    continue;
                }
                prep();
                long c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    tmp = sig[t][i1]; sig[t][i1] = sig[t][i2]; sig[t][i2] = tmp;
                    prep();
                }
            }
        }
        if (cost == 0) { save_state(); return 1; }
    }
    return 0;
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int best_n = atoi(argv[5]);
    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (best_n < 0) best_n = 0;

    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    enumerate_groups();

    double moore = 0.0, pw = 1.0;
    for (int i = 0; i < D; i++) { moore += pw; pw *= (d - 1); }
    moore *= 2.0;

    /* Base sizes B = 1..4, each with a share of the remaining time. */
    int order[4] = {1, 2, 3, 4};
    double frac[4] = {0.25, 0.35, 0.25, 0.15};
    for (int oi = 0; oi < 4; oi++) {
        int Bv = order[oi];
        double remain = t_end - now();
        if (remain <= 0.5) break;
        double fsum = 0.0;
        for (int oj = oi; oj < 4; oj++) fsum += frac[oj];
        double tend = now() + remain * frac[oi] / fsum;

        int lo = best_n / (2 * Bv) + 1;
        if (lo < d) lo = d;
        int hi = (int)(moore / (2.0 * Bv));
        if (hi > MAXN) hi = MAXN;
        if (lo > hi) continue;

        int a = lo, b = hi;
        while (a <= b && now() < tend) {
            int mid = a + (b - a) / 2;
            int span = b - a + 1, probes = 1;
            while (span > 1) { span = (span + 1) / 2; probes++; }
            double rem = tend - now();
            double slice = rem / (probes + 1);
            if (slice < 0.5) slice = 0.5;
            if (slice > rem) slice = rem;
            if (search_block(mid, Bv, now() + slice)) {
                if (2 * Bv * mid > best_n) best_n = 2 * Bv * mid;
                a = mid + 1;
            } else {
                b = mid - 1;
            }
        }
    }

    if (saved == 0) {
        printf("0 0\n");
        return 0;
    }
    build_group(sbM, sbK, sbR);
    B = sbB;
    N = sbN;
    memcpy(sig, ssig, sizeof sig);
    memcpy(vol, svol, sizeof vol);
    prep();
    if (cover_cost() != 0) {
        printf("0 0\n");
        return 0;
    }
    int BN = B * N;
    printf("%d %d\n", 2 * BN, BN * d);
    for (int i = 0; i < B; i++)
        for (int x = 0; x < N; x++)
            for (int t = 0; t < d; t++) {
                int j = sig[t][i];
                int y = MT[x * N + vol[t][i]];
                printf("%d %d\n", i * N + x, BN + j * N + y);
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

    # Multi-orbit metacyclic voltage lifts; the C search only aims above best[0].
    if d >= 2 and D >= 3:
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        if budget > 2.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), int(best[0])],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass  # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
