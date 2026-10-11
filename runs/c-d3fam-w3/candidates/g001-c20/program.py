"""Haar-graph covering search for D = 3 (bold replacement of the lift/grow search).

Construction: for a group G of order N and a connection set S of size d containing the identity,
the bipartite Haar graph has vertices a_g, b_h (g, h in G) and edges a_g -- b_{g s} for s in S.
It has diameter <= 3 exactly when S S^{-1} = G and S^{-1} S = G. That gives order 2N with degree d,
so the goal is the largest N with a covering set S. Groups are metacyclic, Z_m x|_r Z_k, which
includes all abelian groups of order N (r = 1). A C annealer searches for S. The Python side keeps
the best known construction (Araujo-Pardo & Lopez or PG(2,q)) and only accepts a C result that is
strictly larger and passes lib.is_valid.
"""
import itertools
import time

import lib

GQ_Q_MAX = 9      # largest q for which the generalized quadrangle W(q) is built in Python
TIME_FRAC = 0.93  # fraction of time_limit available to the C run (C stops at 96% of its budget)

C_SOURCE = r'''
/* Haar-graph covering search for bipartite diameter-3 graphs.
 *
 * Usage:  prog d D seed time_limit Nmin
 * stdout: "V m" then m edge lines, or "0 0" if nothing beats Nmin.
 *
 * For a metacyclic group G of order N and S (|S| = d, identity in S), the Haar graph has
 * a_g -- b_{g s}. Diameter <= 3 iff S S^{-1} = G and S^{-1} S = G. Simulated annealing swaps
 * elements of S to maximise the number of covered group elements (target 2N). N is tried from
 * the largest candidate down, with a short quick scan first and then longer runs above the best.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 512
#define MAXD 64
#define MAXV (2 * MAXN)

static int d, D;
static double t_deadline;

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

/* ------------------------------------------------------------ group Z_m x|_r Z_k */

/* Element (a, b) is the integer a*k + b; identity is 0. */
static int GN;
static int MUL[MAXN * MAXN];
static int INV[MAXN];

static void build_group(int m, int k, int r) {
    int N = m * k;
    static int rp[MAXN];
    GN = N;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            MUL[x * N + y] = (int)(((a + (long)rp[b] * c) % m) * k + (b + e) % k);
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MUL[x * N + y] == 0) { INV[x] = y; break; }
}

/* Random admissible (m, k, r) with m*k = N, gcd(r, m) = 1 and r^k = 1 mod m. Cyclic as fallback. */
static void pick_spec(int N, int *m_out, int *k_out, int *r_out) {
    int divs[MAXN], nd = 0;
    for (int m = 1; m <= N; m++) if (N % m == 0) divs[nd++] = m;
    for (int tries = 0; tries < 40; tries++) {
        int m = divs[rndint(nd)];
        int k = N / m;
        if (m == 1) { *m_out = 1; *k_out = k; *r_out = 0; return; }
        for (int t2 = 0; t2 < 100; t2++) {
            int r = 1 + rndint(m - 1);
            if (gcd(r, m) == 1 && powmod(r, k, m) == 1 % m) {
                *m_out = m; *k_out = k; *r_out = r; return;
            }
        }
    }
    *m_out = 1; *k_out = N; *r_out = 0;
}

/* ------------------------------------------------------------ covering state */

static int S[MAXD];
static int inS[MAXN];
static int cnt1[MAXN], cnt2[MAXN];
static int covered;   /* number of covered elements of S S^{-1} plus those of S^{-1} S */

static void inc1(int g) { if (cnt1[g]++ == 0) covered++; }
static void dec1(int g) { if (--cnt1[g] == 0) covered--; }
static void inc2(int g) { if (cnt2[g]++ == 0) covered++; }
static void dec2(int g) { if (--cnt2[g] == 0) covered--; }
static int mul(int x, int y) { return MUL[x * GN + y]; }

static void recount(void) {
    memset(cnt1, 0, sizeof(int) * GN);
    memset(cnt2, 0, sizeof(int) * GN);
    covered = 0;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) {
            inc1(mul(S[i], INV[S[j]]));
            inc2(mul(INV[S[i]], S[j]));
        }
}

/* Remove S[i]'s ordered pairs with all other elements (S[i] stays in place). */
static void remove_elem(int i) {
    int x = S[i], ix = INV[x];
    for (int j = 0; j < d; j++) {
        if (j == i) continue;
        int y = S[j], iy = INV[y];
        dec1(mul(x, iy)); dec1(mul(y, ix));
        dec2(mul(ix, y)); dec2(mul(iy, x));
    }
    dec1(0); dec2(0);
}

/* Set S[i] = y and add its ordered pairs. */
static void add_elem(int i, int y) {
    int iy = INV[y];
    for (int j = 0; j < d; j++) {
        if (j == i) continue;
        int z = S[j], iz = INV[z];
        inc1(mul(y, iz)); inc1(mul(z, iy));
        inc2(mul(iy, z)); inc2(mul(iz, y));
    }
    inc1(0); inc2(0);
    S[i] = y;
}

/* ------------------------------------------------------------ search */

static int bm, bk, br, bS[MAXD];

/* Anneal for a covering S of a random admissible group of order N. Returns 1 on success
 * (globals bm, bk, br, bS hold the result), 0 on timeout. */
static int try_N(int N, double until) {
    if (N <= d) return 0;
    int m, k, r;
    const long cyc = 200000;
    while (now() < until) {
        pick_spec(N, &m, &k, &r);
        build_group(m, k, r);
        memset(inS, 0, sizeof(int) * N);
        S[0] = 0;
        inS[0] = 1;
        for (int i = 1; i < d; i++) {
            int y;
            do { y = 1 + rndint(N - 1); } while (inS[y]);
            S[i] = y;
            inS[y] = 1;
        }
        recount();
        for (long rd = 0; rd < 10; rd++) {
            for (long it = 0; it < cyc; it++) {
                if (covered == 2 * N) {
                    bm = m; bk = k; br = r;
                    memcpy(bS, S, sizeof(int) * d);
                    return 1;
                }
                if ((it & 4095) == 0 && now() > until) return 0;
                double T = exp(-2.1 * (double)it / (double)cyc);
                int i = 1 + rndint(d - 1);
                int y;
                do { y = 1 + rndint(N - 1); } while (inS[y]);
                int x = S[i];
                int old = covered;
                remove_elem(i);
                add_elem(i, y);
                int delta = covered - old;
                if (delta >= 0 || rnd01() < exp(delta / T)) {
                    inS[x] = 0;
                    inS[y] = 1;
                } else {
                    remove_elem(i);
                    add_elem(i, x);
                }
            }
        }
    }
    return 0;
}

/* Verify diameter <= D of the Haar graph and print it. Returns 0 (printing nothing) on failure. */
static int verify_print(int N, int m, int k, int r, const int *Sx) {
    static int adj[MAXV][MAXD];
    static int deg[MAXV], dist[MAXV], q[MAXV];
    int V = 2 * N;
    build_group(m, k, r);
    for (int g = 0; g < N; g++) {
        deg[g] = d;
        deg[N + g] = d;
        for (int j = 0; j < d; j++) {
            adj[g][j] = N + mul(g, Sx[j]);
            adj[N + g][j] = mul(g, INV[Sx[j]]);
        }
    }
    for (int src = 0; src < V; src++) {
        for (int v = 0; v < V; v++) dist[v] = -1;
        int head = 0, tail = 0;
        dist[src] = 0;
        q[tail++] = src;
        while (head < tail) {
            int v = q[head++];
            if (dist[v] >= D) continue;
            for (int j = 0; j < deg[v]; j++) {
                int u = adj[v][j];
                if (dist[u] < 0) { dist[u] = dist[v] + 1; q[tail++] = u; }
            }
        }
        if (tail != V) return 0;
    }
    printf("%d %d\n", V, N * d);
    for (int g = 0; g < N; g++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", g, N + mul(g, Sx[j]));
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit Nmin\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int Nmin = atoi(argv[5]);
    double t0 = now();
    t_deadline = t0 + limit * 0.96;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (D != 3 || d < 3 || d > MAXD) { printf("0 0\n"); return 0; }
    long Nmax_l = (long)d * (d - 1) + 1;          /* Moore-type bound on N for D = 3 */
    int Nmax = Nmax_l > MAXN ? MAXN : (int)Nmax_l;
    if (Nmin < d + 1) Nmin = d + 1;
    if (Nmin > Nmax) { printf("0 0\n"); return 0; }

    int bestN = 0;
    int count = Nmax - Nmin + 1;

    /* Phase A: quick descending scan. The first N that succeeds is the largest found so far. */
    double slice = 0.5 * (t_deadline - now()) / count;
    if (slice < 0.2) slice = 0.2;
    for (int N = Nmax; N >= Nmin && bestN == 0; N--) {
        if (now() >= t_deadline) break;
        double until = now() + slice;
        if (until > t_deadline) until = t_deadline;
        if (try_N(N, until)) bestN = N;
    }

    /* Phase B: spend the rest of the time on the orders above the best found. */
    while (now() < t_deadline && bestN < Nmax) {
        int lo = bestN ? bestN + 1 : Nmin;
        int hi = Nmax;
        int cntB = hi - lo + 1;
        double remaining = t_deadline - now();
        double s2 = remaining / (2.0 * cntB);
        if (s2 < 0.2) s2 = 0.2;
        int found = 0;
        for (int N = hi; N >= lo && !found; N--) {
            if (now() >= t_deadline) break;
            double until = now() + s2;
            if (until > t_deadline) until = t_deadline;
            if (try_N(N, until)) { bestN = N; found = 1; }
        }
    }

    if (bestN == 0 || !verify_print(bestN, bm, bk, br, bS))
        printf("0 0\n");
    return 0;
}
'''


# ---------------------------------------------------------------- helpers

def _gq_w(q):
    """Point-line incidence graph of the generalized quadrangle W(q): degree q+1, diameter 4."""
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
    """W(q) for the largest prime power q <= min(d-1, GQ_Q_MAX)."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def known_start(d, D):
    """Best known construction for (d, D) that Python can build directly, or None."""
    if D == 3:
        if lib.is_prime_power(d - 1):
            return lib.projective_plane_incidence(d - 1)     # Moore graph
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            return lib.araujo_lopez_graph(d - 2)             # record 2(q^2+q+5), q = d-2
        return _pg_base(d)                                   # fallback: PG(2,q), q < d-1
    if D >= 4:
        return _best_gq(d)                                   # diameter 4 <= D
    return None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    kdd = lib.haar_graph(d, range(d))          # K_{d,d}: diameter 2, always valid
    if D == 2:
        return kdd

    best = None
    try:
        best = known_start(d, D)
    except Exception:
        best = None
    if best is None or not lib.is_valid(best[0], best[1], d, D):
        best = kdd

    if best[0] >= lib.moore_bound(d, D):
        return best                            # Moore graph: nothing to search for

    if D != 3 or d < 3:
        return best                            # the covering search is specific to D = 3

    # Leave a 1 s margin for process start, compile, parsing and validation. C stops itself at
    # 96% of its budget, so the subprocess timeout is only a backstop.
    budget = TIME_FRAC * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 1.0:
        return best

    # Only orders above the parent's half-size can improve it: Haar order is 2N.
    nmin = best[0] // 2 + 1
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), nmin],
                         stdin_graph=None, timeout=budget + 3)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass                                   # keep the valid construction
    return best
