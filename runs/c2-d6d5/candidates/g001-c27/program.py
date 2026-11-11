"""Bi-Cayley (Haar-type) search: a different construction from the voltage-lift engine.

A graph on A = G x {0} and B = G x {1} for a finite group G of order N, with
edge (g,0)-(h,1) iff g^{-1} h is in a connection set S of size d. Left multiplication
is an automorphism that is transitive on A and on B, so every distance check reduces to
two breadth-first searches, from (e,0) and (e,1). The C engine anneals over S for groups
of order N = bestN + 1, climbing one order at a time. Every output graph is re-checked
in Python, and a valid fallback is always returned.
"""
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley diameter search over semidirect groups Z_m x|_r Z_k.
 * Usage: prog d D seed time_limit   (stdin is ignored)
 * Output: "n m" and edges of the largest valid bi-Cayley graph found, or K_{d,d}.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1200
#define MAXD 24

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
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000L) break;
    }
    return 2 * s;
}

/* ------------------------------------------------------------ group Z_m x| Z_k */

static int N, GM, GK, GR;
static int rp[MAXN];
static int MT[MAXN * MAXN];  /* MT[x*N+y] = x*y */
static int INV[MAXN];

/* Element (a,b) is a*k+b; (a,b)(c,e) = (a + r^b c mod m, b+e mod k). */
static void set_group(int m, int k, int r) {
    GM = m; GK = k; GR = r; N = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            MT[x * N + y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INV[x] = y; break; }
}

/* Uniform choice among all semidirect groups of order n (cyclic included). */
static int choose_group(int n, int *om, int *ok, int *orr) {
    long count = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        int rmax = m == 1 ? 1 : m;
        for (int r = 0; r < rmax; r++) {
            if (m > 1 && gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (!count) return 0;
    *om = bm; *ok = bk; *orr = br;
    return 1;
}

/* ------------------------------------------------------- connection-set search */

static int Sel[MAXD], Sinv[MAXD];
static unsigned char inS[MAXN];
static int dist[2 * MAXN], qu[2 * MAXN];

/* Vertices within distance D of src (A = 0..N-1, B = N..2N-1). */
static int reach_count(int src) {
    int n2 = 2 * N;
    for (int i = 0; i < n2; i++) dist[i] = -1;
    int head = 0, tail = 0;
    qu[tail++] = src;
    dist[src] = 0;
    while (head < tail) {
        int v = qu[head++];
        if (dist[v] >= D) continue;
        int nd = dist[v] + 1;
        if (v < N) {
            for (int j = 0; j < d; j++) {
                int w = N + MT[v * N + Sel[j]];
                if (dist[w] < 0) { dist[w] = nd; qu[tail++] = w; }
            }
        } else {
            int y = v - N;
            for (int j = 0; j < d; j++) {
                int w = MT[y * N + Sinv[j]];
                if (dist[w] < 0) { dist[w] = nd; qu[tail++] = w; }
            }
        }
    }
    return tail;
}

/* Number of unreached (distance > D) pairs from the two sources; 0 means valid. */
static int energy(void) {
    return (2 * N - reach_count(0)) + (2 * N - reach_count(N));
}

/* Simulated annealing over S (d distinct elements) for the current group. */
static int sa_attempt(long iters) {
    memset(inS, 0, (size_t)N);
    for (int j = 0; j < d; j++) {
        int s;
        do s = rndint(N); while (inS[s]);
        inS[s] = 1;
        Sel[j] = s;
        Sinv[j] = INV[s];
    }
    int E = energy();
    if (E == 0) return 1;
    double T = 1.0 + 0.05 * E;
    double fac = pow(0.02, 1.0 / (double)iters);
    for (long it = 0; it < iters; it++) {
        if ((it & 255) == 0 && now() > t_end) return 0;
        int j = rndint(d);
        int old = Sel[j], nw;
        do nw = rndint(N); while (inS[nw]);
        inS[old] = 0; inS[nw] = 1;
        Sel[j] = nw; Sinv[j] = INV[nw];
        int E2 = energy();
        if (E2 <= E || rnd01() < exp((double)(E - E2) / T)) {
            E = E2;
            if (E == 0) return 1;
        } else {
            inS[nw] = 0; inS[old] = 1;
            Sel[j] = old; Sinv[j] = INV[old];
        }
        T *= fac;
    }
    return 0;
}

/* ------------------------------------------------------------------ main */

static int bestn = 0, bm = 0, bk = 0, br = 0;
static int bestS[MAXD];

static void print_best(void) {
    if (bestn == 0) {  /* K_{d,d} */
        printf("%d %d\n", 2 * d, d * d);
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
        return;
    }
    set_group(bm, bk, br);
    printf("%d %d\n", 2 * N, N * d);
    for (int x = 0; x < N; x++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", x, N + MT[x * N + bestS[j]]);
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
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d >= 2 && d <= MAXD && D >= 2) {
        long moore = moore_bound();
        int target = d + 1;
        int fails = 0;
        while (now() < t_end) {
            if (2L * target > moore || target > MAXN) break;
            int m, k, r;
            if (!choose_group(target, &m, &k, &r)) break;
            set_group(m, k, r);
            long iters = 40000 + 4000L * (fails < 50 ? fails : 50);
            if (sa_attempt(iters)) {
                bestn = target;
                bm = m; bk = k; br = r;
                memcpy(bestS, Sel, sizeof(int) * (size_t)d);
                target = bestn + 1;
                fails = 0;
            } else {
                fails++;
            }
        }
    }
    print_best();
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def fallback(d, D):
    """Always-valid graph: K_{d,d} when D >= 2, a single edge when D = 1."""
    if D >= 2 and d >= 1:
        return lib.haar_graph(d, range(d))
    if d >= 1 and D >= 1:
        return (2, [(0, 1)])
    return (1, [])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else fallback(d, D)
    budget = 0.8 * time_limit - (time.monotonic() - t0) - 1.5
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.5 and D >= 2 and d >= 2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=None, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # a failing C run only costs the search; the valid best is kept
    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback(d, D)
    return best
