"""Program: metacyclic voltage lifts with base size 1-3, searched by simulated annealing.

Construction (new in this version, replacing the PSL/SL(2,q) bi-Cayley search):
  * Group G = Z_m semidirect Z_k (element (a,b), product (a,b)(c,e) = (a + r^b c, b + e),
    requires r^k = 1 mod m). Orders are not limited to the PSL/SL(2,q) orders.
  * Base graph: p A-vertices and p B-vertices, d permutations sigma_1..sigma_d of
    {0..p-1} and voltages g_{i,k} in G. The lift has vertices A_{i,x}, B_{j,y} and
    edges A_{i,x} -- B_{sigma_k(i), x*g_{i,k}}. It is d-regular and bipartite with 2pN vertices.
  * Left multiplication is an automorphism, so the diameter is <= D iff BFS from
    A_{i,e} (i < p) and B_{j,e} (j < p) reaches all 2pN vertices within D steps.
  * The C engine samples a random group and base size with order just above the
    current best, anneals the voltages and permutations to zero unreached pairs, and
    climbs the order ladder after each success.

Safety: the C engine prints K_{d,d} if it finds nothing better. Python checks the
result with lib.is_valid and keeps the best valid graph, falling back to the known
start or K_{d,d}.
"""
import time

import lib

C_SOURCE = r'''
/* Metacyclic voltage-lift search.
 * Usage:  prog d D seed time_limit        (stdin is ignored)
 * Output: "n m" then m lines "u v": a bipartite d-regular graph of diameter <= D
 *         (K_{d,d} if nothing better was found).
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 12200
#define MAXP 3
#define MAXDEG 8
#define MAXV (2 * MAXP * MAXN)
#define MAXRS (MAXP * MAXDEG * MAXN)
#define STALL 30000

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

/* Largest possible order of a bipartite graph with max degree d and diameter D. */
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

/* ------------------------------------------------------------------ group */

static int mg, kg, rg, N, PB;
static int pw[MAXN];   /* pw[b] = r^b mod m */

static void set_group(int m, int k, int r) {
    mg = m; kg = k; rg = r; N = m * k;
    long v = 1 % m;
    for (int b = 0; b < k; b++) {
        pw[b] = (int)v;
        v = (v * r) % m;
    }
}

/* Element x = a*kg + b stands for (a, b); identity is 0. */
static int mulg(int x, int y) {
    int a = x / kg, b = x - a * kg;
    int c = y / kg, e = y - c * kg;
    int ra = (a + (pw[b] * c) % mg) % mg;
    int rb = b + e;
    if (rb >= kg) rb -= kg;
    return ra * kg + rb;
}

static int invg(int x) {
    int a = x / kg, b = x - a * kg;
    int nb = (kg - b) % kg;
    int ia = (mg - (pw[nb] * a) % mg) % mg;
    return ia * kg + nb;
}

/* ------------------------------------------------------------------ lift state */

static int sig[MAXDEG][MAXP], sinv[MAXDEG][MAXP], gv[MAXP][MAXDEG];
static int bsig[MAXDEG][MAXP], bg[MAXP][MAXDEG];
static int Rr[MAXRS], Ri[MAXRS];   /* index (i*d + k)*N + x */
static int stamp[MAXV], qv[MAXV];
static int tick = 0;

static void rebuild_dart(int i, int k) {
    int g = gv[i][k], gi = invg(g);
    int base = (i * d + k) * N;
    for (int x = 0; x < N; x++) {
        Rr[base + x] = mulg(x, g);
        Ri[base + x] = mulg(x, gi);
    }
}

/* Dart targets from one A-vertex must be distinct pairs (sigma, voltage). */
static int valid_vertex(int i) {
    for (int k1 = 0; k1 < d; k1++)
        for (int k2 = k1 + 1; k2 < d; k2++)
            if (sig[k1][i] == sig[k2][i] && gv[i][k1] == gv[i][k2]) return 0;
    return 1;
}

static int init_state(void) {
    for (int k = 0; k < d; k++) {
        for (int i = 0; i < PB; i++) sig[k][i] = i;
        for (int i = PB - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = sig[k][i]; sig[k][i] = sig[k][j]; sig[k][j] = t;
        }
        for (int i = 0; i < PB; i++) sinv[k][sig[k][i]] = i;
    }
    int tries = 0;
    for (;;) {
        if (++tries > 5000) return 0;
        for (int i = 0; i < PB; i++)
            for (int k = 0; k < d; k++) gv[i][k] = rndint(N);
        int ok = 1;
        for (int i = 0; i < PB && ok; i++) ok = valid_vertex(i);
        if (ok) break;
    }
    for (int i = 0; i < PB; i++)
        for (int k = 0; k < d; k++) rebuild_dart(i, k);
    return 1;
}

/* ------------------------------------------------------------------ cost */

/* Visited count within dmax steps from src (vertex ids: A_{i,x} = i*N+x, B_{j,y} = PB*N + j*N+y). */
static int ball(int src, int dmax) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int pn = PB * N;
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < pn) {
                int i = v / N, x = v - i * N;
                for (int k = 0; k < d; k++) {
                    int j = sig[k][i];
                    int u = pn + j * N + Rr[(i * d + k) * N + x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - pn, j = w / N, y = w - j * N;
                for (int k = 0; k < d; k++) {
                    int i = sinv[k][j];
                    int u = i * N + Ri[(i * d + k) * N + y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached (source, vertex) pairs over the 2*PB orbit representatives; 0 means diameter <= D. */
static long cost_now(void) {
    int V = 2 * PB * N, pn = PB * N;
    long c = 0;
    for (int i = 0; i < PB; i++) c += (long)(V - ball(i * N, D));
    for (int j = 0; j < PB; j++) c += (long)(V - ball(pn + j * N, D));
    return c;
}

static int accept(long delta, long cur) {
    if (delta <= 0) return 1;
    double T = 0.3 + 0.01 * (double)cur;
    return rnd01() < exp(-(double)delta / T);
}

/* Simulated annealing on voltages and permutations. Returns 1 if cost 0 reached. */
static int anneal(double until) {
    if (!init_state()) return 0;
    long cur = cost_now(), best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        if (stall > STALL) {
            if (!init_state()) return 0;
            cur = cost_now();
            best_c = cur;
            stall = 0;
            continue;
        }
        if (PB >= 2 && rnd01() < 0.35) {
            int k = rndint(d), i1 = rndint(PB), i2 = rndint(PB - 1);
            if (i2 >= i1) i2++;
            int j1 = sig[k][i1], j2 = sig[k][i2];
            sig[k][i1] = j2; sig[k][i2] = j1;
            sinv[k][j1] = i2; sinv[k][j2] = i1;
            int ok = valid_vertex(i1) && valid_vertex(i2);
            if (ok) {
                long nc = cost_now();
                if (accept(nc - cur, cur)) cur = nc;
                else ok = 0;
            }
            if (!ok) {
                sig[k][i1] = j1; sig[k][i2] = j2;
                sinv[k][j1] = i1; sinv[k][j2] = i2;
            }
        } else {
            int i = rndint(PB), k = rndint(d);
            int old = gv[i][k];
            int nw = rndint(N);
            if (nw != old) {
                gv[i][k] = nw;
                int ok = valid_vertex(i);
                if (ok) {
                    rebuild_dart(i, k);
                    long nc = cost_now();
                    if (accept(nc - cur, cur)) cur = nc;
                    else ok = 0;
                }
                if (!ok) {
                    gv[i][k] = old;
                    rebuild_dart(i, k);
                }
            }
        }
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

/* ------------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
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
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    long best_n = 2L * d;
    int have = 0, bm = 0, bk = 0, br = 0, bpb = 0;

    while (1) {
        double rem = t_end - now();
        if (rem < 0.4) break;
        long lo = best_n + 2;
        if (lo > moore) break;
        long hi = best_n + best_n / 5 + 32;
        if (hi > moore) hi = moore;
        if (hi > 2L * MAXP * MAXN) hi = 2L * MAXP * MAXN;

        int p = 1 + rndint(MAXP);
        long nlo = (lo + 2L * p - 1) / (2L * p);
        long nhi = hi / (2L * p);
        if (nhi > MAXN) nhi = MAXN;
        if (nlo > nhi) continue;
        int Nn = (int)(nlo + (long)rndint((int)(nhi - nlo + 1)));

        int divs[256], nd = 0;
        for (int t = 1; t * t <= Nn; t++) {
            if (Nn % t == 0) {
                divs[nd++] = t;
                if (t * t != Nn && nd < 256) divs[nd++] = Nn / t;
            }
        }
        int m = divs[rndint(nd)];
        int kk = Nn / m;
        int r = 1 % m;
        if (m >= 2 && kk >= 2 && rnd01() < 0.7) {
            for (int tr = 0; tr < 300; tr++) {
                int cand = 1 + rndint(m - 1);
                if (gcd_i(cand, m) == 1 && powmod(cand, kk, m) == 1 % m) {
                    r = cand;
                    break;
                }
            }
        }

        set_group(m, kk, r);
        PB = p;

        double slice = rem * 0.15;
        if (slice < 0.5) slice = 0.5;
        if (slice > 5.0) slice = 5.0;
        double until = now() + slice;
        if (until > t_end) until = t_end;

        if (anneal(until)) {
            best_n = 2L * PB * N;
            bm = mg; bk = kg; br = rg; bpb = PB;
            for (int k = 0; k < d; k++)
                for (int i = 0; i < PB; i++) bsig[k][i] = sig[k][i];
            for (int i = 0; i < PB; i++)
                for (int k = 0; k < d; k++) bg[i][k] = gv[i][k];
            have = 1;
        }
    }

    if (!have) {
        print_complete();
        return 0;
    }
    set_group(bm, bk, br);
    PB = bpb;
    int pn = PB * N;
    printf("%d %ld\n", 2 * pn, (long)pn * d);
    for (int i = 0; i < PB; i++)
        for (int x = 0; x < N; x++)
            for (int k = 0; k < d; k++)
                printf("%d %d\n", i * N + x, pn + bsig[k][i] * N + mulg(x, bg[i][k]));
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: always valid
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)], timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
