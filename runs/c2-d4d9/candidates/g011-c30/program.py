"""Program: voltage lifts over metacyclic groups with multi-vertex base graphs.

Construction (new in this version):
  * Base graph: P A-vertices and P B-vertices (P = 1..6), with d darts. Dart k joins A_u
    to B_{sig_k(u)}, where each sig_k is a permutation, so every base vertex has degree d.
  * Voltages: dart (u,k) has a voltage volt[u*d+k] in G. The lift has vertices (X, g),
    g in G, and joins (A_u, g) to (B_v, g*a). Its order is 2*P*|G|.
  * Left multiplication by h in G is an automorphism. So the diameter is <= D iff BFS
    from (A_u, e) and (B_v, e) for every base index reaches all vertices within D steps.
  * Groups: metacyclic Z_m x|_r Z_k (including abelian and cyclic cases).
  * Search: hill climbing over voltages and base permutations, minimising the number of
    unreached (source, target) pairs. Simplicity is kept by requiring distinct voltages on
    darts that share an endpoint pair.
  * Candidates: all (P, |G|) pairs whose order is at least the current floor. They are
    tried lowest order first, with slices that double after each unsuccessful pass.
    After each success the candidate list is rebuilt above the new best.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with
lib.is_valid and keeps the best valid graph, falling back to the known start or K_{d,d}.
Calibration cases at the Moore bound return immediately.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 8
#define MAXP 8
#define PMAX 6
#define MAXNG 3000
#define MAXV (2 * MAXP * MAXNG)
#define MAXCAND 32
#define MAXOPT 12
#define NPER 2
#define STALL 5000

typedef struct { int m, k, r; } Opt;
typedef struct { int p, m, k, r, N, V; } Cand;

static int d, D;
static long moore;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
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

/* ------------------------------------------------------------ group Z_m x|_r Z_k */

static int N = 0, P = 0;
static uint16_t *T = NULL;     /* T[x*N+y] = x*y */
static int *INV = NULL;        /* INV[x] = x^{-1} */
static int pw[MAXNG + 1];

/* element (a,b) coded as a*k+b; (a,b)(c,d) = (a + r^b c, b + d); identity is index 0 */
static void build_group(int m, int k, int r) {
    N = m * k;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    free(T);
    free(INV);
    T = malloc(sizeof(uint16_t) * (size_t)N * (size_t)N);
    INV = malloc(sizeof(int) * (size_t)N);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, dd = y % k;
            int aa = (int)((a + (long)pw[b] * c) % m);
            int bb = (b + dd) % k;
            T[(size_t)x * N + y] = (uint16_t)(aa * k + bb);
        }
        int nb = (k - b) % k;
        int ia = (int)((m - ((long)pw[nb] * a) % m) % m);
        INV[x] = ia * k + nb;
    }
}

/* Options for a group of order n: nonabelian first, then abelian, then cyclic. */
static int g_nnon = 0;
static int find_opts(int n, Opt *o, int maxo) {
    int cnt = 0;
    for (int k = 2; k <= n / 3 && cnt < maxo; k++) {
        if (n % k) continue;
        int m = n / k;
        for (int r = 2; r < m && cnt < maxo; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            o[cnt].m = m;
            o[cnt].k = k;
            o[cnt].r = r;
            cnt++;
        }
    }
    g_nnon = cnt;
    for (int k = 2; k <= n / 3 && cnt < maxo; k++) {
        if (n % k) continue;
        o[cnt].m = n / k;
        o[cnt].k = k;
        o[cnt].r = 1;
        cnt++;
    }
    if (cnt < maxo && n >= 3) {
        o[cnt].m = n;
        o[cnt].k = 1;
        o[cnt].r = 1;
        cnt++;
    }
    return cnt;
}

/* ------------------------------------------------------------ lift configuration */

static int sig[MAXD][MAXP];    /* sig[k][u] = B-vertex joined to A_u by dart k */
static int sinv[MAXD][MAXP];   /* sinv[k][v] = A-vertex joined to B_v by dart k */
static int volt[MAXP * MAXD];  /* volt[u*d+k] */

static void recompute_sinv(void) {
    for (int k = 0; k < d; k++)
        for (int u = 0; u < P; u++) sinv[k][sig[k][u]] = u;
}

static void swap_sig(int k, int u1, int u2) {
    int t = sig[k][u1];
    sig[k][u1] = sig[k][u2];
    sig[k][u2] = t;
    sinv[k][sig[k][u1]] = u1;
    sinv[k][sig[k][u2]] = u2;
}

/* No two darts from the same A-vertex may hit the same B-vertex with the same voltage. */
static int simple_ok(void) {
    for (int u = 0; u < P; u++)
        for (int k = 0; k < d; k++)
            for (int k2 = k + 1; k2 < d; k2++)
                if (sig[k][u] == sig[k2][u] && volt[u * d + k] == volt[u * d + k2]) return 0;
    return 1;
}

static int init_config(void) {
    for (int k = 0; k < d; k++)
        for (int u = 0; u < P; u++) sig[k][u] = u;
    for (int k = 1; k < d; k++)
        for (int u = P - 1; u > 0; u--) {
            int j = rndint(u + 1);
            int t = sig[k][u];
            sig[k][u] = sig[k][j];
            sig[k][j] = t;
        }
    for (int tries = 0; tries < 100000; tries++) {
        for (int u = 0; u < P; u++)
            for (int k = 0; k < d; k++) volt[u * d + k] = rndint(N);
        if (simple_ok()) {
            recompute_sinv();
            return 1;
        }
    }
    return 0;
}

/* ------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

static int ball(int src) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int head = 0, tail = 0, PN = P * N;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int x = qv[head];
            if (x < PN) {
                int u = x / N, g = x - u * N;
                for (int k = 0; k < d; k++) {
                    int v = sig[k][u];
                    int y = PN + v * N + T[(size_t)g * N + volt[u * d + k]];
                    if (stamp[y] != tick) { stamp[y] = tick; qv[tail++] = y; }
                }
            } else {
                int yy = x - PN, v = yy / N, h = yy - v * N;
                for (int k = 0; k < d; k++) {
                    int u = sinv[k][v];
                    int z = u * N + T[(size_t)h * N + INV[volt[u * d + k]]];
                    if (stamp[z] != tick) { stamp[z] = tick; qv[tail++] = z; }
                }
            }
        }
    }
    return tail;
}

/* Sources: A_u at identity and B_v at identity. Left multiplication is an automorphism. */
static long cost_all(void) {
    long V = 2L * P * N, c = 0;
    for (int u = 0; u < P; u++) c += V - ball(u * N);
    for (int v = 0; v < P; v++) c += V - ball(P * N + v * N);
    return c;
}

/* ------------------------------------------------------------ hill climb */

static int climb(double until) {
    if (!init_config()) return 0;
    long cur = cost_all(), best = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        if (stall > STALL) {
            if (!init_config()) return 0;
            cur = cost_all();
            best = cur;
            stall = 0;
            continue;
        }
        if (P > 1 && rnd01() < 0.08) {
            int k = 1 + rndint(d - 1);
            int u1 = rndint(P), u2 = rndint(P);
            if (u1 == u2) { stall++; continue; }
            swap_sig(k, u1, u2);
            if (!simple_ok()) {
                swap_sig(k, u1, u2);
                stall++;
                continue;
            }
            long nc = cost_all();
            if (nc <= cur || rnd01() < 0.01) cur = nc;
            else swap_sig(k, u1, u2);
        } else {
            int u = rndint(P), k = rndint(d), idx = u * d + k;
            int old = volt[idx], nv = rndint(N);
            if (nv == old) { stall++; continue; }
            volt[idx] = nv;
            if (!simple_ok()) {
                volt[idx] = old;
                stall++;
                continue;
            }
            long nc = cost_all();
            if (nc <= cur || rnd01() < 0.01) cur = nc;
            else volt[idx] = old;
        }
        if (cur < best) { best = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

/* ------------------------------------------------------------ candidates */

static Cand cands[MAXCAND];
static int ncand = 0;

static void apply_cand(const Cand *c) {
    P = c->p;
    build_group(c->m, c->k, c->r);
}

static void gen_cands(long bestV) {
    ncand = 0;
    for (int p = 1; p <= PMAX; p++) {
        long N0 = bestV / (2L * p) + 1;
        int got = 0;
        for (long Nv = N0; got < NPER && Nv <= MAXNG && 2L * p * Nv <= moore; Nv++) {
            Opt o[MAXOPT];
            int no = find_opts((int)Nv, o, MAXOPT);
            int nn = g_nnon;
            if (no == 0) continue;
            int take = (p == 1) ? 2 : 1;
            if (take > no) take = no;
            int off = nn > 0 ? rndint(nn) : 0;
            for (int j = 0; j < take && ncand < MAXCAND; j++) {
                int idx = (j < nn && nn > 0) ? (off + j) % nn : j;
                Cand c;
                c.p = p;
                c.m = o[idx].m;
                c.k = o[idx].k;
                c.r = o[idx].r;
                c.N = (int)Nv;
                c.V = 2 * p * (int)Nv;
                cands[ncand++] = c;
            }
            got++;
        }
    }
    for (int i = 1; i < ncand; i++) {
        Cand c = cands[i];
        int j = i - 1;
        while (j >= 0 && (cands[j].V > c.V || (cands[j].V == c.V && cands[j].p > c.p))) {
            cands[j + 1] = cands[j];
            j--;
        }
        cands[j + 1] = c;
    }
}

/* ------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static Cand bestc;
static int bsig[MAXD][MAXP];
static int bvolt[MAXP * MAXD];
static int have = 0;

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [floor_vertices]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long floorV = argc > 5 ? atol(argv[5]) : 0;

    double t0 = now();
    double usable = limit - 1.5;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD || D < 2) { print_complete(); return 0; }

    moore = moore_bound();
    long bestV = 2L * d - 1;
    if (floorV - 1 > bestV) bestV = floorV - 1;

    double s0 = usable * 0.008;
    if (s0 < 0.1) s0 = 0.1;
    double slice = s0;

    while (bestV < moore && now() < t_end - 0.3) {
        gen_cands(bestV);
        if (ncand == 0) break;
        int improved = 0;
        for (int i = 0; i < ncand; i++) {
            double rem = t_end - now();
            if (rem < 0.2) break;
            double sl = slice < rem ? slice : rem;
            apply_cand(&cands[i]);
            if (climb(now() + sl)) {
                bestc = cands[i];
                bestV = (long)2 * P * N;
                have = 1;
                memcpy(bsig, sig, sizeof sig);
                memcpy(bvolt, volt, sizeof volt);
                improved = 1;
                break;
            }
        }
        if (!improved) slice *= 2.0;
    }

    if (!have) { print_complete(); return 0; }

    P = bestc.p;
    build_group(bestc.m, bestc.k, bestc.r);
    memcpy(sig, bsig, sizeof sig);
    memcpy(volt, bvolt, sizeof volt);
    recompute_sinv();
    if (cost_all() != 0) { print_complete(); return 0; }

    int V = 2 * P * N;
    printf("%d %d\n", V, P * N * d);
    for (int u = 0; u < P; u++)
        for (int g = 0; g < N; g++)
            for (int k = 0; k < d; k++) {
                int v = sig[k][u];
                int y = P * N + v * N + T[(size_t)g * N + volt[u * d + k]];
                printf("%d %d\n", u * N + g, y);
            }
    return 0;
}
'''

REF_VERTICES = {(4, 9): 4970}


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
    if start is None or not lib.is_valid(start[0], start[1], d, D):
        start = lib.haar_graph(d, range(d))   # K_{d,d}: always valid for D >= 2
    best = start
    if best[0] >= lib.moore_bound(d, D) or d < 3 or d > 8 or D < 2:
        return best   # Moore graph or outside the engine's range: nothing to search
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget > 1.0:
        floor = REF_VERTICES.get((d, D), best[0])
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), floor],
                             timeout=budget + 8)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
