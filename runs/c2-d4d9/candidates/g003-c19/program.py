"""Program: voltage lifts of small bipartite base graphs over non-abelian groups.

Replaces the bi-Cayley search over PSL(2,q). New construction:
  * Base graph: A_0..A_{a-1}, B_0..B_{a-1}, with A_i joined to B_{i+T_t mod a} for
    t in 0..d-1, where T is a d-subset of Z_a (a >= d, so the base is simple).
  * Voltages: each base dart (i, t) carries g_{i,t} in G = Z_m x|_r Z_k (order N = m k).
    Lift: A_(i,x) ~ B_(i+T_t, x*g_{i,t}) for all x in G. The lift has 2aN vertices,
    is d-regular and bipartite, and has no multi-edges because the T_t are distinct.
  * Left multiplication by G is an automorphism, so the diameter is <= D iff BFS from
    each of the 2a base representatives (identity fibre) reaches everything within D.
  * Search: for each candidate order V = 2aN (ascending window, shuffled per pass),
    pick a random group, base offsets T and hill-climb voltages to minimise the count
    of unreached (source, vertex) pairs.

Safety: the C engine prints K_{d,d} if nothing is found. Python validates the result with
lib.is_valid and keeps the best valid graph (known start or K_{d,d}).
"""
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

#define MAXD 8
#define MAXA 16
#define MAXN 3000
#define MAXV (2 * MAXA * MAXN)
#define MAXC 6000

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
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* ------------------------------------------------------------ group Z_m x|_r Z_k */

static int gN, gm, gk, gr;
static int *mulT = NULL;
static int mulcap = 0;
static int invT[MAXN];
static int rp[MAXN];

/* Element x = a*k + b (a in Z_m, b in Z_k); (a,b)(c,d) = (a + r^b c, b + d). */
static int build_group(int m, int k, int r) {
    int N = m * k;
    if (N < 1 || N > MAXN) return 0;
    gN = N; gm = m; gk = k; gr = r;
    if (N * N > mulcap) {
        free(mulT);
        mulT = malloc(sizeof(int) * (size_t)N * (size_t)N);
        if (!mulT) { mulcap = 0; return 0; }
        mulcap = N * N;
    }
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, dd = y % k;
            int ma = (int)((a + (long)rp[b] * c) % m);
            int mb = (b + dd) % k;
            mulT[x * N + y] = ma * k + mb;
        }
    }
    for (int x = 0; x < N; x++) invT[x] = 0;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (mulT[x * N + y] == 0) invT[x] = y;
    return 1;
}

/* ------------------------------------------------------------ lift */

static int A;                    /* base vertices per side */
static int T[MAXD];              /* distinct offsets in Z_A */
static int volt[MAXA][MAXD];     /* voltages in G */
static int adj[MAXV * MAXD];
static int V;

static void rebuild_adj(void) {
    int aN = A * gN;
    V = 2 * aN;
    for (int i = 0; i < A; i++)
        for (int x = 0; x < gN; x++) {
            int v = i * gN + x;
            for (int t = 0; t < d; t++) {
                int j = (i + T[t]) % A;
                int y = mulT[x * gN + volt[i][t]];
                adj[v * d + t] = aN + j * gN + y;
            }
        }
    for (int j = 0; j < A; j++)
        for (int y = 0; y < gN; y++) {
            int v = aN + j * gN + y;
            for (int t = 0; t < d; t++) {
                int i = (j - T[t] + A) % A;
                int g = volt[i][t];
                int x = mulT[y * gN + invT[g]];
                adj[v * d + t] = i * gN + x;
            }
        }
}

static int stamp_arr[MAXV];
static int tick = 0;
static int bq[MAXV];

static int reach_count(int src) {
    if (++tick == 0x7fffffff) {
        memset(stamp_arr, 0, sizeof stamp_arr);
        tick = 1;
    }
    int head = 0, tail = 0;
    stamp_arr[src] = tick;
    bq[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            const int *nb = adj + bq[head] * d;
            for (int t = 0; t < d; t++) {
                int u = nb[t];
                if (stamp_arr[u] != tick) {
                    stamp_arr[u] = tick;
                    bq[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* Sum over base representatives of unreached vertices within D; 0 iff diameter <= D. */
static long cost_all(void) {
    long c = 0;
    int aN = A * gN;
    for (int i = 0; i < A; i++) c += (long)(V - reach_count(i * gN));
    for (int j = 0; j < A; j++) c += (long)(V - reach_count(aN + j * gN));
    return c;
}

static void random_volts(void) {
    for (int i = 0; i < A; i++)
        for (int t = 0; t < d; t++) volt[i][t] = rndint(gN);
}

#define STALL_MAX 4000

static int climb(double until) {
    random_volts();
    rebuild_adj();
    long cur = cost_all(), best = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        if (stall > STALL_MAX) {
            random_volts();
            rebuild_adj();
            cur = cost_all();
            best = cur;
            stall = 0;
            continue;
        }
        int i = rndint(A), t = rndint(d);
        int old = volt[i][t];
        int nv = rndint(gN);
        if (nv == old) continue;
        volt[i][t] = nv;
        rebuild_adj();
        long nc = cost_all();
        if (nc <= cur || rnd01() < 0.01) {
            cur = nc;
        } else {
            volt[i][t] = old;
            rebuild_adj();
        }
        if (cur < best) { best = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

/* ------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

typedef struct { int V, a, N; } Cand;
static Cand cands[MAXC];
static int nc = 0;

static void shuffle_cands(void) {
    for (int c = nc - 1; c > 0; c--) {
        int j = rndint(c + 1);
        Cand tmp = cands[c];
        cands[c] = cands[j];
        cands[j] = tmp;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [lo hi]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.95 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    long lo = 2L * d + 2, hi = moore;
    if (argc > 6) { lo = atol(argv[5]); hi = atol(argv[6]); }
    if (hi > moore) hi = moore;
    if (hi > MAXV) hi = MAXV;
    if (lo < 2 * d) lo = 2 * d;

    /* candidate (V, a, N) with V = 2 a N, a >= d */
    for (long Vv = lo; Vv <= hi; Vv++) {
        if (Vv & 1) continue;
        long half = Vv / 2;
        for (int a = d; a < MAXA && a <= half; a++) {
            if (half % a) continue;
            long N = half / a;
            if (N < 2 || N > MAXN) continue;
            if (nc < MAXC) {
                cands[nc].V = (int)Vv;
                cands[nc].a = a;
                cands[nc].N = (int)N;
                nc++;
            }
        }
    }

    int best_V = 0;
    int bm = 0, bk = 0, br = 0, bA = 0;
    int bT[MAXD];
    static int bvolt[MAXA][MAXD];

    for (;;) {
        shuffle_cands();
        int any = 0;
        for (int c = 0; c < nc; c++) {
            if (cands[c].V <= best_V) continue;
            double rem = t_end - now();
            if (rem < 0.3) goto finish;
            any = 1;
            double slice = rem * 0.1;
            if (slice < 0.5) slice = 0.5;
            if (slice > 3.0) slice = 3.0;
            if (slice > rem) slice = rem;

            int a = cands[c].a, N = cands[c].N;
            int divs[64], nd = 0;
            for (int m = 1; m <= N && nd < 64; m++)
                if (N % m == 0) divs[nd++] = m;
            int m = divs[rndint(nd)];
            int k = N / m;
            int r = 0;
            if (m > 1) {
                r = 1;
                for (int tries = 0; tries < 200; tries++) {
                    int cr = 1 + rndint(m - 1);
                    if (gcd_i(cr, m) == 1 && powmod(cr, k, m) == 1) { r = cr; break; }
                }
            }
            if (!build_group(m, k, r)) continue;

            A = a;
            int perm[MAXA];
            for (int i = 0; i < a; i++) perm[i] = i;
            for (int i = a - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
            }
            for (int t = 0; t < d; t++) T[t] = perm[t];

            if (climb(now() + slice)) {
                best_V = cands[c].V;
                bm = m; bk = k; br = r; bA = a;
                for (int t = 0; t < d; t++) bT[t] = T[t];
                for (int i = 0; i < a; i++)
                    for (int t = 0; t < d; t++) bvolt[i][t] = volt[i][t];
            }
        }
        if (!any) break;
    }

finish:
    if (best_V == 0) {
        print_complete();
        return 0;
    }
    A = bA;
    for (int t = 0; t < d; t++) T[t] = bT[t];
    for (int i = 0; i < A; i++)
        for (int t = 0; t < d; t++) volt[i][t] = bvolt[i][t];
    if (!build_group(bm, bk, br)) {
        print_complete();
        return 0;
    }
    rebuild_adj();
    if (cost_all() != 0) {
        print_complete();
        return 0;
    }
    int aN = A * gN;
    printf("%d %d\n", 2 * aN, aN * d);
    for (int i = 0; i < A; i++)
        for (int x = 0; x < gN; x++)
            for (int t = 0; t < d; t++) {
                int j = (i + T[t]) % A;
                int y = mulT[x * gN + volt[i][t]];
                printf("%d %d\n", i * gN + x, aN + j * gN + y);
            }
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def target_window(d, D):
    """Vertex-count window (lo, hi) for the C search, lo even-agnostic."""
    moore = lib.moore_bound(d, D)
    if d == 4 and D == 9:
        return 4370, min(5200, moore)
    return 4 * d, min(12000, moore)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))  # K_{d,d}
    if start is not None and best[0] >= lib.moore_bound(d, D):
        return best
    if d < 2 or d > 8 or D < 2:
        return best
    lo, hi = target_window(d, D)
    if start is not None:
        lo = max(lo, best[0] + 2)
    if lo > hi:
        return best
    budget = 0.8 * time_limit - 2.0 - (time.monotonic() - t0)
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                         timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass   # keep the valid fallback
    return best
