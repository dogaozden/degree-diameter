"""Program: random-voltage lifts over metacyclic groups with base size 1-3 (bi-Cayley generalised).

Construction (new family, replaces bi-Cayley-only search):
  * Base bipartite multigraph on b+b vertices (b in {1,2,3}) built from d perfect matchings
    sigma_k of {0..b-1}.
  * Voltages g[k][i] in a finite group G (metacyclic Z_m x|_r Z_k, order N = m*k).
  * Lift: vertex (A_i, x) ~ (B_{sigma_k(i)}, x*g[k][i]) for every k. The result has 2bN vertices,
    is bipartite, and is d-regular (parallel darts with equal voltage are penalised).
  * Left multiplication by G is an automorphism, so the diameter is <= D iff BFS from each of the
    2b fibre representatives (identity of each fibre) reaches all vertices within D steps.
  * Search: simulated annealing over voltages and matchings, cost = unreached (rep, vertex) pairs.

Scheduling: a low band just under the record secures a valid fallback; then the upper band
(vertex counts above the record) is searched with iterative deepening. The C engine always prints
a valid graph (K_{d,d} if nothing better is found). Python validates with lib.is_valid.
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

#define MAXN 3200
#define MAXB 3
#define MAXDEG 8
#define MAXV (2 * MAXB * MAXN)
#define MAXCAND 320
#define STALL 20000L
#define TEMP 1.0
#define CONFLICT_PEN 40L

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

/* ------------------------------------------------------------ group + lift state */

static int N = 0;
static int b = 1;
static int V = 0;
static uint16_t T[MAXN * MAXN];   /* T[x*N+y] = x*y */
static int INV[MAXN];
static int pw[MAXN], Cy[MAXN], Ey[MAXN];

static int sig[MAXDEG][MAXB];     /* sig[k][i]  : B index of dart k from A_i */
static int tau[MAXDEG][MAXB];     /* tau[k][j]  : A index whose dart k lands on B_j */
static int gv[MAXDEG][MAXB];      /* voltage of dart (k,i) */
static int gi[MAXDEG][MAXB];      /* inverse voltage */
static int nbr[MAXDEG];
static int stamp[MAXV];
static int qv[MAXV];
static int tick = 0;

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
static void build_group(int m, int k, int r) {
    N = m * k;
    pw[0] = 1 % m;
    for (int e = 1; e < k; e++) pw[e] = (int)((long)pw[e - 1] * r % m);
    for (int y = 0; y < N; y++) { Cy[y] = y / k; Ey[y] = y % k; }
    for (int x = 0; x < N; x++) {
        int a = x / k, bb = x % k;
        for (int y = 0; y < N; y++) {
            int aa = (int)(((long)a + (long)pw[bb] * Cy[y]) % m);
            int cc = (bb + Ey[y]) % k;
            int val = aa * k + cc;
            T[x * N + y] = (uint16_t)val;
            if (val == 0) INV[x] = y;
        }
    }
}

static void refresh(void) {
    for (int k = 0; k < d; k++) {
        for (int i = 0; i < b; i++) tau[k][sig[k][i]] = i;
        for (int i = 0; i < b; i++) gi[k][i] = INV[gv[k][i]];
    }
}

/* Neighbours of vertex v into nbr[0..d-1].
   A_i,x has id i*N+x; B_j,y has id (b+j)*N+y. */
static void neigh(int v) {
    int bN = b * N;
    if (v < bN) {
        int i = v / N, x = v - i * N;
        for (int k = 0; k < d; k++)
            nbr[k] = (b + sig[k][i]) * N + T[x * N + gv[k][i]];
    } else {
        int j = v / N - b, y = v - (j + b) * N;
        for (int k = 0; k < d; k++) {
            int i = tau[k][j];
            nbr[k] = i * N + T[y * N + gi[k][i]];
        }
    }
}

static int reach_from(int src) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            neigh(v);
            for (int t = 0; t < d; t++) {
                int u = nbr[t];
                if (stamp[u] != tick) {
                    stamp[u] = tick;
                    qv[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* Number of parallel-dart clashes (two darts from A_i to B_j with equal voltage). */
static long conflicts(void) {
    long c = 0;
    for (int i = 0; i < b; i++)
        for (int k = 0; k < d; k++)
            for (int l = k + 1; l < d; l++)
                if (sig[k][i] == sig[l][i] && gv[k][i] == gv[l][i]) c++;
    return c;
}

static long cost_eval(void) {
    long c = conflicts() * CONFLICT_PEN;
    for (int r = 0; r < 2 * b; r++) {
        int reached = reach_from(r * N);
        c += (long)(V - reached);
    }
    return c;
}

static void randomize(void) {
    for (int k = 0; k < d; k++) {
        int p[MAXB];
        for (int i = 0; i < b; i++) p[i] = i;
        for (int i = b - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = p[i];
            p[i] = p[j];
            p[j] = t;
        }
        for (int i = 0; i < b; i++) {
            sig[k][i] = p[i];
            gv[k][i] = rndint(N);
        }
    }
    refresh();
}

static void do_swap(int k, int i, int i2) {
    int t = sig[k][i];
    sig[k][i] = sig[k][i2];
    sig[k][i2] = t;
    tau[k][sig[k][i]] = i;
    tau[k][sig[k][i2]] = i2;
}

static int anneal(double until) {
    randomize();
    long cur = cost_eval(), best = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        if (stall > STALL) {
            randomize();
            cur = cost_eval();
            best = cur;
            stall = 0;
            continue;
        }
        int k = rndint(d);
        int i = rndint(b);
        int swp = (b >= 2 && rnd01() < 0.3);
        int i2 = 0, oldg = 0;
        if (swp) {
            i2 = rndint(b - 1);
            if (i2 >= i) i2++;
            do_swap(k, i, i2);
        } else {
            oldg = gv[k][i];
            gv[k][i] = rndint(N);
            gi[k][i] = INV[gv[k][i]];
        }
        long nc = cost_eval();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / TEMP)) {
            cur = nc;
        } else if (swp) {
            do_swap(k, i, i2);
        } else {
            gv[k][i] = oldg;
            gi[k][i] = INV[oldg];
        }
        if (cur < best) {
            best = cur;
            stall = 0;
        } else {
            stall++;
        }
    }
    return 1;
}

/* ------------------------------------------------------------ candidates */

typedef struct { int b, m, k, r; } Cand;   /* group order N = m*k, base size b */

static Cand candLo[MAXCAND], candHi[MAXCAND];
static int ncl = 0, nch = 0;

static Cand gbest;
static int gfound = 0;
static long gbestV = 0;
static int gbsig[MAXDEG][MAXB], gbgv[MAXDEG][MAXB];

static void add_to(Cand *list, int *n, int cap, int bb, int m, int k, int r) {
    if (*n < cap) {
        list[*n].b = bb;
        list[*n].m = m;
        list[*n].k = k;
        list[*n].r = r;
        (*n)++;
    }
}

static void gen_cands(long vlo, long vhi, Cand *list, int *n, int cap) {
    static const int order[3] = {2, 3, 1};
    *n = 0;
    if (vlo < 6) vlo = 6;
    for (long Vv = vlo; Vv <= vhi && *n < cap; Vv++) {
        for (int oi = 0; oi < 3; oi++) {
            int bb = order[oi];
            long per = 2L * bb;
            if (Vv % per) continue;
            long Nl = Vv / per;
            if (Nl < 4 || Nl > MAXN) continue;
            int nn = (int)Nl;
            for (int k = 1; k <= nn; k++) {
                if (nn % k) continue;
                int m = nn / k;
                if (m < 2) continue;
                add_to(list, n, cap, bb, m, k, 1);
                if (k >= 2) {
                    int got = 0;
                    for (int r = 2; r < m && got < 2; r++) {
                        if (gcd_l(r, m) != 1) continue;
                        if (powmod_l(r, k, m) != 1) continue;
                        add_to(list, n, cap, bb, m, k, r);
                        got++;
                    }
                }
            }
        }
    }
}

static void save_best(const Cand *c, int Vv) {
    gfound = 1;
    gbest = *c;
    gbestV = Vv;
    memcpy(gbsig, sig, sizeof sig);
    memcpy(gbgv, gv, sizeof gv);
}

static void search_phase(const Cand *list, int n, double phase_end) {
    if (n <= 0) return;
    double rem0 = phase_end - now();
    if (rem0 <= 0.05) return;
    double base = rem0 / (3.0 * (double)n);
    if (base < 0.02) base = 0.02;
    int cm = -1, ck = -1, cr = -1;
    for (int round = 0; round < 12; round++) {
        int ran = 0;
        for (int ci = 0; ci < n; ci++) {
            const Cand *c = &list[ci];
            long Vc = 2L * c->b * c->m * c->k;
            if (Vc <= gbestV) continue;
            double rem = phase_end - now();
            if (rem < 0.05) return;
            double slice = base * (double)(1 << round);
            if (slice > rem) slice = rem;
            if (c->m != cm || c->k != ck || c->r != cr) {
                build_group(c->m, c->k, c->r);
                cm = c->m;
                ck = c->k;
                cr = c->r;
            }
            b = c->b;
            V = 2 * b * N;
            ran = 1;
            if (anneal(now() + slice)) save_best(c, V);
        }
        if (!ran) return;
    }
}

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int c = 0; c < d; c++) printf("%d %d\n", a, d + c);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [ref_vertices]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long ref = argc > 5 ? atol(argv[5]) : 4970;
    if (ref < 1) ref = 1;

    double t0 = now();
    double usable = limit - 1.5;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }
    moore = moore_bound();

    long vhi = moore;
    long cap = (long)(1.12 * (double)ref);
    if (cap < ref + 200) cap = ref + 200;
    if (vhi > cap) vhi = cap;
    if (vhi > 2L * MAXB * MAXN) vhi = 2L * MAXB * MAXN;
    long lo_lo = (long)(0.93 * (double)ref);

    gen_cands(lo_lo, ref, candLo, &ncl, 160);
    gen_cands(ref + 1, vhi, candHi, &nch, MAXCAND);

    gfound = 0;
    gbestV = 0;
    /* low band first: a valid fallback just below the reference */
    search_phase(candLo, ncl, t0 + 0.2 * usable);
    /* upper band: vertex counts strictly above the reference */
    search_phase(candHi, nch, t_end);

    if (!gfound) { print_complete(); return 0; }

    build_group(gbest.m, gbest.k, gbest.r);
    b = gbest.b;
    V = 2 * b * N;
    memcpy(sig, gbsig, sizeof sig);
    memcpy(gv, gbgv, sizeof gv);
    refresh();
    if (cost_eval() != 0) { print_complete(); return 0; }

    printf("%d %ld\n", V, (long)b * d * N);
    for (int i = 0; i < b; i++)
        for (int x = 0; x < N; x++)
            for (int k = 0; k < d; k++) {
                int u = i * N + x;
                int w = (b + sig[k][i]) * N + T[x * N + gv[k][i]];
                printf("%d %d\n", u, w);
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


def _cycle(D):
    """Even cycle C_{2D}: bipartite, degree 2, diameter D (optimal for d = 2)."""
    n = 2 * D
    return n, [(i, (i + 1) % n) for i in range(n)]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    start = known_start(d, D)
    if start is None or not lib.is_valid(start[0], start[1], d, D):
        start = _cycle(D) if (d == 2 and D >= 2) else lib.haar_graph(d, range(d))
        if not lib.is_valid(start[0], start[1], d, D):
            start = lib.haar_graph(d, range(d))   # K_{d,d}
    best = start

    # Moore-optimal or trivially small cases: nothing to search.
    if d < 3 or D < 3 or best[0] >= lib.moore_bound(d, D):
        return best

    spare = 0.8 * time_limit - (time.monotonic() - t0) - 4.0
    if spare < 2.0:
        return best

    ref = max(best[0], REF_VERTICES.get((d, D), 0))
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(spare, 2), ref],
                         timeout=spare + 10.0)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass   # keep the valid fallback
    return best
