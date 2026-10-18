"""Combined bi-Cayley / voltage-lift search for bipartite degree-diameter graphs.

One C engine searches over lifts of small base multigraphs. A lift has p fibres per side,
each of size N, and a group G of order N acts on it by left multiplication. Vertex (i, x) on
the A side is joined to (p+j, x*g) for each dart (i, j, g). Left multiplication is an
automorphism that is regular on every fibre, so the diameter test needs only 2p BFS runs, one
from each fibre representative. Groups are metacyclic Z_m x| Z_k (table-free products) or
PSL/SL/PGL(2,q) for q <= 19 (products via a canonical index table). p = 1 gives Cayley-type
bi-Cayley graphs, and p = 2..4 gives richer base graphs.

Candidates are ordered around the reference order (close to the record first, then slightly
above it). They are scheduled in rounds with doubling slices, and each attempt runs
simulated annealing over the dart voltages with restarts. Only candidates that could beat the
current best are retried. Python supplies the algebraic starts, passes the best start graph
to C, and keeps the result only if lib.is_valid accepts it.
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

#define MAXV 20000
#define MAXN 10000
#define MAXM 5000
#define QMAX 19
#define MAXDEG 8
#define MAXP 4
#define MAXEDGES 80000
#define MAXCAND 4000
#define CYCLE 20000

static int d, D;
static long REF;
static int CAPV;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
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

static long cap_order(void) {
    long mb = moore_bound();
    return mb < MAXV ? mb : MAXV;
}

/* ------------------------------------------------------------ groups */

static int G_kind, G_N, G_e, G_m, G_k, G_r, G_q, G_mode;
static int PW[MAXN];
static int MATX[4 * MAXM];
static int IDXM[QMAX * QMAX * QMAX * QMAX];

static int inv_mod(int f, int q) {
    for (int x = 1; x < q; x++)
        if ((f * x) % q == 1) return x;
    return 0;
}

/* mode 0: PSL (+-), mode 1: SL, mode 2: PGL (scalars) */
static int canon_code(int q, int mode, int a, int b, int c, int e) {
    if (mode == 2) {
        int f = a ? a : (b ? b : (c ? c : e));
        int iv = inv_mod(f, q);
        a = a * iv % q;
        b = b * iv % q;
        c = c * iv % q;
        e = e * iv % q;
    }
    int code = ((a * q + b) * q + c) * q + e;
    if (mode == 0) {
        int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
        int c2 = ((na * q + nb) * q + nc) * q + ne;
        if (c2 < code) code = c2;
    }
    return code;
}

static int gmul(int x, int y) {
    if (G_kind == 0) {
        int k = G_k;
        int a = x / k, b = x % k, c = y / k, dd = y % k;
        int aa = (int)(((long)a + (long)PW[b] * c) % G_m);
        int bb = (b + dd) % k;
        return aa * k + bb;
    }
    const int *X = MATX + 4 * x, *Y = MATX + 4 * y;
    int q = G_q;
    int a = (X[0] * Y[0] + X[1] * Y[2]) % q;
    int b = (X[0] * Y[1] + X[1] * Y[3]) % q;
    int c = (X[2] * Y[0] + X[3] * Y[2]) % q;
    int e = (X[2] * Y[1] + X[3] * Y[3]) % q;
    return IDXM[canon_code(q, G_mode, a, b, c, e)];
}

/* Z_m x|_r Z_k, element (a,b) = a*k+b, (a,b)(c,f) = (a + r^b c, b+f). */
static int build_meta(int m, int k, int r) {
    long n = (long)m * k;
    if (n > MAXN || n < 2) return 0;
    G_kind = 0;
    G_m = m;
    G_k = k;
    G_r = r;
    G_N = (int)n;
    G_e = 0;
    PW[0] = 1 % m;
    for (int b = 1; b < k; b++) PW[b] = (int)((long)PW[b - 1] * r % m);
    return 1;
}

static int build_matrix(int q, int mode) {
    G_kind = 1;
    G_q = q;
    G_mode = mode;
    int Q4 = q * q * q * q;
    if (Q4 > QMAX * QMAX * QMAX * QMAX) return 0;
    for (int i = 0; i < Q4; i++) IDXM[i] = -1;
    int cnt = 0;
    for (int code = 0; code < Q4; code++) {
        int e = code % q, c = (code / q) % q, b = (code / (q * q)) % q, a = code / (q * q * q);
        int det = ((a * e - b * c) % q + q) % q;
        if (mode == 2) {
            if (det == 0) continue;
        } else if (det != 1) {
            continue;
        }
        if (canon_code(q, mode, a, b, c, e) != code) continue;
        if (cnt >= MAXM) return 0;
        MATX[4 * cnt] = a;
        MATX[4 * cnt + 1] = b;
        MATX[4 * cnt + 2] = c;
        MATX[4 * cnt + 3] = e;
        IDXM[code] = cnt;
        cnt++;
    }
    G_N = cnt;
    G_e = IDXM[canon_code(q, mode, 1, 0, 0, 1)];
    return cnt;
}

/* ------------------------------------------------------------ candidates */

typedef struct { int kind, q, mode, m, k, r, N, p, V; long tries; } Cand;
static Cand CANDS[MAXCAND];
static int nCand = 0;

static void push_meta(int m, int k, int r, int N, int p) {
    if (nCand >= MAXCAND) return;
    Cand *c = &CANDS[nCand++];
    memset(c, 0, sizeof *c);
    c->kind = 0;
    c->m = m;
    c->k = k;
    c->r = r;
    c->N = N;
    c->p = p;
    c->V = 2 * p * N;
}

static void push_matrix(int q, int mode, int N, int p) {
    if (nCand >= MAXCAND) return;
    Cand *c = &CANDS[nCand++];
    memset(c, 0, sizeof *c);
    c->kind = 1;
    c->q = q;
    c->mode = mode;
    c->N = N;
    c->p = p;
    c->V = 2 * p * N;
}

/* Metacyclic candidates with group order N in [lo, hi], visited descending or ascending. */
static void gen_meta(int p, long lo, long hi, int desc, int limit) {
    long hiN = CAPV / (2L * p);
    if (hi > hiN) hi = hiN;
    if (lo < 2) lo = 2;
    if (hi < lo) return;
    int cnt = 0;
    for (long i = 0; i <= hi - lo && cnt < limit; i++) {
        long N = desc ? hi - i : lo + i;
        for (long k = 2; k <= N / 3; k++) {
            if (N % k) continue;
            long m = N / k;
            if (m < 3) continue;
            int got = 0;
            for (long r = 2; r < m && got < 2; r++) {
                if (gcd_l(r, m) != 1) continue;
                if (powmod_l(r, k, m) != 1) continue;
                push_meta((int)m, (int)k, (int)r, (int)N, p);
                got++;
                cnt++;
            }
        }
    }
}

static void gen_matrix(long vlo, long vhi) {
    static const int qs[6] = {5, 7, 11, 13, 17, 19};
    for (int qi = 0; qi < 6; qi++) {
        for (int mode = 0; mode < 3; mode++) {
            int q = qs[qi];
            long N = (long)q * ((long)q * q - 1);
            if (mode == 0) N /= 2;
            if (N > MAXM) continue;
            for (int p = 1; p <= MAXP; p++) {
                if (p > 1 && d < 2) continue;
                long V = 2L * p * N;
                if (V < vlo || V > vhi) continue;
                push_matrix(q, mode, (int)N, p);
            }
        }
    }
}

/* ------------------------------------------------------------ best so far */

static int BEST_N = 0, BEST_M = 0;
static int BEST_E[2 * MAXEDGES];

static void read_start(void) {
    int n, m;
    BEST_N = 0;
    BEST_M = 0;
    if (scanf("%d %d", &n, &m) != 2) return;
    if (n <= 0 || n > MAXV || m < 0 || m > MAXEDGES) return;
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n) {
            BEST_N = 0;
            BEST_M = 0;
            return;
        }
        BEST_E[2 * e] = u;
        BEST_E[2 * e + 1] = v;
        BEST_M = e + 1;
    }
    BEST_N = n;
}

/* ------------------------------------------------------------ lift engine */

typedef struct { int i, j, g, rs, cs; } Dart;
static Dart DT[MAXDEG * MAXP];
static int ND;
static int GP, GN, GE, NV;
static int adjv[MAXV][MAXDEG];
static int stampv[MAXV], qv[MAXV];
static int tick_ = 0;

static int ball_size(int src) {
    if (++tick_ == 0x7fffffff) {
        memset(stampv, 0, sizeof stampv);
        tick_ = 1;
    }
    int head = 0, tail = 0;
    stampv[src] = tick_;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            for (int k = 0; k < d; k++) {
                int u = adjv[v][k];
                if (stampv[u] != tick_) {
                    stampv[u] = tick_;
                    qv[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* Number of (fibre representative, vertex) pairs not reached within D. 0 means valid. */
static long lift_cost(void) {
    long bad = 0;
    for (int f = 0; f < 2 * GP; f++) bad += NV - ball_size(f * GN + GE);
    return bad;
}

/* Random d-regular bipartite base multigraph on p + p vertices, connected. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, ns = 1;
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = (v < p) ? (u >= p && M[v][u - p] > 0) : (u < p && M[u][v - p] > 0);
                if (linked) {
                    seen[u] = 1;
                    ns++;
                    stack[top++] = u;
                }
            }
        }
        if (ns == 2 * p) return;
    }
}

/* Voltage for dart t, different from every other dart on the same base pair. */
static int fresh(int t) {
    int start = rndint(GN);
    for (int k = 0; k < GN; k++) {
        int g = (start + k) % GN;
        int ok = 1;
        for (int s = 0; s < ND; s++) {
            if (s == t || DT[s].g < 0) continue;
            if (DT[s].i == DT[t].i && DT[s].j == DT[t].j && DT[s].g == g) {
                ok = 0;
                break;
            }
        }
        if (ok) return g;
    }
    return start;
}

/* Rewrite the N edges of dart t from the current voltage. */
static void set_dart(int t) {
    int i = DT[t].i, j = DT[t].j, g = DT[t].g;
    for (int x = 0; x < GN; x++) {
        int a = i * GN + x;
        int b = (GP + j) * GN + gmul(x, g);
        adjv[a][DT[t].rs] = b;
        adjv[b][DT[t].cs] = a;
    }
}

static void init_cycle(void) {
    int M[MAXP][MAXP];
    make_base(GP, M);
    ND = 0;
    for (int i = 0; i < GP; i++)
        for (int j = 0; j < GP; j++)
            for (int c = 0; c < M[i][j]; c++) {
                DT[ND].i = i;
                DT[ND].j = j;
                DT[ND].g = -1;
                ND++;
            }
    for (int t = 0; t < ND; t++) {
        int rs = 0, cs = 0;
        for (int s = 0; s < t; s++) {
            if (DT[s].i == DT[t].i) rs++;
            if (DT[s].j == DT[t].j) cs++;
        }
        DT[t].rs = rs;
        DT[t].cs = cs;
    }
    for (int t = 0; t < ND; t++)
        DT[t].g = (GP == 1 && t == 0) ? GE : fresh(t);
    for (int t = 0; t < ND; t++) set_dart(t);
}

static void save_solution(void) {
    int V = 2 * GP * GN;
    int A = GP * GN;
    if (V <= BEST_N) return;
    if ((long)A * d > MAXEDGES) return;
    int m = 0;
    for (int a = 0; a < A; a++)
        for (int k = 0; k < d; k++) {
            BEST_E[2 * m] = a;
            BEST_E[2 * m + 1] = adjv[a][k];
            m++;
        }
    BEST_N = V;
    BEST_M = m;
}

/* Anneal voltages of random lifts of one candidate until time runs out or a valid lift is found. */
static int attempt(const Cand *c, double until) {
    if (c->kind == 0) {
        if (!build_meta(c->m, c->k, c->r)) return 0;
    } else {
        if (!build_matrix(c->q, c->mode)) return 0;
    }
    GN = G_N;
    GE = G_e;
    GP = c->p;
    if (GN != c->N || GN < d + 1) return 0;
    NV = 2 * GP * GN;
    if (NV > CAPV) return 0;
    while (now() < until) {
        init_cycle();
        long cur = lift_cost();
        if (cur == 0) {
            save_solution();
            return 1;
        }
        for (long s = 0; s < CYCLE; s++) {
            if ((s & 63) == 0 && now() > until) return 0;
            double T = 2.0 * pow(0.02, (double)s / CYCLE);
            int t = rndint(ND);
            int old = DT[t].g;
            DT[t].g = fresh(t);
            set_dart(t);
            long nc = lift_cost();
            long df = nc - cur;
            if (df <= 0 || rnd01() < exp(-(double)df / T)) {
                cur = nc;
                if (cur == 0) {
                    save_solution();
                    return 1;
                }
            } else {
                DT[t].g = old;
                set_dart(t);
            }
        }
    }
    return 0;
}

/* Rounds with doubling slices over all candidates that can still beat the best. */
static void schedule(void) {
    double budget = t_end - now();
    double base = budget / (2.5 * (double)(nCand > 0 ? nCand : 1));
    if (base < 0.08) base = 0.08;
    if (base > 3.0) base = 3.0;
    for (int round = 0; round < 40; round++) {
        int active = 0;
        for (int i = 0; i < nCand; i++) {
            double rem = t_end - now();
            if (rem < 0.05) return;
            Cand *c = &CANDS[i];
            if (c->V <= BEST_N) continue;
            active = 1;
            double slice = base * (double)(1L << (round < 6 ? round : 6));
            if (slice > rem) slice = rem;
            attempt(c, now() + slice);
            c->tries++;
        }
        if (!active) return;
    }
}

static void output_best(void) {
    if (BEST_N == 0) {
        if (D >= 2) {
            printf("%d %d\n", 2 * d, d * d);
            for (int a = 0; a < d; a++)
                for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
        } else {
            printf("2 1\n0 1\n");
        }
        return;
    }
    printf("%d %d\n", BEST_N, BEST_M);
    for (int i = 0; i < BEST_M; i++) printf("%d %d\n", BEST_E[2 * i], BEST_E[2 * i + 1]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [ref_vertices] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    REF = argc > 5 ? atol(argv[5]) : 0;

    double t0 = now();
    double usable = limit * 0.9 - 0.3;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG) {
        printf("0 0\n");
        return 0;
    }
    read_start();
    CAPV = (int)cap_order();
    if (REF <= 0) REF = CAPV / 2;

    if (d >= 2 && D >= 2 && BEST_N < CAPV) {
        long VLO = (long)(0.85 * (double)REF);
        if (VLO < BEST_N + 1) VLO = BEST_N + 1;
        long VHI = (long)(1.2 * (double)REF);
        if (VHI > CAPV) VHI = CAPV;

        gen_matrix(VLO, CAPV);
        gen_meta(1, (VLO + 1) / 2, REF / 2, 1, 60);
        gen_meta(1, REF / 2 + 1, VHI / 2, 0, 60);
        gen_meta(2, (VLO + 3) / 4, REF / 4, 1, 30);
        gen_meta(2, REF / 4 + 1, VHI / 4, 0, 30);
        gen_meta(3, (VLO + 5) / 6, REF / 6, 1, 20);
        gen_meta(3, REF / 6 + 1, VHI / 6, 0, 20);
        gen_meta(4, (VLO + 7) / 8, REF / 8, 1, 20);
        gen_meta(4, REF / 8 + 1, VHI / 8, 0, 20);

        schedule();
    }
    output_best();
    return 0;
}
'''


def _try(fn, *args):
    try:
        return fn(*args)
    except Exception:
        return None


REF_VERTICES = {(4, 9): 4970}


def known_start(d, D):
    """Algebraic start for D = 3 (Moore graph or Araujo-Pardo-Lopez record), or None."""
    if D == 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        return _try(lib.projective_plane_incidence, d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return _try(lib.araujo_lopez_graph, d - 2)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    start = known_start(d, D)
    if start is None or not lib.is_valid(start[0], start[1], d, D):
        start = lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2
    best = start

    if d > 8 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best

    ref = REF_VERTICES.get((d, D), 0)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), ref],
                         stdin_graph=best, timeout=budget + 5)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass   # keep the valid fallback
    return best
