"""Program: multi-vertex voltage lifts over metacyclic groups (bipartite base graphs with P vertices per side).

Construction (new in this version):
  * Base graph: P vertices on each side, given by a d-regular bipartite multigraph M (row and column sums d,
    built as a sum of d random permutation matrices, connected). Each dart (i, j) carries a voltage g in G.
  * Group G = Z_m x|_r Z_k (order N). Lift: A_{i,x} is joined to B_{j, x*g} for every dart (i, j, g).
    The lift has 2*P*N vertices and is d-regular and bipartite.
  * Left multiplication by G is an automorphism, so the diameter is <= D iff BFS from (A_i, e) and (B_j, e)
    reaches every vertex within D steps for all i, j. The cost is the number of unreached pairs.
  * The bi-Cayley case (P = 1) is kept, so the known 4970-vertex record can still be rebuilt.
  * Candidates: P = 1 at N = ceil(REF/2) first (phase A, the safe record path), then P = 2, 3, 4 at group
    orders just above REF/(2P), which give more than REF vertices. Phase B runs all candidates round-robin
    with doubling slices. Search state persists across slices.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with lib.is_valid and
keeps the best valid graph, falling back to the known start or K_{d,d}.
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

#define MAXN 2600
#define MAXV 6000
#define MAXD 8
#define MAXP 4
#define MAXE (MAXP * MAXD)
#define MAXCAND 48
#define STALL 3000

static int d, D;
static long REF, moore;
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

/* ------------------------------------------------------------ group */

static int GM, GK, GN;          /* current group Z_m x|_r Z_k, order GN = GM*GK */
static int PW[MAXN];            /* PW[b] = r^b mod m */
static uint16_t T[MAXN * MAXN]; /* T[x*GN+y] = x*y, element (a,b) coded a*k+b */

static void build_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GN = m * k;
    PW[0] = 1 % m;
    for (int b = 1; b < k; b++) PW[b] = (int)((long)PW[b - 1] * r % m);
    for (int x = 0; x < GN; x++) {
        int a = x / k, b = x % k;
        uint16_t *row = T + (size_t)x * GN;
        int t = 0;   /* t = PW[b] * c mod m */
        for (int c = 0; c < m; c++) {
            int aa = a + t;
            if (aa >= m) aa -= m;
            for (int dd = 0; dd < k; dd++) {
                int bb = b + dd;
                if (bb >= k) bb -= k;
                row[c * k + dd] = (uint16_t)(aa * k + bb);
            }
            t += PW[b];
            if (t >= m) t -= m;
        }
    }
}

/* inverse of (a,b) is (-r^{-b} a, -b), and r^{-b} = r^{k-b} */
static int ginv(int g) {
    int a = g / GK, b = g % GK;
    int nb = (GK - b) % GK;
    int na = (int)((GM - ((long)PW[nb] * a) % GM) % GM);
    return na * GK + nb;
}

/* ------------------------------------------------------------ darts */

static int P, NE, PN, VN;
static int DI[MAXE], DJ[MAXE], DG[MAXE], DINV[MAXE];
static int AD[MAXP][MAXD], BD[MAXP][MAXD];

static void set_darts(int Pn, int M[MAXP][MAXP]) {
    P = Pn;
    NE = 0;
    for (int i = 0; i < P; i++)
        for (int j = 0; j < P; j++)
            for (int c = 0; c < M[i][j]; c++) {
                DI[NE] = i;
                DJ[NE] = j;
                NE++;
            }
    int ca[MAXP] = {0}, cb[MAXP] = {0};
    for (int k = 0; k < NE; k++) {
        AD[DI[k]][ca[DI[k]]++] = k;
        BD[DJ[k]][cb[DJ[k]]++] = k;
    }
    PN = P * GN;
    VN = 2 * PN;
}

static void set_volt(int k, int g) {
    DG[k] = g;
    DINV[k] = ginv(g);
}

/* conflict: two darts on the same (i,j) pair may not share a voltage */
static int conflict_upto(int k, int g) {
    for (int k2 = 0; k2 < k; k2++)
        if (DI[k2] == DI[k] && DJ[k2] == DJ[k] && DG[k2] == g) return 1;
    return 0;
}

static int conflict_any(int k, int g) {
    for (int k2 = 0; k2 < NE; k2++)
        if (k2 != k && DI[k2] == DI[k] && DJ[k2] == DJ[k] && DG[k2] == g) return 1;
    return 0;
}

static void randomize_all(void) {
    for (int k = 0; k < NE; k++) {
        int g;
        do g = rndint(GN); while (conflict_upto(k, g));
        set_volt(k, g);
    }
}

/* ------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick_n = 0;
static int qv[MAXV];

static int ball(int src, int dmax) {
    if (++tick_n == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick_n = 1;
    }
    int head = 0, tail = 0;
    stamp[src] = tick_n;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < PN) {
                int i = v / GN, x = v - i * GN;
                for (int t = 0; t < d; t++) {
                    int k = AD[i][t];
                    int u = PN + DJ[k] * GN + T[(size_t)x * GN + DG[k]];
                    if (stamp[u] != tick_n) { stamp[u] = tick_n; qv[tail++] = u; }
                }
            } else {
                int w = v - PN;
                int j = w / GN, y = w - j * GN;
                for (int t = 0; t < d; t++) {
                    int k = BD[j][t];
                    int u = DI[k] * GN + T[(size_t)y * GN + DINV[k]];
                    if (stamp[u] != tick_n) { stamp[u] = tick_n; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Sources: identity of every A-fiber and every B-fiber (element 0 is the identity). */
static long cost_now(void) {
    long c = 0;
    for (int s = 0; s < 2 * P; s++) {
        int src = (s < P) ? s * GN : PN + (s - P) * GN;
        c += (long)(VN - ball(src, D));
    }
    return c;
}

static int climb(double until, long *out) {
    long cur = cost_now(), best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 15) == 0 && now() > until) break;
        if (stall > STALL) {
            randomize_all();
            cur = cost_now();
            best_c = cur;
            stall = 0;
            continue;
        }
        int k = rndint(NE);
        int old = DG[k];
        int g;
        do g = rndint(GN); while (conflict_any(k, g));
        set_volt(k, g);
        long nc = cost_now();
        if (nc <= cur || rnd01() < 0.02) cur = nc;
        else set_volt(k, old);
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
    }
    *out = cur;
    return cur == 0;
}

/* ------------------------------------------------------------ candidates */

typedef struct {
    int P, m, k, r, N;
    int M[MAXP][MAXP];
    int ready, done;
    int DG[MAXE];
} Cand;

static Cand cands[MAXCAND];
static int ncand = 0;

static int gen_groups(int N, int want, int *gm, int *gk, int *gr) {
    int ng = 0;
    gm[ng] = N; gk[ng] = 1; gr[ng] = 1; ng++;          /* cyclic */
    for (int k = 2; k <= N / 3 && ng < want; k++) {
        if (N % k) continue;
        int m = N / k;
        for (int r = 2; r < m; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            gm[ng] = m; gk[ng] = k; gr[ng] = r; ng++;
            break;
        }
    }
    return ng;
}

static void rand_perm(int n, int *p) {
    for (int i = 0; i < n; i++) p[i] = i;
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = p[i]; p[i] = p[j]; p[j] = t;
    }
}

static int uf[2 * MAXP];
static int findu(int x) {
    while (uf[x] != x) {
        uf[x] = uf[uf[x]];
        x = uf[x];
    }
    return x;
}

/* Random d-regular bipartite base multigraph on Pn + Pn vertices, connected. */
static int gen_M(int Pn, int M[MAXP][MAXP]) {
    for (int att = 0; att < 200; att++) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int sg[MAXP];
            rand_perm(Pn, sg);
            for (int i = 0; i < Pn; i++) M[i][sg[i]]++;
        }
        for (int v = 0; v < 2 * Pn; v++) uf[v] = v;
        for (int i = 0; i < Pn; i++)
            for (int j = 0; j < Pn; j++)
                if (M[i][j] > 0) {
                    int a = findu(i), b = findu(Pn + j);
                    if (a != b) uf[a] = b;
                }
        int r0 = findu(0), ok = 1;
        for (int v = 1; v < 2 * Pn; v++)
            if (findu(v) != r0) { ok = 0; break; }
        if (ok) return 1;
    }
    return 0;
}

static void push_cand(int Pn, int N, int m, int k, int r, int M[MAXP][MAXP]) {
    if (ncand >= MAXCAND) return;
    Cand *c = &cands[ncand++];
    memset(c, 0, sizeof *c);
    c->P = Pn;
    c->N = N;
    c->m = m;
    c->k = k;
    c->r = r;
    memcpy(c->M, M, sizeof(int) * MAXP * MAXP);
}

static void add_candidates(void) {
    int gm[4], gk[4], gr[4];
    int M[MAXP][MAXP];
    /* phase A: bi-Cayley at N = ceil(REF/2), reproducing the record vertex count */
    long N1 = (REF + 1) / 2;
    if (N1 >= d + 1 && N1 <= MAXN && 2 * N1 <= moore && 2 * N1 <= MAXV) {
        int ng = gen_groups((int)N1, 3, gm, gk, gr);
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        M[0][0] = d;
        for (int g = 0; g < ng; g++) push_cand(1, (int)N1, gm[g], gk[g], gr[g], M);
    }
    /* phase B: lifts over P = 2, 3, 4 base vertices per side, orders just above REF/(2P) */
    for (int p = 2; p <= MAXP; p++) {
        long Nmin = REF / (2 * p) + 1;
        for (long N = Nmin; N < Nmin + 2; N++) {
            if (N > MAXN || 2 * p * N > moore || 2 * p * N > MAXV) break;
            if (N < d + 1) continue;
            int ng = gen_groups((int)N, 2, gm, gk, gr);
            for (int g = 0; g < ng; g++)
                for (int mm = 0; mm < 2; mm++) {
                    if (!gen_M(p, M)) continue;
                    push_cand(p, (int)N, gm[g], gk[g], gr[g], M);
                }
        }
    }
}

static void setup(Cand *c) {
    build_group(c->m, c->k, c->r);
    set_darts(c->P, c->M);
    if (c->ready) {
        for (int k = 0; k < NE; k++) set_volt(k, c->DG[k]);
    } else {
        randomize_all();
    }
}

static void save(Cand *c) {
    for (int k = 0; k < NE; k++) c->DG[k] = DG[k];
    c->ready = 1;
}

/* Round-robin with doubling slices; each candidate resumes from its saved voltages. */
static void run_phase(int only_p1, double phase_end, double base, int *bestV, int *bestIdx) {
    for (int round = 0;; round++) {
        int active = 0;
        for (int i = 0; i < ncand; i++) {
            Cand *c = &cands[i];
            if (c->done) continue;
            if (only_p1 && c->P != 1) continue;
            int V = 2 * c->P * c->N;
            if (V <= *bestV) continue;
            double remaining = phase_end - now();
            if (remaining < 0.05) return;
            double slice = base * (double)(1 << (round < 6 ? round : 6));
            if (slice > remaining) slice = remaining;
            setup(c);
            long cst = 0;
            int ok = climb(now() + slice, &cst);
            save(c);
            active = 1;
            if (ok) {
                c->done = 1;
                if (V > *bestV) { *bestV = V; *bestIdx = i; }
            }
        }
        if (!active) return;
    }
}

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
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
    REF = argc > 5 ? atol(argv[5]) : 4970;
    if (REF <= 0) REF = 4970;

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) { print_complete(); return 0; }
    moore = moore_bound();
    add_candidates();
    if (ncand == 0) { print_complete(); return 0; }

    int bestV = 0, bestIdx = -1;
    double total = t_end - now();
    if (total < 0.5) total = 0.5;
    double baseA = total * 0.01;
    if (baseA < 0.2) baseA = 0.2;
    double baseB = total * 0.006;
    if (baseB < 0.1) baseB = 0.1;

    run_phase(1, now() + 0.3 * total, baseA, &bestV, &bestIdx);
    run_phase(0, t_end, baseB, &bestV, &bestIdx);

    if (bestIdx < 0) { print_complete(); return 0; }
    Cand *c = &cands[bestIdx];
    setup(c);
    if (cost_now() != 0) { print_complete(); return 0; }

    printf("%d %d\n", VN, PN * d);
    for (int i = 0; i < P; i++)
        for (int x = 0; x < GN; x++) {
            int v = i * GN + x;
            for (int t = 0; t < d; t++) {
                int k = AD[i][t];
                int u = PN + DJ[k] * GN + T[(size_t)x * GN + DG[k]];
                printf("%d %d\n", v, u);
            }
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
    budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.3:
        try:
            ref = REF_VERTICES.get((d, D), best[0])
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), ref],
                             timeout=budget + 6)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
