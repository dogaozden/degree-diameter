"""Program: multi-orbit voltage-lift search with resumable annealing.

Construction (new in this version):
  * Base graph with P vertices on each side (P = 1..4). Each A-orbit i has d darts, each B-orbit j
    has d darts. A pattern cnt[i][j] gives how many darts join A_i to B_j (row and column sums = d).
  * Group G of order M is cyclic or metacyclic Z_m x|_r Z_k. Dart t = (i, j, g) joins
    A(i,x) to B(j, x*g) for all x. The lift has 2*P*M vertices and is exactly d-regular and bipartite.
    Distinct voltages inside each (i,j) block keep the graph simple.
  * Left multiplication by G is an automorphism, so diameter <= D holds iff BFS from A(i,e) and
    B(j,e) for every orbit reaches all 2PM vertices within D steps. The cost is the total number of
    unreached (source, vertex) pairs.
  * Candidates cover vertex counts from 0.9*ref up to ref+30, so they include sizes above the record.
    Successive halving ranks them by residual cost per vertex. Each survivor resumes annealing from its
    saved best voltages, so no work is lost between rounds. A success raises the bar and drops every
    candidate at or below it.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with lib.is_valid
and keeps the best valid graph, falling back to the known start or K_{d,d}.
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
#define MAXP 4
#define MAXD 8
#define MAXV 16384
#define MAXL (MAXP * MAXD)
#define MAXPAT 4096
#define POOL_CAP 32
#define MAXCAND 4096
#define COST_FAIL (1L << 40)

#define T_HI 3.0
#define T_LO 0.08
#define CYCLES 3.0

static int d, D;
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

static int N = 0, P = 1, e_id = 0;
static uint16_t Tab[MAXN * MAXN];   /* Tab[x*N+y] = x*y */
static int INV[MAXN];

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d). */
static void build_group(int m, int k, int r) {
    N = m * k;
    static int pw[MAXN];
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, dd = y % k;
            int aa = (int)(((long)a + (long)pw[b] * c) % m);
            int bb = (b + dd) % k;
            Tab[(size_t)x * N + y] = (uint16_t)(aa * k + bb);
        }
    }
    e_id = 0;
    for (int x = 0; x < N; x++) INV[x] = -1;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (Tab[(size_t)x * N + y] == 0) { INV[x] = y; break; }
}

/* ------------------------------------------------------------ base patterns */

static int npat[MAXP + 1];
static uint8_t PAT[MAXP + 1][MAXPAT][MAXP][MAXP];
static int cur[MAXP][MAXP];
static int pp_cur = 1;

static void rec_pat(int pos) {
    int p = pp_cur;
    if (npat[p] >= MAXPAT) return;
    if (pos == p * p) {
        for (int i = 0; i < p; i++) {
            int s = 0;
            for (int j = 0; j < p; j++) s += cur[i][j];
            if (s != d) return;
        }
        for (int j = 0; j < p; j++) {
            int s = 0;
            for (int i = 0; i < p; i++) s += cur[i][j];
            if (s != d) return;
        }
        for (int i = 0; i < p; i++)
            for (int j = 0; j < p; j++) PAT[p][npat[p]][i][j] = (uint8_t)cur[i][j];
        npat[p]++;
        return;
    }
    int i = pos / p, j = pos % p;
    int rs = 0, cs = 0;
    for (int jj = 0; jj < j; jj++) rs += cur[i][jj];
    for (int ii = 0; ii < i; ii++) cs += cur[ii][j];
    int lo = 0, hi = d;
    if (d - rs < hi) hi = d - rs;
    if (d - cs < hi) hi = d - cs;
    if (j == p - 1) {
        if (d - rs > lo) lo = d - rs;
        if (d - rs < hi) hi = d - rs;
    }
    if (i == p - 1) {
        if (d - cs > lo) lo = d - cs;
        if (d - cs < hi) hi = d - cs;
    }
    for (int v = lo; v <= hi; v++) {
        cur[i][j] = v;
        rec_pat(pos + 1);
    }
}

/* ------------------------------------------------------------ candidates */

typedef struct {
    int m, k, r, p, V;
    uint8_t cnt[MAXP][MAXP];
    int has;
    int st[MAXL];
} Cand;

static Cand cands[MAXCAND];
static int ncand = 0;

static void add_cand(int m, int k, int r, int p, int V) {
    if (ncand >= MAXCAND) return;
    Cand *c = &cands[ncand++];
    memset(c, 0, sizeof *c);
    c->m = m; c->k = k; c->r = r; c->p = p; c->V = V;
    int idx = rndint(npat[p]);
    memcpy(c->cnt, PAT[p][idx], sizeof c->cnt);
}

/* ------------------------------------------------------------ darts */

static int L = 0;
static int DI[MAXL], DJ[MAXL], G[MAXL], GI[MAXL];
static int RL[MAXP][MAXD], CL[MAXP][MAXD];

static void set_pattern(const Cand *c) {
    int rc[MAXP] = {0}, cc[MAXP] = {0};
    L = 0;
    for (int i = 0; i < c->p; i++)
        for (int j = 0; j < c->p; j++)
            for (int q = 0; q < c->cnt[i][j]; q++) {
                DI[L] = i;
                DJ[L] = j;
                RL[i][rc[i]++] = L;
                CL[j][cc[j]++] = L;
                L++;
            }
}

/* true if another dart in the same (i,j) block already uses voltage g */
static int clash(int t, int g) {
    for (int u = 0; u < L; u++)
        if (u != t && G[u] == g && DI[u] == DI[t] && DJ[u] == DJ[t]) return 1;
    return 0;
}

static void randomize(void) {
    for (int t = 0; t < L; t++) G[t] = -1;
    for (int t = 0; t < L; t++) {
        int g;
        do g = rndint(N); while (clash(t, g));
        G[t] = g;
        GI[t] = INV[g];
    }
}

static void apply(const Cand *c) {
    P = c->p;
    build_group(c->m, c->k, c->r);
    set_pattern(c);
    if (c->has) {
        for (int t = 0; t < L; t++) {
            G[t] = c->st[t];
            GI[t] = INV[G[t]];
        }
    }
}

/* ------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick_c = 0;
static int qv[MAXV];

static int ball(int src) {
    if (++tick_c == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick_c = 1;
    }
    int PN = P * N;
    int head = 0, tail = 0;
    stamp[src] = tick_c;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < PN) {
                int i = v / N, x = v - i * N;
                const uint16_t *row = &Tab[(size_t)x * N];
                for (int a = 0; a < d; a++) {
                    int t = RL[i][a];
                    int u = PN + DJ[t] * N + row[G[t]];
                    if (stamp[u] != tick_c) { stamp[u] = tick_c; qv[tail++] = u; }
                }
            } else {
                int w = v - PN;
                int j = w / N, y = w - j * N;
                const uint16_t *row = &Tab[(size_t)y * N];
                for (int a = 0; a < d; a++) {
                    int t = CL[j][a];
                    int u = DI[t] * N + row[GI[t]];
                    if (stamp[u] != tick_c) { stamp[u] = tick_c; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached (source, vertex) pairs over one source per orbit (0 = valid). */
static long cost_now(void) {
    long V = 2L * P * N;
    long c = 0;
    for (int i = 0; i < P; i++) c += V - ball(i * N + e_id);
    for (int j = 0; j < P; j++) c += V - ball(P * N + j * N + e_id);
    return c;
}

/* Simulated annealing with sawtooth reheating; on return G holds the best state seen. */
static long climb(double until, int resume) {
    double start = now();
    double span = until - start;
    if (span <= 0.0) return COST_FAIL;
    if (!resume) randomize();
    long cur_c = cost_now();
    long bestc = cur_c;
    static int bestG[MAXL];
    memcpy(bestG, G, sizeof(int) * (size_t)L);
    double temp = T_HI;
    long it = 0;
    while (cur_c > 0) {
        if ((++it & 7) == 0) {
            double t = now();
            if (t >= until) break;
            double f = (t - start) / span;
            double ph = f * CYCLES;
            ph = ph - floor(ph);
            temp = T_HI * pow(T_LO / T_HI, ph);
        }
        int t = rndint(L);
        int old = G[t], oldi = GI[t];
        int g;
        do g = rndint(N); while (g == old || clash(t, g));
        G[t] = g;
        GI[t] = INV[g];
        long nc = cost_now();
        long delta = nc - cur_c;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur_c = nc;
            if (cur_c < bestc) {
                bestc = cur_c;
                memcpy(bestG, G, sizeof(int) * (size_t)L);
            }
        } else {
            G[t] = old;
            GI[t] = oldi;
        }
    }
    memcpy(G, bestG, sizeof(int) * (size_t)L);
    for (int t = 0; t < L; t++) GI[t] = INV[G[t]];
    return bestc;
}

/* ------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static void print_lift(void) {
    int PN = P * N;
    printf("%d %d\n", 2 * PN, PN * d);
    for (int i = 0; i < P; i++)
        for (int x = 0; x < N; x++)
            for (int a = 0; a < d; a++) {
                int t = RL[i][a];
                int u = PN + DJ[t] * N + Tab[(size_t)x * N + G[t]];
                printf("%d %d\n", i * N + x, u);
            }
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
    if (ref <= 0) ref = 4970;

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    for (int p = 1; p <= MAXP; p++) {
        npat[p] = 0;
        pp_cur = p;
        rec_pat(0);
    }

    /* Candidates: multi-orbit lifts with total vertices V = 2*p*M in the window. */
    long lowV = (long)(0.9 * (double)ref), hiV = ref + 30;
    if (hiV > moore) hiV = moore;
    if (hiV > MAXV - 1) hiV = MAXV - 1;
    if (lowV < 6) lowV = 6;
    for (long V = lowV; V <= hiV && ncand < MAXCAND - 64; V++) {
        for (int p = 1; p <= MAXP; p++) {
            if (V % (2 * p)) continue;
            long M = V / (2 * p);
            if (M < 3 || M > MAXN || npat[p] == 0) continue;
            int opts = 0;
            for (long k = 1; k <= M && opts < 4; k++) {
                if (M % k) continue;
                int m = (int)(M / k);
                if (m < 2) continue;
                if (k == 1) { add_cand(m, 1, 1, p, (int)V); opts++; continue; }
                add_cand(m, (int)k, 1, p, (int)V);
                opts++;
                int got = 0;
                for (int r = 2; r < m && got < 1 && opts < 4; r++) {
                    if (gcd_l(r, m) != 1 || powmod_l(r, k, m) != 1) continue;
                    add_cand(m, (int)k, r, p, (int)V);
                    got++;
                    opts++;
                }
            }
        }
    }
    if (ncand > POOL_CAP) {
        int stride = (ncand + POOL_CAP - 1) / POOL_CAP;
        int w = 0;
        for (int i = 0; i < ncand; i += stride) cands[w++] = cands[i];
        ncand = w;
    }

    static int alive[MAXCAND];
    static double res[MAXCAND];
    int nalive = ncand;
    for (int i = 0; i < ncand; i++) { alive[i] = i; res[i] = 1e18; }
    double rem0 = t_end - now();
    double slice = rem0 / (4.0 * (nalive > 0 ? nalive : 1));
    if (slice > 1.5) slice = 1.5;
    if (slice < 0.15) slice = 0.15;

    int bestV = 0, have = 0;
    Cand bestC;
    memset(&bestC, 0, sizeof bestC);

    /* Successive halving with resumable annealing. */
    while (nalive > 0) {
        int nnew = 0, timeup = 0;
        for (int a = 0; a < nalive; a++) {
            int i = alive[a];
            Cand *c = &cands[i];
            if (c->V <= bestV) continue;
            double rem = t_end - now();
            if (rem < 0.05) { timeup = 1; break; }
            apply(c);
            double sl = slice < rem ? slice : rem;
            long bc = climb(now() + sl, c->has);
            for (int t = 0; t < L; t++) c->st[t] = G[t];
            c->has = 1;
            if (bc == 0) {
                have = 1;
                bestV = c->V;
                bestC = *c;
                continue;
            }
            res[i] = (double)bc / (double)c->V;
            alive[nnew++] = i;   /* nnew <= a, so unread entries are never overwritten */
        }
        if (timeup) break;
        for (int x = 1; x < nnew; x++) {
            int t = alive[x];
            int y = x - 1;
            while (y >= 0 && res[alive[y]] > res[t]) {
                alive[y + 1] = alive[y];
                y--;
            }
            alive[y + 1] = t;
        }
        nalive = (nnew + 1) / 2;
        slice *= 2.0;
    }

    if (!have) { print_complete(); return 0; }
    apply(&bestC);
    if (cost_now() != 0) { print_complete(); return 0; }
    print_lift();
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
    moore = lib.moore_bound(d, D)
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= moore:
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            ref = REF_VERTICES.get((d, D), max(4, int(0.25 * moore)))
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, ref], timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
