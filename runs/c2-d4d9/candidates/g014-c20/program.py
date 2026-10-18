"""Program: multi-base bi-Cayley voltage lifts over metacyclic and PSL/SL(2,q) groups.

Construction (new in this version, replacing the single-base bi-Cayley search):
  * Group G of order N and a base graph with K vertices per side (K = 1..6). Vertices are
    A_i x and B_j y (i, j < K, x, y in G). Each base pair (i, j) carries a voltage set S_ij
    with |S_ij| = c_ij, where the count matrix c has all row and column sums equal to d.
    Edges: A_i x ~ B_j (x s) for s in S_ij. The graph is d-regular, bipartite, with 2KN vertices.
  * Left multiplication is an automorphism, so diameter <= D holds iff BFS from A_i e (all i)
    and from B_j e (all j) reaches every vertex within D steps.
  * Search: simulated annealing over the voltage sets with sawtooth reheating. Moves replace one
    voltage, or apply a 2x2 "cycle" move that changes the count matrix while keeping all row and
    column sums. The count matrix is therefore searched, not fixed.
  * Candidates: all (K, group) pairs with 2KN just above the record half, plus a few at or
    below it as fallbacks. Iterative deepening gives each candidate a slice that doubles per round,
    and candidates at or below the best found so far are skipped.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with
lib.is_valid and keeps the best valid graph, falling back to the known start or K_{d,d}.
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
#define MAXK 6
#define MAXD 8
#define MAXKN 3300
#define MAXV (2 * MAXKN)
#define MAXCAND 40

#define T_HI 3.0
#define T_LO 0.08
#define CYCLES 3.0

typedef struct {
    int type;            /* 0 = metacyclic, 1 = matrix group */
    int q, psl, m, kk, r;
    int K, N, kN;        /* base vertices per side, group order, K*N */
} Cand;

static int d, D;
static long moore_g;
static double t_end;

static int K = 1, N = 0, KN = 0, NV = 0, e_id = 0;
static uint16_t *T = NULL;   /* T[x*N+y] = x*y */
static int *INV = NULL;

/* voltage state: cnt[i][j] darts from A_i to B_j, E[i][j][t] their voltages */
static int cnt[MAXK][MAXK];
static int E[MAXK][MAXK][MAXD];
static int RF[MAXK][MAXK][MAXD][MAXN];   /* RF[i][j][t][x] = x * s      */
static int RB[MAXK][MAXK][MAXD][MAXN];   /* RB[i][j][t][y] = y * s^{-1} */
static int ucnt[MAXK][MAXK];
static int uE[MAXK][MAXK][MAXD];
static int bcnt[MAXK][MAXK];
static int bE[MAXK][MAXK][MAXD];
static int aff_i[4], aff_j[4], naff = 0;

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

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

/* ------------------------------------------------------------------ groups */

static void alloc_group(int n) {
    free(T);
    free(INV);
    T = malloc(sizeof(uint16_t) * (size_t)n * (size_t)n);
    INV = malloc(sizeof(int) * (size_t)n);
}

static void finish_inv(void) {
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++) {
            if ((int)T[(size_t)x * N + y] == e_id) { INV[x] = y; break; }
        }
    }
}

/* Z_m x|_r Z_kk, element (a,b) coded as a*kk+b, (a,b)(c,d) = (a + r^b c, b + d). */
static int build_meta(int m, int kk, int r) {
    int n = m * kk;
    if (n > MAXN || n < 2) return 0;
    alloc_group(n);
    N = n;
    static int pw[MAXN];
    pw[0] = 1 % m;
    for (int b = 1; b < kk; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / kk, b = x % kk;
        for (int y = 0; y < N; y++) {
            int c = y / kk, dd = y % kk;
            int aa = (int)(((long)a + (long)pw[b] * c) % m);
            int bb = (b + dd) % kk;
            T[(size_t)x * N + y] = (uint16_t)(aa * kk + bb);
        }
    }
    e_id = 0;
    finish_inv();
    return 1;
}

/* SL(2,q) or PSL(2,q), q prime. */
static int qg, psl_g;
static int gmat[MAXN][4];
static int idxm[83521];   /* q^4 for q <= 17 */

static int canon_key(int a, int b, int c, int e) {
    int q = qg;
    int k = ((a * q + b) * q + c) * q + e;
    if (!psl_g) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}

static int build_matrix(int q, int psl) {
    qg = q;
    psl_g = psl;
    int ks = q * q * q * q;
    for (int i = 0; i < ks; i++) idxm[i] = -1;
    int cntg = 0;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int e = 0; e < q; e++) {
                    if ((((a * e - b * c) % q) + q) % q != 1) continue;
                    int own = ((a * q + b) * q + c) * q + e;
                    if (canon_key(a, b, c, e) != own) continue;
                    if (cntg >= MAXN) return 0;
                    gmat[cntg][0] = a;
                    gmat[cntg][1] = b;
                    gmat[cntg][2] = c;
                    gmat[cntg][3] = e;
                    idxm[own] = cntg;
                    cntg++;
                }
    N = cntg;
    alloc_group(N);
    for (int x = 0; x < N; x++) {
        int a = gmat[x][0], b = gmat[x][1], c = gmat[x][2], e = gmat[x][3];
        for (int y = 0; y < N; y++) {
            int a2 = gmat[y][0], b2 = gmat[y][1], c2 = gmat[y][2], e2 = gmat[y][3];
            int pa = (a * a2 + b * c2) % q;
            int pb = (a * b2 + b * e2) % q;
            int pc = (c * a2 + e * c2) % q;
            int pe = (c * b2 + e * e2) % q;
            T[(size_t)x * N + y] = (uint16_t)idxm[canon_key(pa, pb, pc, pe)];
        }
    }
    e_id = idxm[canon_key(1, 0, 0, 1)];
    finish_inv();
    return 1;
}

static int apply_cand(const Cand *c) {
    int ok = (c->type == 0) ? build_meta(c->m, c->kk, c->r) : build_matrix(c->q, c->psl);
    if (!ok) return 0;
    if (N != c->N) return 0;
    K = c->K;
    KN = K * N;
    NV = 2 * KN;
    if (K < 1 || K > MAXK || KN > MAXKN) return 0;
    return 1;
}

/* ------------------------------------------------------------------ candidates */

static const int MQ[9] = {5, 5, 7, 7, 11, 11, 13, 13, 17};
static const int MP[9] = {0, 1, 0, 1, 0, 1, 0, 1, 1};

static int matorder(int q, int psl) {
    long o = (long)q * ((long)q * q - 1);
    if (psl) o /= 2;
    return (int)o;
}

/* Add up to two metacyclic groups of order Nv, for base size Kv, with kN = v. */
static int add_meta(int Nv, int Kv, int v, Cand *out, int nc, int cap) {
    int got = 0;
    for (int kk = 2; kk <= Nv / 3 && nc < cap && got < 2; kk++) {
        if (Nv % kk) continue;
        int m = Nv / kk;
        if (m < 3) continue;
        for (int r = 2; r < m && got < 2 && nc < cap; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, kk, m) != 1) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 0;
            c.m = m;
            c.kk = kk;
            c.r = r;
            c.K = Kv;
            c.N = Nv;
            c.kN = v;
            out[nc++] = c;
            got++;
        }
    }
    return nc;
}

static int gather_v(Cand *out, int nc, int v, int cap) {
    if (2L * v > moore_g) return nc;
    for (int Kv = 1; Kv <= MAXK && nc < cap; Kv++) {
        if (v % Kv) continue;
        int Nv = v / Kv;
        if (Nv < 3 || Nv > MAXN) continue;
        for (int g = 0; g < 9 && nc < cap; g++) {
            if (matorder(MQ[g], MP[g]) != Nv) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 1;
            c.q = MQ[g];
            c.psl = MP[g];
            c.K = Kv;
            c.N = Nv;
            c.kN = v;
            out[nc++] = c;
        }
        nc = add_meta(Nv, Kv, v, out, nc, cap);
    }
    return nc;
}

static int cmp_kn(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    return (x->kN > y->kN) - (x->kN < y->kN);
}

/* ------------------------------------------------------------------ voltage state */

static void set_pair(int i, int j) {
    for (int t = 0; t < cnt[i][j]; t++) {
        int s = E[i][j][t], si = INV[s];
        for (int x = 0; x < N; x++) {
            RF[i][j][t][x] = (int)T[(size_t)x * N + s];
            RB[i][j][t][x] = (int)T[(size_t)x * N + si];
        }
    }
}

static int in_set(int x, const int *a, int c) {
    for (int t = 0; t < c; t++)
        if (a[t] == x) return 1;
    return 0;
}

/* Random group element not among the first c voltages of pair (i,j). */
static int fresh(int i, int j, int c) {
    int x;
    do x = rndint(N); while (in_set(x, E[i][j], c));
    return x;
}

/* Random count matrix with row and column sums d (greedy placement always succeeds),
   then random distinct voltages for each pair. */
static void randomize_state(void) {
    int colsum[MAXK];
    memset(cnt, 0, sizeof cnt);
    memset(colsum, 0, sizeof colsum);
    for (int i = 0; i < K; i++)
        for (int u = 0; u < d; u++) {
            int j;
            do j = rndint(K); while (colsum[j] >= d);
            cnt[i][j]++;
            colsum[j]++;
        }
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            for (int t = 0; t < cnt[i][j]; t++)
                E[i][j][t] = fresh(i, j, t);
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++) set_pair(i, j);
}

/* ------------------------------------------------------------------ BFS cost */

/* Number of vertices reached within D steps from vertex src. */
static int ball(int src) {
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
            if (v < KN) {
                int i = v / N, x = v - i * N;
                for (int j = 0; j < K; j++) {
                    int c = cnt[i][j];
                    for (int t = 0; t < c; t++) {
                        int u = KN + j * N + RF[i][j][t][x];
                        if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                    }
                }
            } else {
                int w = v - KN, j = w / N, y = w - j * N;
                for (int i = 0; i < K; i++) {
                    int c = cnt[i][j];
                    for (int t = 0; t < c; t++) {
                        int u = i * N + RB[i][j][t][y];
                        if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                    }
                }
            }
        }
    }
    return tail;
}

/* Total number of unreached (source, vertex) pairs over all 2K sources. 0 = valid. */
static long cost_now(void) {
    long c = 0;
    for (int i = 0; i < K; i++) c += (long)(NV - ball(i * N + e_id));
    for (int j = 0; j < K; j++) c += (long)(NV - ball(KN + j * N + e_id));
    return c;
}

/* Propose one move; store the old state in ucnt/uE and the touched pairs in aff. */
static void propose(void) {
    memcpy(ucnt, cnt, sizeof cnt);
    memcpy(uE, E, sizeof E);
    naff = 0;
    if (K == 1 || rnd01() < 0.5) {
        int i, j;
        do { i = rndint(K); j = rndint(K); } while (cnt[i][j] == 0);
        int t = rndint(cnt[i][j]);
        E[i][j][t] = fresh(i, j, cnt[i][j]);
        aff_i[0] = i;
        aff_j[0] = j;
        naff = 1;
        return;
    }
    /* cycle move: (i1,j1),(i2,j2) lose one dart; (i1,j2),(i2,j1) gain one */
    int i1 = 0, i2 = 0, j1 = 0, j2 = 0, ok = 0;
    for (int tries = 0; tries < 60 && !ok; tries++) {
        i1 = rndint(K);
        i2 = rndint(K);
        j1 = rndint(K);
        j2 = rndint(K);
        if (i1 != i2 && j1 != j2 && cnt[i1][j1] > 0 && cnt[i2][j2] > 0) ok = 1;
    }
    if (!ok) return;
    int t = rndint(cnt[i1][j1]);
    E[i1][j1][t] = E[i1][j1][cnt[i1][j1] - 1];
    cnt[i1][j1]--;
    t = rndint(cnt[i2][j2]);
    E[i2][j2][t] = E[i2][j2][cnt[i2][j2] - 1];
    cnt[i2][j2]--;
    E[i1][j2][cnt[i1][j2]] = fresh(i1, j2, cnt[i1][j2]);
    cnt[i1][j2]++;
    E[i2][j1][cnt[i2][j1]] = fresh(i2, j1, cnt[i2][j1]);
    cnt[i2][j1]++;
    aff_i[0] = i1; aff_j[0] = j1;
    aff_i[1] = i2; aff_j[1] = j2;
    aff_i[2] = i1; aff_j[2] = j2;
    aff_i[3] = i2; aff_j[3] = j1;
    naff = 4;
}

/* Simulated annealing with sawtooth reheating. Returns 1 and leaves a valid state in place. */
static int climb(double until) {
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    randomize_state();
    long cur = cost_now();
    long bestc = cur;
    memcpy(bcnt, cnt, sizeof cnt);
    memcpy(bE, E, sizeof E);
    double temp = T_HI;
    long it = 0;
    while (cur > 0) {
        if ((++it & 15) == 0) {
            double t = now();
            if (t >= until) break;
            double ph = (t - start) / span * CYCLES;
            ph -= floor(ph);
            temp = T_HI * pow(T_LO / T_HI, ph);
        }
        propose();
        for (int k = 0; k < naff; k++) set_pair(aff_i[k], aff_j[k]);
        long nc = cost_now();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                memcpy(bcnt, cnt, sizeof cnt);
                memcpy(bE, E, sizeof E);
            }
        } else {
            memcpy(cnt, ucnt, sizeof cnt);
            memcpy(E, uE, sizeof E);
            for (int k = 0; k < naff; k++) set_pair(aff_i[k], aff_j[k]);
        }
    }
    if (bestc != 0) return 0;
    memcpy(cnt, bcnt, sizeof cnt);
    memcpy(E, bE, sizeof E);
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++) set_pair(i, j);
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

    if (d < 1 || d > MAXD || D < 2) { print_complete(); return 0; }
    moore_g = moore_bound();

    int rec = (int)(ref / 2);          /* vertices per side to beat: 2*K*N > ref */
    int mainLo = rec + 1;
    int mainHi = rec + rec / 8 + 2;
    if (mainHi > MAXKN) mainHi = MAXKN;

    static Cand all[MAXCAND], fb[16];
    int nf = 0;
    for (int v = rec; v >= (rec * 3) / 4 && nf < 6; v--) nf = gather_v(fb, nf, v, 6);
    int na = 0;
    for (int i = 0; i < nf; i++) all[na++] = fb[i];
    for (int v = mainLo; v <= mainHi && na < 30; v++) na = gather_v(all, na, v, 30);
    if (na == 0) { print_complete(); return 0; }
    qsort(all, (size_t)na, sizeof(Cand), cmp_kn);

    double budget = t_end - now();
    double base = budget / (na * 6.0);
    if (base < 0.2) base = 0.2;

    int have = 0;
    long bestV = 0;
    Cand best;
    memset(&best, 0, sizeof best);
    static int sCnt[MAXK][MAXK];
    static int sE[MAXK][MAXK][MAXD];

    for (int round = 0; round < 6; round++) {
        for (int i = 0; i < na; i++) {
            double rem = t_end - now();
            if (rem < 0.1) break;
            Cand *c = &all[i];
            if (c->kN <= bestV) continue;
            if (!apply_cand(c)) continue;
            double slice = base * (double)(1 << round);
            if (c->kN <= rec) slice *= 4.0;   /* fallbacks get extra time */
            if (slice > rem) slice = rem;
            if (climb(now() + slice)) {
                have = 1;
                bestV = c->kN;
                best = *c;
                memcpy(sCnt, cnt, sizeof cnt);
                memcpy(sE, E, sizeof E);
            }
        }
        if (t_end - now() < 0.1) break;
    }

    if (!have) { print_complete(); return 0; }
    if (!apply_cand(&best)) { print_complete(); return 0; }
    memcpy(cnt, sCnt, sizeof cnt);
    memcpy(E, sE, sizeof E);
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++) set_pair(i, j);
    if (cost_now() != 0) { print_complete(); return 0; }

    printf("%d %d\n", NV, KN * d);
    for (int i = 0; i < K; i++)
        for (int x = 0; x < N; x++) {
            int A = i * N + x;
            for (int j = 0; j < K; j++)
                for (int t = 0; t < cnt[i][j]; t++)
                    printf("%d %d\n", A, KN + j * N + RF[i][j][t][x]);
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
    if best[0] >= lib.moore_bound(d, D):
        return best   # Moore graph: nothing can beat it
    budget = min(0.8 * time_limit, max(time_limit - 10.0, 0.6 * time_limit))
    budget -= time.monotonic() - t0
    if budget > 1.0:
        try:
            ref = REF_VERTICES.get((d, D), 4970)
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), ref],
                             timeout=budget + 4)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
