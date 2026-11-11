"""Program: two-stage search for d=4, D=9.

Stage A: the bi-Cayley search over metacyclic and PSL/SL(2,q) groups (the parent engine). It gets
about 60% of the budget and usually secures the record 4970.

Stage B (new): take the stage-A graph and grow it one vertex pair at a time. Each growth step
removes a matching of d edges, attaches a new A vertex to the B endpoints and a new B vertex to the
A endpoints, which keeps every degree at d. Then simulated annealing with degree-preserving
2-switches repairs the diameter, with cost = number of ordered pairs at distance > D, computed by
bitset ball propagation. A snapshot is kept at every success, so the output is always a valid
graph, never worse than the input.

Other (d, D) cases use the parent engine unchanged. Every output is checked with lib.is_valid,
and the best valid graph is returned.
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

#define MAXN 3200
#define MAXV (2 * MAXN)
#define MAXDEG 8
#define MAXCAND 48

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

/* ------------------------------------------------------------------ group */

static int N = 0, e_id = 0;
static uint16_t *T = NULL;   /* T[x*N+y] = x*y */
static int *INV = NULL;      /* INV[x] = x^{-1} */

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

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d). */
static int build_meta(int m, int k, int r) {
    int n = m * k;
    if (n > MAXN || n < 2) return 0;
    N = n;
    alloc_group(N);
    static int pw[MAXN];
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, dd = y % k;
            int aa = (a + pw[b] * c) % m;
            int bb = (b + dd) % k;
            T[(size_t)x * N + y] = (uint16_t)(aa * k + bb);
        }
    }
    e_id = 0;
    finish_inv();
    return N;
}

/* PSL(2,q) or SL(2,q), q prime. */
static int qg, psl_g;
static int gmat[MAXN][4];
static int *idxm = NULL;
static int idxm_cap = 0;

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
    if (ks > idxm_cap) {
        free(idxm);
        idxm = malloc(sizeof(int) * (size_t)ks);
        idxm_cap = ks;
    }
    for (int i = 0; i < ks; i++) idxm[i] = -1;
    int cnt = 0;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int e = 0; e < q; e++) {
                    if ((((a * e - b * c) % q) + q) % q != 1) continue;
                    int own = ((a * q + b) * q + c) * q + e;
                    if (canon_key(a, b, c, e) != own) continue;
                    if (cnt >= MAXN) return 0;
                    gmat[cnt][0] = a;
                    gmat[cnt][1] = b;
                    gmat[cnt][2] = c;
                    gmat[cnt][3] = e;
                    idxm[own] = cnt;
                    cnt++;
                }
    N = cnt;
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
    return N;
}

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int type;   /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r, N;
    double frac;
} Cand;

static int apply_cand(const Cand *c) {
    if (c->type == 0) return build_meta(c->m, c->k, c->r);
    return build_matrix(c->q, c->psl);
}

static void add_meta(int Nval, Cand *arr, int *cnt) {
    for (int k = 2; k <= Nval / 3 && *cnt < MAXCAND; k++) {
        if (Nval % k) continue;
        int m = Nval / k;
        if (m < 3) continue;
        int got = 0;
        for (int r = 2; r < m && got < 2 && *cnt < MAXCAND; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 0;
            c.m = m;
            c.k = k;
            c.r = r;
            c.N = Nval;
            c.frac = 0.06;
            arr[(*cnt)++] = c;
            got++;
        }
    }
}

/* ------------------------------------------------------------------ connection set */

static int S[MAXDEG];
static int Rr[MAXDEG][MAXN];   /* Rr[k][x] = x * s_k */
static int Ri[MAXDEG][MAXN];   /* Ri[k][y] = y * s_k^{-1} */

static void set_col(int k) {
    int s = S[k], si = INV[s];
    for (int x = 0; x < N; x++) {
        Rr[k][x] = (int)T[(size_t)x * N + s];
        Ri[k][x] = (int)T[(size_t)x * N + si];
    }
}

static int in_S(int x, int m) {
    for (int k = 0; k < m; k++)
        if (S[k] == x) return 1;
    return 0;
}

/* ------------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

static int ball(int src, int dmax) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < N) {
                for (int k = 0; k < d; k++) {
                    int u = N + Rr[k][v];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int y = v - N;
                for (int k = 0; k < d; k++) {
                    int u = Ri[k][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

static long cost_now(void) {
    return (long)(2 * N - ball(e_id, D)) + (long)(2 * N - ball(N + e_id, D));
}

static void randomize_S(void) {
    for (int k = 0; k < d; k++) {
        int x;
        do x = rndint(N); while (in_S(x, k));
        S[k] = x;
    }
    for (int k = 0; k < d; k++) set_col(k);
}

static int climb(double until) {
    randomize_S();
    long cur = cost_now(), best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        if (stall > 4000) {
            randomize_S();
            cur = cost_now();
            best_c = cur;
            stall = 0;
            continue;
        }
        int k = rndint(d);
        int old = S[k];
        int x;
        do x = rndint(N); while (in_S(x, d));
        S[k] = x;
        set_col(k);
        long nc = cost_now();
        if (nc <= cur || rnd01() < 0.02) {
            cur = nc;
        } else {
            S[k] = old;
            set_col(k);
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
    double usable = limit - 1.5;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    long bestN = d;

    int recHalf = (int)(ref / 2);
    int lowN = (int)(0.87 * (double)recHalf);
    int hiN = (int)(1.13 * (double)recHalf);
    if (hiN > MAXN) hiN = MAXN;
    if (2L * hiN > moore) hiN = (int)(moore / 2);
    if (lowN < 3) lowN = 3;
    int recN = recHalf + 1;

    static Cand all[3 * MAXCAND + 32];
    static Cand hi[MAXCAND], lo[MAXCAND];
    int na = 0, nh = 0, nl = 0;

    /* 1. matrix groups in the window (known fallbacks) */
    static const int qs[] = {5, 7, 11, 13, 17, 19};
    for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++) {
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o < lowN || o > hiN || o > MAXN) continue;
            if (na >= 16) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 1;
            c.q = (int)q;
            c.psl = psl;
            c.N = (int)o;
            c.frac = 0.25;
            all[na++] = c;
        }
    }

    /* 2. metacyclic groups just below the record, descending */
    for (int Nv = recN - 1; Nv >= lowN; Nv--) add_meta(Nv, lo, &nl);
    /* 3. metacyclic groups beating the record, ascending */
    for (int Nv = recN; Nv <= hiN; Nv++) add_meta(Nv, hi, &nh);

    for (int i = 0; i < nl; i++) all[na++] = lo[i];
    for (int i = 0; i < nh; i++) all[na++] = hi[i];

    double budget0 = t_end - now();
    int have = 0;
    Cand best;
    memset(&best, 0, sizeof best);
    static int bS[MAXDEG];

    double base_slice = budget0 * 0.03;
    if (base_slice < 0.3) base_slice = 0.3;
    for (int round = 0; round < 8; round++) {
        for (int i = 0; i < na; i++) {
            double remaining = t_end - now();
            if (remaining < 0.2) break;
            Cand *c = &all[i];
            if ((long)c->N <= bestN) continue;
            if (2L * c->N > moore) continue;
            if (!apply_cand(c)) continue;
            double slice = base_slice * (double)(1 << round);
            if (slice > remaining) slice = remaining;
            if (climb(now() + slice)) {
                have = 1;
                bestN = N;
                best = *c;
                memcpy(bS, S, sizeof(int) * (size_t)d);
            }
        }
        if (t_end - now() < 0.2) break;
    }

    if (!have) { print_complete(); return 0; }
    if (!apply_cand(&best)) { print_complete(); return 0; }
    memcpy(S, bS, sizeof(int) * (size_t)d);
    for (int k = 0; k < d; k++) set_col(k);
    if (cost_now() != 0) { print_complete(); return 0; }

    printf("%d %ld\n", 2 * N, (long)N * d);
    for (int x = 0; x < N; x++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", x, N + Rr[k][x]);
    return 0;
}
'''

C_GROW_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXH 2800
#define MAXW ((2 * MAXH + 63) / 64)
#define MAXD 8

static int d, D;
static long moore;
static double t_end;
static int n;                  /* current per-side count */
static int adjA[MAXH][MAXD];   /* A index -> B indices */
static int adjB[MAXH][MAXD];   /* B index -> A indices */
static int snapA[MAXH][MAXD];
static int snapB[MAXH][MAXD];
static int snapN;
static int cntA[MAXH], cntB[MAXH];
static uint64_t BUF0[2 * MAXH][MAXW];
static uint64_t BUF1[2 * MAXH][MAXW];
static uint64_t (*cur)[MAXW] = BUF0;
static uint64_t (*nxt)[MAXW] = BUF1;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 0x2545F4914F6CDD1DULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long moore_bound(void) {
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* Number of ordered pairs (x,y) with dist(x,y) > D. Zero iff the graph is valid. */
static long cost(void) {
    int nw = (MAXH + n + 63) / 64;
    for (int i = 0; i < n; i++) {
        memset(cur[i], 0, sizeof(uint64_t) * (size_t)nw);
        cur[i][i >> 6] |= 1ULL << (i & 63);
    }
    for (int j = 0; j < n; j++) {
        int id = MAXH + j;
        memset(cur[id], 0, sizeof(uint64_t) * (size_t)nw);
        cur[id][id >> 6] |= 1ULL << (id & 63);
    }
    for (int s = 0; s < D; s++) {
        for (int i = 0; i < n; i++) {
            uint64_t *o = nxt[i];
            memcpy(o, cur[i], sizeof(uint64_t) * (size_t)nw);
            for (int k = 0; k < d; k++) {
                const uint64_t *r = cur[MAXH + adjA[i][k]];
                for (int w = 0; w < nw; w++) o[w] |= r[w];
            }
        }
        for (int j = 0; j < n; j++) {
            int id = MAXH + j;
            uint64_t *o = nxt[id];
            memcpy(o, cur[id], sizeof(uint64_t) * (size_t)nw);
            for (int k = 0; k < d; k++) {
                const uint64_t *r = cur[adjB[j][k]];
                for (int w = 0; w < nw; w++) o[w] |= r[w];
            }
        }
        uint64_t (*tmp)[MAXW] = cur;
        cur = nxt;
        nxt = tmp;
    }
    long miss = 0;
    long full = 2L * n;
    for (int i = 0; i < n; i++) {
        long c = 0;
        for (int w = 0; w < nw; w++) c += pc64(cur[i][w]);
        miss += full - c;
    }
    for (int j = 0; j < n; j++) {
        int id = MAXH + j;
        long c = 0;
        for (int w = 0; w < nw; w++) c += pc64(cur[id][w]);
        miss += full - c;
    }
    return miss;
}

static int has_nb(const int *list, int target) {
    for (int k = 0; k < d; k++)
        if (list[k] == target) return 1;
    return 0;
}

static int find_pos(const int *list, int target) {
    for (int k = 0; k < d; k++)
        if (list[k] == target) return k;
    return -1;
}

/* Degree-preserving 2-switch: (i,b1),(i2,b2) -> (i,b2),(i2,b1). */
static int pi, pka, pi2, pka2, pb1, pb2, pj1, pj2;

static int propose(void) {
    for (int tr = 0; tr < 64; tr++) {
        int i = rndint(n), i2 = rndint(n);
        if (i == i2) continue;
        int ka = rndint(d), ka2 = rndint(d);
        int b1 = adjA[i][ka], b2 = adjA[i2][ka2];
        if (b1 == b2) continue;
        if (has_nb(adjA[i], b2) || has_nb(adjA[i2], b1)) continue;
        int j1 = find_pos(adjB[b1], i), j2 = find_pos(adjB[b2], i2);
        if (j1 < 0 || j2 < 0) continue;
        pi = i; pka = ka; pi2 = i2; pka2 = ka2;
        pb1 = b1; pb2 = b2; pj1 = j1; pj2 = j2;
        adjA[i][ka] = b2;
        adjB[b2][j2] = i;
        adjA[i2][ka2] = b1;
        adjB[b1][j1] = i2;
        return 1;
    }
    return 0;
}

static void undo(void) {
    adjA[pi][pka] = pb1;
    adjB[pb1][pj1] = pi;
    adjA[pi2][pka2] = pb2;
    adjB[pb2][pj2] = pi2;
}

/* Add one vertex per side: remove a matching of d edges (a_t,b_t), join new A to all b_t
   and new B to all a_t. Every degree stays d. */
static int grow(void) {
    if (n + 1 > MAXH || 2L * (n + 1) > moore) return 0;
    int as[MAXD], ks[MAXD], bs[MAXD], js[MAXD];
    for (int t = 0; t < d; t++) {
        int ok = 0;
        for (int tr = 0; tr < 400 && !ok; tr++) {
            int a = rndint(n), k = rndint(d), b = adjA[a][k];
            int dup = 0;
            for (int s = 0; s < t; s++)
                if (as[s] == a || bs[s] == b) { dup = 1; break; }
            if (dup) continue;
            as[t] = a;
            ks[t] = k;
            bs[t] = b;
            ok = 1;
        }
        if (!ok) return 0;
        js[t] = find_pos(adjB[bs[t]], as[t]);
        if (js[t] < 0) return 0;
    }
    int nb = n;
    for (int t = 0; t < d; t++) {
        adjA[as[t]][ks[t]] = nb;
        adjB[bs[t]][js[t]] = nb;
        adjA[nb][t] = bs[t];
        adjB[nb][t] = as[t];
    }
    n++;
    return 1;
}

static void save_snap(void) {
    memcpy(snapA, adjA, sizeof adjA);
    memcpy(snapB, adjB, sizeof adjB);
    snapN = n;
}

static void load_snap(void) {
    memcpy(adjA, snapA, sizeof adjA);
    memcpy(adjB, snapB, sizeof adjB);
    n = snapN;
}

/* Simulated annealing on the number of bad pairs until valid or until 'until'. */
static int repair(double until) {
    double t_start = now();
    double span = until - t_start;
    if (span < 1e-3) span = 1e-3;
    long c = cost();
    while (c > 0) {
        double tn = now();
        if (tn >= until) return 0;
        double frac = (tn - t_start) / span;
        double T = 3.0 - 2.5 * frac;
        if (T < 0.3) T = 0.3;
        if (!propose()) continue;
        long nc = cost();
        long delta = nc - c;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) c = nc;
        else undo();
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int total = 0, m = 0;
    if (scanf("%d %d", &total, &m) != 2 || total < 2 || (total % 2) || total / 2 >= MAXH) {
        printf("0 0\n");
        return 0;
    }
    int h = total / 2;
    if (m != h * d) { printf("0 0\n"); return 0; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        int a, b;
        if (u < h && v >= h) { a = u; b = v - h; }
        else if (v < h && u >= h) { a = v; b = u - h; }
        else { printf("0 0\n"); return 0; }
        if (cntA[a] >= d || cntB[b] >= d) { printf("0 0\n"); return 0; }
        adjA[a][cntA[a]++] = b;
        adjB[b][cntB[b]++] = a;
    }
    for (int i = 0; i < h; i++)
        if (cntA[i] != d || cntB[i] != d) { printf("0 0\n"); return 0; }
    for (int i = 0; i < h; i++)
        for (int k = 0; k < d; k++)
            for (int l = 0; l < k; l++)
                if (adjA[i][k] == adjA[i][l]) { printf("0 0\n"); return 0; }

    n = h;
    moore = moore_bound();
    if (cost() != 0) { printf("0 0\n"); return 0; }
    save_snap();

    int gfail = 0;
    while (now() < t_end) {
        if (!grow()) {
            if (++gfail > 30) break;
            continue;
        }
        double remain = t_end - now();
        if (remain <= 0.05) break;
        double slice = remain * 0.35;
        if (repair(now() + slice)) save_snap();
        else load_snap();
        gfail = 0;
    }

    printf("%d %d\n", 2 * snapN, snapN * d);
    for (int a = 0; a < snapN; a++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", a, snapN + snapA[a][k]);
    return 0;
}
'''

REF_VERTICES = {(4, 9): 4970}
GROW_TARGETS = {(4, 9)}


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def is_regular_bipartite(n, edges, d):
    """True if every vertex has degree d and every edge joins 0..n/2-1 to n/2..n-1."""
    if n % 2:
        return False
    h = n // 2
    deg = [0] * n
    for u, v in edges:
        if (u < h) == (v < h):
            return False
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


def _improve(d, D, text, best):
    """Return the parsed C output if it is a valid, larger graph; otherwise keep best."""
    try:
        out = lib.parse_graph_text(text)
    except Exception:
        return best
    if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
        return out
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    if start is None or not lib.is_valid(start[0], start[1], d, D):
        start = lib.haar_graph(d, range(d))   # K_{d,d}: always valid for D >= 2
    best = start
    total = 0.92 * time_limit - 1.0
    if best[0] >= lib.moore_bound(d, D):
        total = min(total, 0.5)               # nothing beats a Moore graph
    grow = (d, D) in GROW_TARGETS

    def left():
        return total - (time.monotonic() - t0)

    # Stage A: group-based search (parent engine). Full budget for non-target cases.
    budget_a = left() * (0.6 if grow else 1.0)
    if budget_a > 0.2:
        try:
            ref = REF_VERTICES.get((d, D), 4970)
            text = lib.run_c(C_SOURCE, [d, D, seed, budget_a, ref], timeout=budget_a + 5)
            best = _improve(d, D, text, best)
        except Exception:
            pass   # keep the valid fallback

    # Stage B: grow the stage-A graph by vertex pairs and repair with annealing.
    if grow and left() > 2.0 and is_regular_bipartite(best[0], best[1], d):
        budget_b = left() - 1.0
        try:
            text = lib.run_c(C_GROW_SOURCE, [d, D, seed, budget_b],
                             stdin_graph=best, timeout=budget_b + 5)
            best = _improve(d, D, text, best)
        except Exception:
            pass   # keep the valid fallback

    return best
