"""Program: two engines for the weakest target (d=4, D=9).

Engine A (PARENT_C): the previous bi-Cayley search over SL/PSL(2,q) and metacyclic
groups. It is kept as a safety net, so the record-matching graph is not lost.

Engine B (NEW_C): a different construction, a multi-orbit voltage lift. The graph has
2*B*N vertices, where Z = G is a metacyclic group of order N and B is the number of
orbits per side (B = 1..6). Each side-A orbit i sends d darts to side-B orbits
pk[k][i] (one permutation per dart index k), each with a group voltage S[i][k]:

    A_{i,g} ~ B_{pk[k][i], g*S[i][k]}   for k < d.

Every vertex has degree d and the graph is bipartite. Left multiplication by G is an
automorphism, so the diameter condition reduces to BFS from the 2B representatives
A_{i,e} and B_{j,e}. Hill climbing on the voltages minimises the number of unreached
pairs. The engine searches for any valid graph with more than the reference vertex
count, ordered from the smallest candidate size upwards.

Time: the target gets 40% of the budget for engine A and the rest for engine B.
Other cases use engine A only. Every output is checked with lib.is_valid, and the
best valid graph (or the K_{d,d} / Moore fallback) is returned.
"""
import time

import lib

PARENT_C = r'''
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
    double usable = limit - 1.0;
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
    int recN = recHalf + 1;   /* smallest N that beats the record vertex count */

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

    /* 2. metacyclic groups just below the record, descending (cheap wins first) */
    for (int Nv = recN - 1; Nv >= lowN; Nv--) add_meta(Nv, lo, &nl);
    /* 3. metacyclic groups beating the record, ascending (hard, last) */
    for (int Nv = recN; Nv <= hiN; Nv++) add_meta(Nv, hi, &nh);

    for (int i = 0; i < nl; i++) all[na++] = lo[i];
    for (int i = 0; i < nh; i++) all[na++] = hi[i];

    double budget0 = t_end - now();
    int have = 0;
    Cand best;
    memset(&best, 0, sizeof best);
    static int bS[MAXDEG];

    /* Iterative deepening: each round gives every still-improving candidate a slice,
       and the slice doubles per round. Matrix groups come first in every round. */
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

NEW_C = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2700
#define MAXB 6
#define MAXD 8
#define MAXVV (2 * MAXB * MAXN)
#define MAXCAND 160
#define SPAN 10
#define STALL 3000

typedef struct { int b, m, k, r, N, V; } Cand;
typedef struct { int m, k, r; } GDesc;

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

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

/* ------------------------------------------------------------------ group */

static uint16_t Tt[MAXN * MAXN];   /* Tt[x*N+y] = x*y */
static int INV[MAXN];
static int pw[MAXN];
static int N = 0;

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d). */
static int build_meta(int m, int k, int r) {
    int n = m * k;
    if (m < 2 || k < 1 || n < 2 || n > MAXN) return 0;
    N = n;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, bx = x % k;
        int aa = a;
        int step = pw[bx];
        for (int c = 0; c < m; c++) {
            int b2 = bx;
            for (int dd = 0; dd < k; dd++) {
                Tt[(size_t)x * N + (c * k + dd)] = (uint16_t)(aa * k + b2);
                b2++;
                if (b2 == k) b2 = 0;
            }
            aa += step;
            if (aa >= m) aa -= m;
        }
    }
    for (int x = 0; x < N; x++) {
        int a = x / k, bx = x % k;
        int nb = (k - bx) % k;
        int ia = (int)(((long)m - ((long)pw[nb] * a) % m) % m);
        INV[x] = ia * k + nb;
    }
    for (int x = 0; x < N; x++)
        if (Tt[(size_t)x * N + INV[x]] != 0) return 0;
    return 1;
}

static int enum_groups(int n, GDesc *out, int maxout) {
    int cnt = 0;
    for (int k = 1; k <= n / 2; k++) {
        if (n % k) continue;
        int m = n / k;
        if (m < 2) continue;
        for (int r = 1; r < m && cnt < maxout; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            out[cnt].m = m;
            out[cnt].k = k;
            out[cnt].r = r;
            cnt++;
        }
    }
    return cnt;
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
    if (x->b != y->b) return x->b - y->b;
    return 0;
}

static int make_cands(long thr, long moore, Cand *cs, int maxc) {
    static GDesc gd[64];
    int nc = 0;
    for (int b = 1; b <= MAXB; b++) {
        long Nlo = thr / (2L * b) + 1;     /* ensures 2*b*N > thr */
        for (long Nv = Nlo; Nv < Nlo + SPAN && Nv <= MAXN; Nv++) {
            long V = 2L * b * Nv;
            if (V > moore || V > MAXVV) break;
            int ng = enum_groups((int)Nv, gd, 64);
            for (int i = ng - 1; i > 0; i--) {
                int j = rndint(i + 1);
                GDesc t = gd[i];
                gd[i] = gd[j];
                gd[j] = t;
            }
            for (int g = 0; g < ng && g < 2 && nc < maxc; g++) {
                cs[nc].b = b;
                cs[nc].m = gd[g].m;
                cs[nc].k = gd[g].k;
                cs[nc].r = gd[g].r;
                cs[nc].N = (int)Nv;
                cs[nc].V = (int)V;
                nc++;
            }
        }
    }
    return nc;
}

/* ------------------------------------------------------------------ voltage lift */

static int B = 0, BN = 0, NV = 0;
static int pk[MAXD][MAXB];     /* pk[k][i]: B-orbit reached by dart k of A-orbit i */
static int pinv[MAXD][MAXB];   /* pinv[k][j]: A-orbit whose dart k lands in B-orbit j */
static int S[MAXB][MAXD];      /* voltage of dart (i,k) */

static void set_pinv(void) {
    for (int k = 0; k < d; k++)
        for (int i = 0; i < B; i++) pinv[k][pk[k][i]] = i;
}

static int conn_ok(void) {
    int seen[2 * MAXB];
    int stack[2 * MAXB];
    memset(seen, 0, sizeof seen);
    int sp = 0, cnt = 1;
    seen[0] = 1;
    stack[sp++] = 0;
    while (sp) {
        int v = stack[--sp];
        if (v < B) {
            for (int k = 0; k < d; k++) {
                int u = B + pk[k][v];
                if (!seen[u]) { seen[u] = 1; cnt++; stack[sp++] = u; }
            }
        } else {
            int j = v - B;
            for (int k = 0; k < d; k++) {
                int u = pinv[k][j];
                if (!seen[u]) { seen[u] = 1; cnt++; stack[sp++] = u; }
            }
        }
    }
    return cnt == 2 * B;
}

static int gen_perms(void) {
    for (int attempt = 0; attempt < 200; attempt++) {
        for (int k = 0; k < d; k++) {
            int p[MAXB];
            for (int i = 0; i < B; i++) p[i] = i;
            for (int i = B - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = p[i];
                p[i] = p[j];
                p[j] = t;
            }
            for (int i = 0; i < B; i++) pk[k][i] = p[i];
        }
        set_pinv();
        if (conn_ok()) return 1;
    }
    return 0;
}

/* Two darts from the same A-orbit into the same B-orbit need distinct voltages. */
static int conflicts(int i, int k, int s) {
    for (int k2 = 0; k2 < d; k2++)
        if (k2 != k && pk[k2][i] == pk[k][i] && S[i][k2] == s) return 1;
    return 0;
}

static int init_S(void) {
    for (int i = 0; i < B; i++)
        for (int k = 0; k < d; k++) S[i][k] = -1;
    for (int i = 0; i < B; i++)
        for (int k = 0; k < d; k++) {
            long tries = 0;
            int s;
            do {
                s = rndint(N);
                if (++tries > 200000) return 0;
            } while (conflicts(i, k, s));
            S[i][k] = s;
        }
    return 1;
}

static int valid_S(void) {
    for (int i = 0; i < B; i++)
        for (int k = 0; k < d; k++) {
            if (S[i][k] < 0 || S[i][k] >= N) return 0;
            if (conflicts(i, k, S[i][k])) return 0;
        }
    return 1;
}

/* ------------------------------------------------------------------ BFS cost */

/* Vertex ids: A_{i,g} = i*N + g (i < B), B_{j,h} = BN + j*N + h. */
static int stamp[MAXVV];
static int tickc = 0;
static int qv[MAXVV];

static int cover(int src) {
    if (++tickc == 0x7ffffff0) {
        memset(stamp, 0, sizeof stamp);
        tickc = 1;
    }
    int head = 0, tail = 0;
    stamp[src] = tickc;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < BN) {
                int i = v / N, g = v - i * N;
                const uint16_t *row = Tt + (size_t)g * N;
                for (int k = 0; k < d; k++) {
                    int u = BN + pk[k][i] * N + row[S[i][k]];
                    if (stamp[u] != tickc) { stamp[u] = tickc; qv[tail++] = u; }
                }
            } else {
                int w = v - BN;
                int j = w / N, h = w - j * N;
                const uint16_t *row = Tt + (size_t)h * N;
                for (int k = 0; k < d; k++) {
                    int i = pinv[k][j];
                    int g = row[INV[S[i][k]]];   /* g = h * s^{-1} */
                    int u = i * N + g;
                    if (stamp[u] != tickc) { stamp[u] = tickc; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left multiplication by G is an automorphism and is transitive on each orbit,
   so the diameter condition reduces to BFS from the 2B orbit representatives. */
static long cost_all(void) {
    long c = 0;
    for (int i = 0; i < B; i++) c += (long)(NV - cover(i * N));
    for (int j = 0; j < B; j++) c += (long)(NV - cover(BN + j * N));
    return c;
}

/* ------------------------------------------------------------------ search */

static int climb(double until) {
    if (!init_S()) return 0;
    long cur = cost_all(), best_c = cur, stall = 0;
    while (1) {
        if (cur == 0) return 1;
        if (now() > until) return 0;
        if (stall > STALL) {
            if (!init_S()) return 0;
            cur = cost_all();
            best_c = cur;
            stall = 0;
            continue;
        }
        int i = rndint(B), k = rndint(d), s = rndint(N);
        if (s == S[i][k] || conflicts(i, k, s)) { stall++; continue; }
        int old = S[i][k];
        S[i][k] = s;
        long nc = cost_all();
        if (nc <= cur || rnd01() < 0.01) cur = nc;
        else S[i][k] = old;
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
    }
}

static int setup_cand(const Cand *c) {
    if (!build_meta(c->m, c->k, c->r)) return 0;
    B = c->b;
    BN = B * N;
    NV = 2 * BN;
    if (NV > MAXVV) return 0;
    return gen_perms();
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
    static Cand cs[MAXCAND];
    int nc = make_cands(ref, moore, cs, MAXCAND);
    qsort(cs, (size_t)nc, sizeof(Cand), cmp_cand);

    long bestV = ref;
    int have = 0;
    Cand bestC;
    memset(&bestC, 0, sizeof bestC);
    static int bestPk[MAXD][MAXB];
    static int bestS[MAXB][MAXD];

    double base = (t_end - now()) * 0.012;
    if (base < 0.3) base = 0.3;
    for (int round = 0; round < 6; round++) {
        for (int i = 0; i < nc; i++) {
            double remain = t_end - now();
            if (remain < 0.2) break;
            if (cs[i].V <= bestV) continue;
            if (!setup_cand(&cs[i])) continue;
            double slice = base * (double)(1 << round);
            if (slice > remain) slice = remain;
            if (climb(now() + slice)) {
                have = 1;
                bestV = cs[i].V;
                bestC = cs[i];
                memcpy(bestPk, pk, sizeof pk);
                memcpy(bestS, S, sizeof S);
            }
        }
        if (t_end - now() < 0.2) break;
    }

    if (!have) { print_complete(); return 0; }
    if (!build_meta(bestC.m, bestC.k, bestC.r)) { print_complete(); return 0; }
    B = bestC.b;
    BN = B * N;
    NV = 2 * BN;
    memcpy(pk, bestPk, sizeof pk);
    set_pinv();
    memcpy(S, bestS, sizeof S);
    if (!valid_S() || cost_all() != 0) { print_complete(); return 0; }

    printf("%d %ld\n", NV, (long)BN * d);
    for (int i = 0; i < B; i++)
        for (int g = 0; g < N; g++)
            for (int k = 0; k < d; k++) {
                int u = i * N + g;
                int v = BN + pk[k][i] * N + Tt[(size_t)g * N + S[i][k]];
                printf("%d %d\n", u, v);
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
        return best                           # already optimal

    total = 0.85 * time_limit - 1.0
    ref = REF_VERTICES.get((d, D), 4970)
    if (d, D) in REF_VERTICES:
        plan = [(PARENT_C, 0.4), (NEW_C, 1.0)]   # safety net first, then the new construction
    else:
        plan = [(PARENT_C, 1.0)]

    for idx, (src, frac) in enumerate(plan):
        left = total - (time.monotonic() - t0)
        if idx == len(plan) - 1:
            budget = left
        else:
            budget = min(left, frac * total)
        if budget < 1.0:
            continue
        try:
            text = lib.run_c(src, [d, D, seed, round(budget, 2), ref], timeout=budget + 5)
            n, edges = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except Exception:
            pass   # keep the valid fallback
    return best
