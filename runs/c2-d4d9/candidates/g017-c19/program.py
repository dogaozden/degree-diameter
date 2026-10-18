"""Program: two-stage search for graphs that beat the record vertex count.

Stage 1 (new construction): voltage lifts of small d-regular bipartite base multigraphs with
p vertices per side. Each base dart carries a voltage in a metacyclic group G of order N, so
the lift has 2pN vertices. Left multiplication by G is an automorphism, so validity needs only
2p BFS runs (one per base vertex, source at the identity). Simulated annealing with sawtooth
reheating searches the voltages. Candidates are tried in ascending order of vertex count.

Stage 2 (parent, kept as the safe fallback): bi-Cayley search over metacyclic and matrix groups
(g007-c25 engine, unchanged).

Safety: every C result is checked with lib.is_valid. The best valid graph is kept, falling back
to the known start or K_{d,d}.
"""
import time

import lib

C_LIFT = r'''
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
#define MAXV (2 * MAXP * MAXN)
#define MAXCAND 256
#define T_HI 6.0
#define T_LO 0.1
#define CYCLES 3.0
#define DUPPEN 100000L

static int d, D;
static long moore;

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

/* ------------------------------------------------------------ group table */

static int N = 0, e_id = 0;
static uint16_t Tbuf[MAXN * MAXN];   /* Tbuf[x*N+y] = x*y */
static int Ibuf[MAXN];               /* inverses */
static int pwv[MAXN];
static int ya[MAXN], yb[MAXN];

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d). Identity is 0. */
static int build_meta(int m, int k, int r) {
    long nl = (long)m * k;
    if (nl > MAXN || nl < 2) return 0;
    int n = (int)nl;
    N = n;
    e_id = 0;
    pwv[0] = 1 % m;
    for (int b = 1; b < k; b++) pwv[b] = (int)((long)pwv[b - 1] * r % m);
    for (int y = 0; y < n; y++) { ya[y] = y / k; yb[y] = y % k; }
    for (int x = 0; x < n; x++) {
        int a = x / k, b = x % k;
        uint16_t *row = &Tbuf[(size_t)x * n];
        for (int y = 0; y < n; y++) {
            int c = ya[y], dd = yb[y];
            int aa = (a + pwv[b] * c) % m;
            int bb = (b + dd) % k;
            row[y] = (uint16_t)(aa * k + bb);
        }
    }
    for (int x = 0; x < n; x++) {
        Ibuf[x] = -1;
        for (int y = 0; y < n; y++)
            if (Tbuf[(size_t)x * n + y] == 0) { Ibuf[x] = y; break; }
        if (Ibuf[x] < 0) return 0;
    }
    return 1;
}

/* ------------------------------------------------------------ candidates */

typedef struct { int p, m, k, r, gn, V; } Cand;
static Cand cands[MAXCAND];
static int ncand = 0;

static void push_cand(int p, int m, int k, int r) {
    if (ncand >= MAXCAND) return;
    Cand c;
    c.p = p; c.m = m; c.k = k; c.r = r;
    c.gn = m * k;
    c.V = 2 * p * c.gn;
    cands[ncand++] = c;
}

/* Up to 3 groups of order Nv per base size p: one semidirect product per k (nontrivial r if any). */
static void gen_for_order(int p, int Nv) {
    int got = 0;
    for (int k = 1; k <= Nv && got < 3; k++) {
        if (Nv % k) continue;
        int m = Nv / k;
        if (m < 2 || (k >= 2 && m < 3)) continue;
        int rr = -1;
        for (int r = 2; r < m; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1 % m) continue;
            rr = r;
            break;
        }
        if (rr < 0) rr = 1;
        push_cand(p, m, k, rr);
        got++;
    }
}

static void gen_all(long refv) {
    ncand = 0;
    for (int p = 1; p <= MAXP; p++) {
        long nmin = refv / (2L * p) + 1;   /* 2*p*N > refv */
        if (nmin < 3) nmin = 3;
        for (long Nv = nmin; Nv < nmin + 4 && Nv <= MAXN; Nv++) {
            if (2L * p * Nv > moore) break;
            gen_for_order(p, (int)Nv);
        }
    }
    for (int i = 1; i < ncand; i++) {
        Cand c = cands[i];
        int j = i - 1;
        while (j >= 0 && cands[j].V > c.V) { cands[j + 1] = cands[j]; j--; }
        cands[j + 1] = c;
    }
}

/* ------------------------------------------------------------ lift state */

static int P = 1;                      /* base vertices per side */
static int sig[MAXD][MAXP];            /* dart k from A_i goes to B_{sig[k][i]} */
static int sinv[MAXD][MAXP];           /* sinv[k][j] = i with sig[k][i] = j */
static int G[MAXP][MAXD];              /* voltage of dart (i,k) */
static int Fc[MAXP][MAXD][MAXN];       /* Fc[i][k][x] = x * g */
static int Bc[MAXP][MAXD][MAXN];       /* Bc[i][k][y] = y * g^{-1} */
static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];
static int bestG[MAXP][MAXD];

static void set_dart(int i, int k) {
    int g = G[i][k], gi = Ibuf[g];
    for (int x = 0; x < N; x++) {
        Fc[i][k][x] = (int)Tbuf[(size_t)x * N + g];
        Bc[i][k][x] = (int)Tbuf[(size_t)x * N + gi];
    }
}

static void set_all(void) {
    for (int i = 0; i < P; i++)
        for (int k = 0; k < d; k++) set_dart(i, k);
}

static void set_sinv(void) {
    for (int k = 0; k < d; k++)
        for (int i = 0; i < P; i++) sinv[k][sig[k][i]] = i;
}

static int uf_find(int *par, int x) {
    while (par[x] != x) { par[x] = par[par[x]]; x = par[x]; }
    return x;
}

static int connected(void) {
    int par[2 * MAXP];
    for (int v = 0; v < 2 * P; v++) par[v] = v;
    for (int k = 0; k < d; k++)
        for (int i = 0; i < P; i++) {
            int a = uf_find(par, i), b = uf_find(par, P + sig[k][i]);
            if (a != b) par[a] = b;
        }
    int r = uf_find(par, 0);
    for (int v = 1; v < 2 * P; v++)
        if (uf_find(par, v) != r) return 0;
    return 1;
}

static int randomize(void) {
    int ok = 0;
    for (int tries = 0; tries < 200 && !ok; tries++) {
        for (int k = 0; k < d; k++) {
            int perm[MAXP];
            for (int i = 0; i < P; i++) perm[i] = i;
            for (int i = P - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
            }
            for (int i = 0; i < P; i++) sig[k][i] = perm[i];
        }
        ok = connected();
    }
    if (!ok) return 0;
    set_sinv();
    for (int i = 0; i < P; i++)
        for (int k = 0; k < d; k++) G[i][k] = rndint(N);
    set_all();
    return 1;
}

/* Number of vertices within distance D of src (src is a left-orbit representative). */
static int ball(int src) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int PN = P * N;
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < PN) {
                int i = v / N, x = v - i * N;
                for (int k = 0; k < d; k++) {
                    int u = PN + sig[k][i] * N + Fc[i][k][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - PN, j = w / N, y = w - j * N;
                for (int k = 0; k < d; k++) {
                    int i2 = sinv[k][j];
                    int u = i2 * N + Bc[i2][k][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached (source, vertex) pairs over the 2P orbit representatives, plus duplicate-dart penalty. */
static long cost_now(void) {
    long c = 0;
    for (int i = 0; i < P; i++)
        for (int k = 0; k < d; k++)
            for (int l = k + 1; l < d; l++)
                if (sig[k][i] == sig[l][i] && G[i][k] == G[i][l]) c += DUPPEN;
    long V = 2L * P * N;
    for (int i = 0; i < P; i++) c += V - ball(i * N + e_id);
    for (int j = 0; j < P; j++) c += V - ball(P * N + j * N + e_id);
    return c;
}

static int climb(double until) {
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    if (!randomize()) return 0;
    long cur = cost_now();
    long bestc = cur;
    memcpy(bestG, G, sizeof G);
    double temp = T_HI;
    long it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0) {
            double t = now();
            if (t >= until) break;
            double f = (t - start) / span;
            double ph = f * CYCLES;
            ph = ph - floor(ph);
            temp = T_HI * pow(T_LO / T_HI, ph);
        }
        int i = rndint(P), k = rndint(d);
        int old = G[i][k];
        int ng = rndint(N);
        if (ng == old) continue;
        G[i][k] = ng;
        set_dart(i, k);
        long nc = cost_now();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                memcpy(bestG, G, sizeof G);
            }
        } else {
            G[i][k] = old;
            set_dart(i, k);
        }
    }
    if (bestc != 0) return 0;
    memcpy(G, bestG, sizeof G);
    set_all();
    return 1;
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
    long ref = argc > 5 ? atol(argv[5]) : 0;

    double t0 = now();
    double usable = limit - 0.5;
    if (usable < limit * 0.5) usable = limit * 0.5;
    double t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { print_complete(); return 0; }

    moore = moore_bound();
    long refv = ref > 0 ? ref : 2L * d;
    gen_all(refv);
    if (ncand == 0) { print_complete(); return 0; }

    double budget0 = t_end - now();
    double base = budget0 * 0.02;
    if (base < 0.2) base = 0.2;

    long bestV = refv;
    int have = 0, bestIdx = -1, sP = 1;
    static int sSig[MAXD][MAXP];
    static int sG[MAXP][MAXD];

    for (int round = 0; round < 8; round++) {
        for (int i = 0; i < ncand; i++) {
            double remaining = t_end - now();
            if (remaining < 0.2) break;
            Cand *c = &cands[i];
            if (c->V <= bestV) continue;
            if (!build_meta(c->m, c->k, c->r)) continue;
            if (N != c->gn) continue;
            P = c->p;
            double slice = base * (double)(1 << round);
            if (slice > remaining) slice = remaining;
            if (climb(now() + slice)) {
                have = 1;
                bestV = c->V;
                bestIdx = i;
                memcpy(sSig, sig, sizeof sig);
                memcpy(sG, G, sizeof G);
                sP = P;
            }
        }
        if (t_end - now() < 0.2) break;
    }

    if (!have) { print_complete(); return 0; }
    Cand *c = &cands[bestIdx];
    if (!build_meta(c->m, c->k, c->r) || N != c->gn) { print_complete(); return 0; }
    P = sP;
    memcpy(sig, sSig, sizeof sig);
    memcpy(G, sG, sizeof G);
    set_sinv();
    set_all();
    if (cost_now() != 0) { print_complete(); return 0; }

    printf("%ld %ld\n", 2L * P * N, (long)P * N * d);
    for (int i = 0; i < P; i++)
        for (int x = 0; x < N; x++)
            for (int k = 0; k < d; k++)
                printf("%d %d\n", i * N + x, P * N + sig[k][i] * N + Fc[i][k][x]);
    return 0;
}
'''

C_BICAYLEY = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 3200
#define MAXV (2 * MAXN)
#define MAXDEG 8
#define MAXCAND 48

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

/* SL(2,q) or PSL(2,q), q prime. */
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

/* Number of vertices not reached within D from A_e and from B_e (0 = valid). */
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

/* Simulated annealing with sawtooth reheating. Returns 1 and leaves the best valid S in place. */
static int climb(double until) {
    if (N <= d + 1) return 0;
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    randomize_S();
    long cur = cost_now();
    long bestc = cur;
    static int bestS[MAXDEG];
    memcpy(bestS, S, sizeof(int) * (size_t)d);
    double temp = T_HI;
    long it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0) {
            double t = now();
            if (t >= until) break;
            double f = (t - start) / span;
            double ph = f * CYCLES;
            ph = ph - floor(ph);
            temp = T_HI * pow(T_LO / T_HI, ph);
        }
        int k = rndint(d);
        int old = S[k];
        int x;
        do x = rndint(N); while (in_S(x, d));
        S[k] = x;
        set_col(k);
        long nc = cost_now();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                memcpy(bestS, S, sizeof(int) * (size_t)d);
            }
        } else {
            S[k] = old;
            set_col(k);
        }
    }
    if (bestc != 0) return 0;
    memcpy(S, bestS, sizeof(int) * (size_t)d);
    for (int k = 0; k < d; k++) set_col(k);
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
    int recN = recHalf + 1;

    static Cand all[3 * MAXCAND + 32];
    static Cand hi[MAXCAND], lo[MAXCAND];
    int na = 0, nh = 0, nl = 0;

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

    for (int Nv = recN - 1; Nv >= lowN; Nv--) add_meta(Nv, lo, &nl);
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

REF_VERTICES = {(4, 9): 4970}


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def _better(best, cand, d, D):
    """Return cand if it is a valid graph with more vertices than best, else best."""
    if cand is None or cand[0] <= best[0]:
        return best
    if lib.is_valid(cand[0], cand[1], d, D):
        return cand
    return best


def _run(source, args, budget):
    """Run a C engine; return (n, edges) or None on any failure."""
    try:
        text = lib.run_c(source, args, timeout=budget + 6.0)
        return lib.parse_graph_text(text)
    except Exception:
        return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    if start is None or not lib.is_valid(start[0], start[1], d, D):
        start = lib.haar_graph(d, range(d))   # K_{d,d}: always valid for D >= 2
    best = start
    if best[0] >= lib.moore_bound(d, D):
        return best   # Moore graph: nothing can beat it

    total = 0.85 * time_limit - 1.5 - (time.monotonic() - t0)
    if total < 2.0:
        return best

    ref = REF_VERTICES.get((d, D), best[0])
    lift_budget = 0.55 * total
    par_budget = total - lift_budget - 0.5

    # Stage 1: voltage lifts of small base multigraphs over metacyclic groups.
    lift = _run(C_LIFT, [d, D, int(seed), round(lift_budget, 3), ref], lift_budget)
    best = _better(best, lift, d, D)
    if best[0] > ref:
        return best

    # Stage 2: bi-Cayley search (safe fallback that reaches the known record).
    if par_budget > 1.0:
        par = _run(C_BICAYLEY, [d, D, int(seed), round(par_budget + 1.0, 3), ref], par_budget)
        best = _better(best, par, d, D)
    return best
