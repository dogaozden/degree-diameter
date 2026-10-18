"""Program: bi-Cayley search over a wider family of groups, with simulated annealing.

Construction:
  * Group G of order N, given by a full multiplication table (N <= 3200). Bi-Cayley graph:
    A_x is joined to B_{x*s_k} for k < d. The graph is d-regular and bipartite on 2N vertices.
  * Left multiplication is an automorphism, so diameter <= D holds iff BFS from A_e and from
    B_e both reach all 2N vertices within D steps.

New in this version:
  * Permutation-group closure helper. Given generators as permutations, it builds the group by
    BFS over right multiplications, then fills the full table in O(N^2) using the rule
    x*(p*g_j) = (x*p)*g_j. This gives groups the metacyclic family cannot: A4, S4, A5, S5, A6.
  * Direct products of a base group with a cyclic group or a dihedral group, and of two base
    groups. Orders near 2486..2808 include A5 x Z_21 (order 2520), S4 x Z_105, PSL(2,7) x Z_15,
    A7-sized and mixed products. These are scheduled alongside the metacyclic groups.
  * Matrix groups SL/PSL(2,q) also serve as direct-product factors (for example PSL(2,11) x Z_4).
  * Abelian and cyclic groups are dropped, since their bi-Cayley balls grow too slowly.
  * Two-phase schedule. Phase 1 looks for a fallback just below the record with a short slice
    per candidate. Phase 2 tries candidates that beat the record in ascending order of order,
    with doubling slices across rounds.

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
#define MAXV (2 * MAXN)
#define MAXDEG 8
#define DEGP 32
#define NGEN_MAX 4
#define HSZ 16384
#define RAWMAX 40000
#define MAXHI 200
#define MAXLO 80

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

/* ------------------------------------------------------------ group tables */

typedef struct { int n, e; uint16_t *t; } Grp;   /* t[x*n+y] = x*y, identity index e */

static Grp grp_empty(void) { Grp g; g.n = 0; g.e = 0; g.t = NULL; return g; }

static void grp_free(Grp *g) { free(g->t); g->t = NULL; g->n = 0; g->e = 0; }

static Grp grp_alloc(int n) {
    Grp g;
    g.n = n;
    g.e = 0;
    g.t = malloc(sizeof(uint16_t) * (size_t)n * (size_t)n);
    if (!g.t) g.n = 0;
    return g;
}

/* installed group (global) */
static uint16_t *T = NULL;
static int *INV = NULL;
static int N = 0, e_id = 0;

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d). */
static Grp grp_meta(int m, int k, int r) {
    if (m < 1 || k < 1) return grp_empty();
    long nl = (long)m * k;
    if (nl < 2 || nl > MAXN) return grp_empty();
    int n = (int)nl;
    Grp g = grp_alloc(n);
    if (!g.t) return g;
    static int pw[MAXN];
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    for (int x = 0; x < n; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < n; y++) {
            int c = y / k, dd = y % k;
            int aa = (a + (int)((long)pw[b] * c % m)) % m;
            int bb = (b + dd) % k;
            g.t[(size_t)x * n + y] = (uint16_t)(aa * k + bb);
        }
    }
    g.e = 0;
    return g;
}

/* Direct product: element (g,h) coded as g*nb+h. */
static Grp grp_direct(const Grp *a, const Grp *b) {
    if (a->n < 1 || b->n < 1 || !a->t || !b->t) return grp_empty();
    long nl = (long)a->n * b->n;
    if (nl > MAXN) return grp_empty();
    int n = (int)nl;
    Grp g = grp_alloc(n);
    if (!g.t) return g;
    int na = a->n, nb = b->n;
    for (int x1 = 0; x1 < na; x1++)
        for (int h1 = 0; h1 < nb; h1++) {
            size_t row = (size_t)(x1 * nb + h1) * (size_t)n;
            for (int x2 = 0; x2 < na; x2++) {
                int ga = a->t[(size_t)x1 * na + x2];
                for (int h2 = 0; h2 < nb; h2++) {
                    int hb = b->t[(size_t)h1 * nb + h2];
                    g.t[row + (size_t)(x2 * nb + h2)] = (uint16_t)(ga * nb + hb);
                }
            }
        }
    g.e = a->e * nb + b->e;
    return g;
}

/* ------------------------------------ permutation groups (closure helper) */

static int pdeg;
static uint8_t elems[MAXN][DEGP];
static int hslot[HSZ];

static uint32_t phash(const uint8_t *p) {
    uint32_t h = 2166136261u;
    for (int i = 0; i < pdeg; i++) { h ^= p[i]; h *= 16777619u; }
    return h;
}

static int hfind(const uint8_t *p) {
    uint32_t h = phash(p) & (HSZ - 1);
    while (hslot[h]) {
        int idx = hslot[h] - 1;
        if (memcmp(elems[idx], p, (size_t)pdeg) == 0) return idx;
        h = (h + 1) & (HSZ - 1);
    }
    return -1;
}

static void hput(const uint8_t *p, int idx) {
    uint32_t h = phash(p) & (HSZ - 1);
    while (hslot[h]) h = (h + 1) & (HSZ - 1);
    hslot[h] = idx + 1;
}

/* out = p composed with q, i.e. out[t] = p[q[t]] */
static void pmul(const uint8_t *p, const uint8_t *q, uint8_t *out) {
    for (int t = 0; t < pdeg; t++) out[t] = p[q[t]];
}

/* Group generated by ng permutations of degree deg. BFS gives a spanning tree
   (par, pgen). Right multiplication tables R[j][x] = x*g_j, and every element y
   satisfies y = elems[par[y]] * g_{pgen[y]}, so T[x][y] = R[pgen[y]][T[x][par[y]]]. */
static Grp grp_perm(int deg, int ng, uint8_t gens[][DEGP]) {
    if (deg < 1 || deg > DEGP || ng < 1 || ng > NGEN_MAX) return grp_empty();
    pdeg = deg;
    memset(hslot, 0, sizeof hslot);
    static int par[MAXN], pgen[MAXN];
    static int R[NGEN_MAX][MAXN];
    uint8_t tmp[DEGP];
    for (int t = 0; t < deg; t++) elems[0][t] = (uint8_t)t;
    hput(elems[0], 0);
    par[0] = -1;
    pgen[0] = -1;
    int cnt = 1;
    for (int i = 0; i < cnt; i++) {
        for (int j = 0; j < ng; j++) {
            pmul(elems[i], gens[j], tmp);
            if (hfind(tmp) >= 0) continue;
            if (cnt >= MAXN) return grp_empty();
            memcpy(elems[cnt], tmp, (size_t)deg);
            hput(tmp, cnt);
            par[cnt] = i;
            pgen[cnt] = j;
            cnt++;
        }
    }
    for (int j = 0; j < ng; j++)
        for (int x = 0; x < cnt; x++) {
            pmul(elems[x], gens[j], tmp);
            int idx = hfind(tmp);
            if (idx < 0) return grp_empty();
            R[j][x] = idx;
        }
    Grp g = grp_alloc(cnt);
    if (!g.t) return g;
    for (int x = 0; x < cnt; x++) g.t[(size_t)x * cnt] = (uint16_t)x;
    for (int y = 1; y < cnt; y++) {
        int p = par[y], j = pgen[y];
        for (int x = 0; x < cnt; x++) {
            int xp = g.t[(size_t)x * cnt + p];
            g.t[(size_t)x * cnt + y] = (uint16_t)R[j][xp];
        }
    }
    g.e = 0;
    return g;
}

static Grp perm_from_flat(int deg, int ng, const int *flat) {
    uint8_t gens[NGEN_MAX][DEGP];
    if (deg < 1 || deg > DEGP || ng < 1 || ng > NGEN_MAX) return grp_empty();
    for (int j = 0; j < ng; j++)
        for (int t = 0; t < deg; t++) gens[j][t] = (uint8_t)flat[j * deg + t];
    return grp_perm(deg, ng, gens);
}

/* ------------------------------------------------------- SL/PSL(2,q), q prime */

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

static Grp grp_matrix(int q, int psl) {
    if (q < 3 || q > 17) return grp_empty();
    qg = q;
    psl_g = psl;
    int ks = q * q * q * q;
    if (ks > idxm_cap) {
        free(idxm);
        idxm = malloc(sizeof(int) * (size_t)ks);
        idxm_cap = idxm ? ks : 0;
        if (!idxm) return grp_empty();
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
                    if (cnt >= MAXN) return grp_empty();
                    gmat[cnt][0] = a;
                    gmat[cnt][1] = b;
                    gmat[cnt][2] = c;
                    gmat[cnt][3] = e;
                    idxm[own] = cnt;
                    cnt++;
                }
    Grp g = grp_alloc(cnt);
    if (!g.t) return g;
    for (int x = 0; x < cnt; x++) {
        int a = gmat[x][0], b = gmat[x][1], c = gmat[x][2], e = gmat[x][3];
        for (int y = 0; y < cnt; y++) {
            int a2 = gmat[y][0], b2 = gmat[y][1], c2 = gmat[y][2], e2 = gmat[y][3];
            int pa = (a * a2 + b * c2) % q;
            int pb = (a * b2 + b * e2) % q;
            int pc = (c * a2 + e * c2) % q;
            int pe = (c * b2 + e * e2) % q;
            int idx = idxm[canon_key(pa, pb, pc, pe)];
            if (idx < 0) { grp_free(&g); return grp_empty(); }
            g.t[(size_t)x * cnt + y] = (uint16_t)idx;
        }
    }
    g.e = idxm[canon_key(1, 0, 0, 1)];
    return g;
}

/* ------------------------------------------------------- base groups */

static int base_order(int id, int p) {
    switch (id) {
        case 0: return p;
        case 1: return 2 * p;      /* dihedral D_p */
        case 2: return 12;         /* A4 */
        case 3: return 24;         /* S4 */
        case 4: return 60;         /* A5 */
        case 5: return 120;        /* S5 */
        case 6: return 360;        /* A6 */
        case 7: return 168;        /* PSL(2,7) */
        case 8: return 120;        /* SL(2,5) */
        case 9: return 660;        /* PSL(2,11) */
        case 10: return 336;       /* SL(2,7) */
        case 12: return 1320;      /* SL(2,11) */
        default: return 0;
    }
}

static Grp build_base(int id, int p) {
    static const int A4g[] = {1, 2, 0, 3, 1, 0, 3, 2};
    static const int S4g[] = {1, 2, 3, 0, 1, 0, 2, 3};
    static const int A5g[] = {1, 2, 3, 4, 0, 1, 2, 0, 3, 4};
    static const int S5g[] = {1, 2, 3, 4, 0, 1, 0, 2, 3, 4};
    static const int A6g[] = {1, 2, 0, 3, 4, 5, 0, 2, 3, 4, 5, 1};
    switch (id) {
        case 0: return grp_meta(p, 1, 1);
        case 1: return grp_meta(p, 2, p - 1);
        case 2: return perm_from_flat(4, 2, A4g);
        case 3: return perm_from_flat(4, 2, S4g);
        case 4: return perm_from_flat(5, 2, A5g);
        case 5: return perm_from_flat(5, 2, S5g);
        case 6: return perm_from_flat(6, 2, A6g);
        case 7: return grp_matrix(7, 1);
        case 8: return grp_matrix(5, 0);
        case 9: return grp_matrix(11, 1);
        case 10: return grp_matrix(7, 0);
        case 12: return grp_matrix(11, 0);
        default: return grp_empty();
    }
}

/* ------------------------------------------------------- candidates */

typedef struct {
    int kind;      /* 0 meta(a1=m,a2=k,b1=r); 1 matrix(a1=q,a2=psl); 2 base(a1=id,a2=p);
                      3 base(a1,a2) x base(b1,b2) */
    int a1, a2, b1, b2;
    int N;         /* nominal order */
    unsigned key;  /* random tie-break */
} Cand;

static Grp build_cand(const Cand *c) {
    if (c->kind == 0) return grp_meta(c->a1, c->a2, c->b1);
    if (c->kind == 1) return grp_matrix(c->a1, c->a2);
    if (c->kind == 2) return build_base(c->a1, c->a2);
    Grp x = build_base(c->a1, c->a2);
    Grp y = build_base(c->b1, c->b2);
    Grp z = grp_direct(&x, &y);
    grp_free(&x);
    grp_free(&y);
    return z;
}

/* Install a group table as the global one. Returns 0 (and frees g) if it is not a group. */
static int install(Grp *g) {
    int n = g->n;
    if (n < 2 || !g->t) { grp_free(g); return 0; }
    int *inv = malloc(sizeof(int) * (size_t)n);
    if (!inv) { grp_free(g); return 0; }
    for (int x = 0; x < n; x++) {
        inv[x] = -1;
        for (int y = 0; y < n; y++)
            if ((int)g->t[(size_t)x * n + y] == g->e) { inv[x] = y; break; }
        if (inv[x] < 0) { free(inv); grp_free(g); return 0; }
    }
    free(T);
    free(INV);
    T = g->t;
    INV = inv;
    N = n;
    e_id = g->e;
    g->t = NULL;
    g->n = 0;
    return 1;
}

static int apply_cand(const Cand *c) {
    Grp g = build_cand(c);
    return install(&g);
}

/* ------------------------------------------------------- connection set */

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

/* ------------------------------------------------------- BFS cost */

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

/* ------------------------------------------------------- candidate generation */

static Cand raw[RAWMAX];
static int nraw = 0;

static void add_raw(int kind, int a1, int a2, int b1, int b2, int Nn) {
    if (nraw >= RAWMAX) return;
    Cand c;
    c.kind = kind;
    c.a1 = a1;
    c.a2 = a2;
    c.b1 = b1;
    c.b2 = b2;
    c.N = Nn;
    c.key = (unsigned)(rnd() >> 33);
    raw[nraw++] = c;
}

static int cmp_asc(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    if (x->N != y->N) return x->N < y->N ? -1 : 1;
    if (x->key != y->key) return x->key < y->key ? -1 : 1;
    return 0;
}

static void gen_raw(int lowN, int hiN) {
    nraw = 0;
    /* metacyclic groups Z_m x|_r Z_k, non-abelian (r != 1) */
    for (int Nv = lowN; Nv <= hiN; Nv++) {
        for (int k = 2; k <= Nv; k++) {
            if (Nv % k) continue;
            int m = Nv / k;
            if (m < 3) continue;
            int got = 0;
            for (int r = 2; r < m && got < 2; r++) {
                if (gcd_l(r, m) != 1) continue;
                if (powmod_l(r, k, m) != 1) continue;
                add_raw(0, m, k, r, 0, Nv);
                got++;
            }
        }
    }
    /* matrix groups */
    static const int qs[] = {5, 7, 11, 13, 17};
    for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++)
        for (int psl = 0; psl < 2; psl++) {
            int q = qs[qi];
            int o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o >= lowN && o <= hiN) add_raw(1, q, psl, 0, 0, o);
        }
    /* base groups (non-cyclic): dihedral D_n for n = 3..60, plus fixed small groups */
    static int bi[128], bp[128], bo[128];
    int nb = 0;
    for (int n = 3; n <= 60; n++) {
        bi[nb] = 1; bp[nb] = n; bo[nb] = 2 * n; nb++;
    }
    static const int fixedid[] = {2, 3, 4, 5, 6, 7, 8, 9, 10, 12};
    for (unsigned i = 0; i < sizeof fixedid / sizeof fixedid[0]; i++) {
        bi[nb] = fixedid[i]; bp[nb] = 0; bo[nb] = base_order(fixedid[i], 0); nb++;
    }
    for (int i = 0; i < nb; i++) {
        if (bo[i] >= lowN && bo[i] <= hiN) add_raw(2, bi[i], bp[i], 0, 0, bo[i]);
        /* base x Z_k */
        for (int k = 2; k <= hiN; k++) {
            long nn = (long)bo[i] * k;
            if (nn < lowN) continue;
            if (nn > hiN) break;
            add_raw(3, bi[i], bp[i], 0, k, (int)nn);
        }
        /* base x base */
        for (int j = i + 1; j < nb; j++) {
            long nn = (long)bo[i] * bo[j];
            if (nn >= lowN && nn <= hiN) add_raw(3, bi[i], bp[i], bi[j], bp[j], (int)nn);
        }
    }
}

/* ------------------------------------------------------- output */

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

    gen_raw(lowN, hiN);
    qsort(raw, (size_t)nraw, sizeof(Cand), cmp_asc);

    static Cand hiL[MAXHI], loL[MAXLO];
    int split = 0;
    while (split < nraw && raw[split].N < recN) split++;
    int nhi = 0, nlo = 0;
    for (int i = split; i < nraw && nhi < MAXHI; i++) hiL[nhi++] = raw[i];
    for (int i = split - 1; i >= 0 && nlo < MAXLO; i--) loL[nlo++] = raw[i];

    double budget0 = t_end - now();
    if (budget0 < 0.0) budget0 = 0.0;
    double base_slice = budget0 * 0.03;
    if (base_slice < 0.5) base_slice = 0.5;

    int have = 0;
    Cand best;
    memset(&best, 0, sizeof best);
    static int bS[MAXDEG];

    /* Phase 1: fallback from groups just below the record, first success wins. */
    double p1_end = now() + 0.25 * budget0;
    for (int i = 0; i < nlo && !have; i++) {
        if (now() >= p1_end || t_end - now() < 0.2) break;
        Cand *c = &loL[i];
        if (2L * c->N > moore) continue;
        if (!apply_cand(c)) continue;
        double sl = base_slice;
        double rem = t_end - now();
        if (sl > rem) sl = rem;
        if (climb(now() + sl)) {
            have = 1;
            bestN = N;
            best = *c;
            memcpy(bS, S, sizeof(int) * (size_t)d);
        }
    }

    /* Phase 2: groups beating the record in ascending order, doubling slices per round. */
    for (int round = 0; round < 8; round++) {
        for (int pass = 0; pass < 2; pass++) {
            if (pass == 1 && have) break;
            Cand *list = pass == 0 ? hiL : loL;
            int cnt = pass == 0 ? nhi : nlo;
            for (int i = 0; i < cnt; i++) {
                double rem = t_end - now();
                if (rem < 0.2) break;
                Cand *c = &list[i];
                if ((long)c->N <= bestN) continue;
                if (2L * c->N > moore) continue;
                if (!apply_cand(c)) continue;
                double sl = base_slice * (double)(1 << round);
                if (sl > rem) sl = rem;
                if (climb(now() + sl)) {
                    have = 1;
                    bestN = N;
                    best = *c;
                    memcpy(bS, S, sizeof(int) * (size_t)d);
                }
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    if start is None or not lib.is_valid(start[0], start[1], d, D):
        start = lib.haar_graph(d, range(d))   # K_{d,d}: always valid for D >= 2
    best = start
    budget = 0.80 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            ref = REF_VERTICES.get((d, D), best[0])
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, ref], timeout=budget + 8)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
