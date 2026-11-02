/* cq.c (deep-108): fast exact evaluator for bipartite bi-coset graphs X(G; L, R; D) over G = PSL(2,q) or PGL(2,q),
 * q prime, by BFS on the orbits of the root's stabiliser (double cosets) instead of on vertices.
 *
 * Graph: A-vertices = left cosets L x, B-vertices = left cosets R y; L x ~ R y iff x y^-1 in D, D = union of
 * double cosets L z_i R. A-degree = #R-cosets in D^-1 = R z^-1 L ..., B-degree = #L-cosets in D. With L = R and one
 * regular double coset this is the family X(G,H,HzH) of handsoff-108 (c6b-exhaust/exh.c uses the same convention).
 *
 * Why orbits: G acts on the right (Lx -> Lxg) and is transitive on each side, so the A-root BFS gives all A-A and
 * A-B distances, and the B-root BFS the B-B distances. Distances from the A root L are invariant under right
 * multiplication by L, so the BFS runs on the L-orbits: A side = double cosets L x L, B side = R y L. A neighbour
 * of an orbit is found from its representative only. About N/|L| nodes instead of N.
 *
 * Cost C = uBA + uAA + uBB in plain vertices (0 = diameter 8): uBA = #B at distance > 7 from the A root,
 * uAA = #A at distance > 8 from the A root, uBB = #B at distance > 8 from the B root.
 *
 * usage: cq q psl NL l1..(4 ints each) NR r1..(4 ints each, NR=0 means R = L) MODE [args]
 *   L and R are given by generator matrices; NL / NR = number of generators.
 *   info                        double-coset size histogram of L\G/L
 *   member k z1(4) .. zk(4)     costs of D = union L z_i R
 *   prof k z..                  sphere sizes from the A root (vertices per level) and the tree counts
 *   unc k z..                   list the uncovered orbits (side, size, representative, stabiliser order)
 *   scan OUT THR [start step]   L = R, one regular double coset: every class (inversion, N_PGL(L) conjugation),
 *                               A-root cost; B-root only if uBA+uAA <= THR. Resumable (skips ids in OUT).
 *   scanLR OUT THR [start step] L != R: every regular double coset L z R (no class reduction), as scan
 *   sample n seed k sizes..     random members: D = union of k random double cosets L z R whose size class
 *                               (#R-cosets) is given; prints costs
 *   bench n                     time n A-root BFS on random regular members
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <sys/mman.h>
#include <math.h>

#define MAXQ 1024
#define MAXH 256
#define MAXDEG 64

static int Q, H2, PSL, M2, NSQ, ZM = 1;
static uint64_t BASE2, NKEY, GORD;
static uint16_t *MULT;               /* MULT[x*Q+y] */
static int *INVV, *LAM, *BITD;

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static int pw(int b, long e) { long r = 1, x = b % Q; while (e) { if (e & 1) r = r * x % Q; x = x * x % Q; e >>= 1; } return (int)r; }
static inline int addq(int u, int v) { int s = u + v; return s >= Q ? s - Q : s; }
static inline int subq(int u, int v) { int s = u - v; return s < 0 ? s + Q : s; }
#define MUL(x, y) ((int)MULT[(x) * Q + (y)])
static void fatal(const char *m) { fprintf(stderr, "FATAL: %s\n", m); exit(2); }

static void setup_field(int q) {
    Q = q; H2 = (q - 1) / 2;
    MULT = malloc(sizeof(uint16_t) * q * q); INVV = malloc(sizeof(int) * q); LAM = malloc(sizeof(int) * q); BITD = malloc(sizeof(int) * q);
    for (int x = 0; x < q; x++) for (int y = 0; y < q; y++) MULT[x * q + y] = (uint16_t)((long)x * y % q);
    INVV[0] = 0; for (int x = 1; x < q; x++) INVV[x] = pw(x, q - 2);
    NSQ = 0; for (int t = 2; t < q; t++) if (pw(t, (q - 1) / 2) == q - 1) { NSQ = t; break; }
    /* LAM[d]: a scalar l with l^2 d = 1 (square d) or l^2 d = NSQ (non-square d) */
    int *sqrtv = malloc(sizeof(int) * q); for (int x = 0; x < q; x++) sqrtv[x] = -1;
    for (int l = 1; l < q; l++) { int s = MUL(l, l); if (sqrtv[s] < 0) sqrtv[s] = l; }
    LAM[0] = 0; BITD[0] = 0;
    for (int d = 1; d < q; d++) {
        int sq = (pw(d, (q - 1) / 2) == 1), target = sq ? 1 : NSQ;
        BITD[d] = !sq;
        /* need l^2 = target / d */
        int want = MUL(target, INVV[d]);
        if (sqrtv[want] < 0) fatal("no scalar");
        LAM[d] = sqrtv[want];
    }
    free(sqrtv);
}

/* scale to det 1 (square det) or det NSQ (non-square det), then fix the sign; returns the det-class bit */
static inline int norm_mat(int *r) {
    int det = subq(MUL(r[0], r[3]), MUL(r[1], r[2]));
    int lam = LAM[det];
    int v0 = MUL(lam, r[0]), v1 = MUL(lam, r[1]), v2 = MUL(lam, r[2]), v3 = MUL(lam, r[3]);
    int bit = BITD[det];
    int neg = v0 ? (v0 > H2) : (v1 > H2);
    int n0 = v0 ? Q - v0 : 0, n1 = v1 ? Q - v1 : 0, n2 = v2 ? Q - v2 : 0, n3 = v3 ? Q - v3 : 0;
    r[0] = neg ? n0 : v0; r[1] = neg ? n1 : v1; r[2] = neg ? n2 : v2; r[3] = neg ? n3 : v3;
    return bit;
}
static inline uint64_t keyof(const int *r, int bit) {
    uint64_t b = (M2 == 2) ? (uint64_t)bit : 0;
    uint64_t k = r[0] ? ((((uint64_t)(r[0] - 1) * Q + r[1]) * Q + r[2]) * M2) + b : BASE2 + (((uint64_t)(r[1] - 1) * Q + r[3]) * M2) + b;
    return k * ZM + (uint64_t)r[4];
}
static void decode(uint64_t k, int m2, int *r) {
    r[4] = (int)(k % ZM); k /= ZM;
    uint64_t base2 = (uint64_t)H2 * Q * Q * m2;
    if (k < base2) {
        int bit = (m2 == 2) ? (int)(k & 1) : 0;
        uint64_t x = k / m2;
        int c = (int)(x % Q); x /= Q;
        int b = (int)(x % Q); x /= Q;
        int a = (int)x + 1;
        int delta = bit ? NSQ : 1;
        r[0] = a; r[1] = b; r[2] = c; r[3] = MUL(addq(delta, MUL(b, c)), INVV[a]);
    } else {
        uint64_t k2 = k - base2;
        int bit = (m2 == 2) ? (int)(k2 & 1) : 0;
        uint64_t x = k2 / m2;
        int d = (int)(x % Q); x /= Q;
        int b = (int)x + 1;
        int delta = bit ? NSQ : 1;
        r[0] = 0; r[1] = b; r[2] = MUL((Q - delta) % Q, INVV[b]); r[3] = d;
    }
}
static inline void mulm(const int *x, const int *y, int *r) {
    r[0] = addq(MUL(x[0], y[0]), MUL(x[1], y[2]));
    r[1] = addq(MUL(x[0], y[1]), MUL(x[1], y[3]));
    r[2] = addq(MUL(x[2], y[0]), MUL(x[3], y[2]));
    r[3] = addq(MUL(x[2], y[1]), MUL(x[3], y[3]));
    r[4] = (x[4] + y[4]) % ZM;
}
static inline void adjm(const int *x, int *r) { r[0] = x[3]; r[1] = x[1] ? Q - x[1] : 0; r[2] = x[2] ? Q - x[2] : 0; r[3] = x[0]; r[4] = (ZM - x[4]) % ZM; }
static inline uint64_t keym(const int *m) { int r[5] = { m[0], m[1], m[2], m[3], m[4] }; int bit = norm_mat(r); if (M2 == 1 && bit) fatal("non-square det in PSL"); return keyof(r, bit); }
static inline int eqm(const int *a, const int *b) { int x[5] = { a[0], a[1], a[2], a[3], a[4] }, y[5] = { b[0], b[1], b[2], b[3], b[4] }; int bx = norm_mat(x), by = norm_mat(y); return bx == by && !memcmp(x, y, sizeof x); }

/* ---------- subgroups ---------- */
typedef struct { int n; int (*e)[5]; } Grp;
static Grp closure(int ng, int (*gen)[5]) {
    Grp g; g.e = malloc(sizeof(int[5]) * MAXH); g.n = 1;
    g.e[0][0] = 1; g.e[0][1] = 0; g.e[0][2] = 0; g.e[0][3] = 1; g.e[0][4] = 0;
    for (int i = 0; i < g.n; i++) for (int k = 0; k < ng; k++) {
        int p[5]; mulm(g.e[i], gen[k], p); int bit = norm_mat(p); if (M2 == 1 && bit) fatal("generator not in PSL");
        int found = 0; for (int j = 0; j < g.n; j++) if (!memcmp(g.e[j], p, sizeof p)) { found = 1; break; }
        if (!found) { if (g.n >= MAXH) fatal("subgroup too big"); memcpy(g.e[g.n], p, sizeof p); g.n++; }
    }
    return g;
}
static int ingrp(const Grp *g, const int *m) { int x[5] = { m[0], m[1], m[2], m[3], m[4] }; norm_mat(x); for (int i = 0; i < g->n; i++) if (!memcmp(g->e[i], x, sizeof x)) return 1; return 0; }
static int order_of(const int *m) { int x[5] = { m[0], m[1], m[2], m[3], m[4] }; norm_mat(x); int p[5] = { x[0], x[1], x[2], x[3], x[4] }; int I[5] = { 1, 0, 0, 1, 0 };
    for (int k = 1; k < 100000; k++) { if (eqm(p, I)) return k; int t[5]; mulm(p, x, t); norm_mat(t); memcpy(p, t, sizeof t); } return -1; }

/* ---------- double coset tables: key -> id of  A g B  ---------- */
typedef struct { uint32_t *oid; uint16_t (*rep)[5]; uint32_t *sz; uint32_t n; } DCT;
static DCT build_dct(const Grp *A, const Grp *B) {
    DCT t;
    size_t tb = ((size_t)NKEY * 4 + (1u << 21) - 1) & ~(size_t)((1u << 21) - 1);
    t.oid = aligned_alloc(1u << 21, tb); if (!t.oid) fatal("alloc oid");
    madvise(t.oid, tb, MADV_HUGEPAGE);
    memset(t.oid, 0xff, NKEY * 4);
    size_t cap = GORD / A->n + 1024;
    t.rep = malloc(sizeof(*t.rep) * cap); t.sz = malloc(sizeof(uint32_t) * cap);
    uint32_t n = 0;
    for (uint64_t k = 0; k < NKEY; k++) {
        if (t.oid[k] != 0xffffffffu) continue;
        int g[5]; decode(k, M2, g);
        uint32_t cnt = 0;
        for (int i = 0; i < A->n; i++) { int ag[5]; mulm(A->e[i], g, ag);
            for (int j = 0; j < B->n; j++) { int p[5]; mulm(ag, B->e[j], p); uint64_t kk = keym(p);
                if (t.oid[kk] == 0xffffffffu) { t.oid[kk] = n; cnt++; } else if (t.oid[kk] != n) fatal("double coset overlap"); } }
        if (n >= cap) fatal("too many double cosets");
        for (int i = 0; i < 5; i++) t.rep[n][i] = (uint16_t)g[i];
        if (cnt % A->n) fatal("double coset size not a multiple of |A|");
        t.sz[n] = cnt / A->n;
        n++;
    }
    t.n = n;
    return t;
}

/* ---------- the graph ---------- */
static Grp GL_, GR_;                  /* L, R */
static DCT TLL, TRL, TRR, TLR;         /* A-root: A side TLL, B side TRL; B-root: B side TRR, A side TLR */
static int LEQR;
static int NE, ND;                    /* A-degree (neighbours R e_j x), B-degree (neighbours L d_j y) */
static int EM[MAXDEG][5], DM[MAXDEG][5];
static uint64_t *VIS[2], *CUR;
static uint32_t *UNV[2], *FR, *NX; static long nunv[2];
static long LEVSZ[16];                 /* vertices reached per level (prof) */
static uint8_t *LEV[2];                /* level per orbit of the last bfs (255 = unreached) */

/* D = union of L z_i R. e-list: distinct R-cosets R z_i^-1 l (l in L); d-list: distinct L-cosets L z_i r (r in R). */
static int set_D(int k, int (*z)[5]) {
    NE = 0; ND = 0;
    for (int i = 0; i < k; i++) {
        int zi[5]; adjm(z[i], zi);
        for (int a = 0; a < GL_.n; a++) {
            int c[5]; mulm(zi, GL_.e[a], c);
            int dup = 0;
            for (int j = 0; j < NE && !dup; j++) { int ci[5], p[5]; adjm(EM[j], ci); mulm(c, ci, p); if (ingrp(&GR_, p)) dup = 1; }
            if (!dup) { if (NE >= MAXDEG) return -1; memcpy(EM[NE++], c, sizeof c); }
        }
        for (int b = 0; b < GR_.n; b++) {
            int c[5]; mulm(z[i], GR_.e[b], c);
            int dup = 0;
            for (int j = 0; j < ND && !dup; j++) { int ci[5], p[5]; adjm(DM[j], ci); mulm(c, ci, p); if (ingrp(&GL_, p)) dup = 1; }
            if (!dup) { if (ND >= MAXDEG) return -1; memcpy(DM[ND++], c, sizeof c); }
        }
    }
    return 0;
}

static inline int getb(const uint64_t *B, uint32_t i) { return (int)((B[i >> 6] >> (i & 63)) & 1); }
static inline void setb(uint64_t *B, uint32_t i) { B[i >> 6] |= 1ULL << (i & 63); }

/* neighbour keys of the vertex with representative x on side s (0 = A: neighbours R e_j x on B; 1 = B: L d_j y on A) */
static inline uint64_t nbkey(const uint16_t *x, int s, int j) {
    const int *g = s == 0 ? EM[j] : DM[j];
    int p[5];
    p[0] = addq(MUL(g[0], x[0]), MUL(g[1], x[2]));
    p[1] = addq(MUL(g[0], x[1]), MUL(g[1], x[3]));
    p[2] = addq(MUL(g[2], x[0]), MUL(g[3], x[2]));
    p[3] = addq(MUL(g[2], x[1]), MUL(g[3], x[3]));
    p[4] = (g[4] + x[4]) % ZM;
    int bit = norm_mat(p);
    return keyof(p, bit);
}

/* BFS from the root on side rs (0 = A root, 1 = B root) up to level 8 on the orbit quotient.
   tab[side] = orbit table used for that side. After return: nunv/UNV hold the unvisited orbits; uncovered counts
   are computed by the caller. If prof, LEVSZ gets vertices per level. */
static void bfs(int rs, DCT *tabA, DCT *tabB, int prof) {
    DCT *tab[2] = { tabA, tabB };
    for (int s = 0; s < 2; s++) { size_t nw = (tab[s]->n + 63) / 64; memset(VIS[s], 0, nw * 8); }
    { size_t nw = ((tab[0]->n > tab[1]->n ? tab[0]->n : tab[1]->n) + 63) / 64; memset(CUR, 0, nw * 8); }
    int I[5] = { 1, 0, 0, 1, 0 };
    uint32_t root = tab[rs]->oid[keym(I)];
    for (int s = 0; s < 2; s++) { uint32_t k = 0; for (uint32_t o = 0; o < tab[s]->n; o++) if (!(s == rs && o == root)) UNV[s][k++] = o; nunv[s] = k; }
    memset(LEV[0], 255, tab[0]->n); memset(LEV[1], 255, tab[1]->n); LEV[rs][root] = 0;
    setb(VIS[rs], root); setb(CUR, root);
    uint32_t nf = 1; FR[0] = root; int sL = rs;
    if (prof) { memset(LEVSZ, 0, sizeof LEVSZ); LEVSZ[0] = tab[rs]->sz[root]; }
    int deg[2] = { NE, ND };
    for (int L = 1; L <= 8 && nf; L++) {
        int o = 1 - sL;
        uint32_t nn = 0;
        DCT *to = tab[o], *tc = tab[sL];
        int dg = deg[sL];
        if ((long)nf * dg < nunv[o] * 3) {                            /* top-down */
            enum { BT = 8 };
            uint64_t kb[BT * MAXDEG];
            for (uint32_t i0 = 0; i0 < nf; i0 += BT) {
                int nb = (int)((nf - i0 < BT) ? (nf - i0) : BT);
                for (int b = 0; b < nb; b++) { const uint16_t *x = tc->rep[FR[i0 + b]]; for (int j = 0; j < dg; j++) kb[b * dg + j] = nbkey(x, sL, j); }
                for (int t = 0; t < nb * dg; t++) __builtin_prefetch(&to->oid[kb[t]]);
                for (int t = 0; t < nb * dg; t++) { uint32_t w = to->oid[kb[t]]; if (!getb(VIS[o], w)) { setb(VIS[o], w); LEV[o][w] = (uint8_t)L; NX[nn++] = w; } }
            }
            uint32_t k = 0;
            for (long i = 0; i < nunv[o]; i++) { uint32_t u = UNV[o][i]; if (!getb(VIS[o], u)) UNV[o][k++] = u; }
            nunv[o] = k;
        } else {                                                     /* bottom-up */
            int dgo = deg[o];
            enum { BB = 8 };
            uint64_t kb[BB * MAXDEG];
            uint32_t k = 0;
            for (long i0 = 0; i0 < nunv[o]; i0 += BB) {
                int nb = (int)((nunv[o] - i0 < BB) ? (nunv[o] - i0) : BB);
                for (int b = 0; b < nb; b++) { const uint16_t *y = to->rep[UNV[o][i0 + b]]; for (int j = 0; j < dgo; j++) kb[b * dgo + j] = nbkey(y, o, j); }
                for (int t = 0; t < nb * dgo; t++) __builtin_prefetch(&tc->oid[kb[t]]);
                for (int b = 0; b < nb; b++) {
                    uint32_t u = UNV[o][i0 + b]; int found = 0;
                    for (int j = 0; j < dgo && !found; j++) if (getb(CUR, tc->oid[kb[b * dgo + j]])) found = 1;
                    if (found) { setb(VIS[o], u); LEV[o][u] = (uint8_t)L; NX[nn++] = u; } else UNV[o][k++] = u;
                }
            }
            nunv[o] = k;
        }
        { size_t nw = ((tab[0]->n > tab[1]->n ? tab[0]->n : tab[1]->n) + 63) / 64; memset(CUR, 0, nw * 8); }
        for (uint32_t i = 0; i < nn; i++) setb(CUR, NX[i]);
        if (prof) { long s = 0; for (uint32_t i = 0; i < nn; i++) s += to->sz[NX[i]]; LEVSZ[L] = s; }
        uint32_t *t = FR; FR = NX; NX = t; nf = nn; sL = o;
    }
}
static long unc_side(DCT *t, int s) { long u = 0; for (long i = 0; i < nunv[s]; i++) u += t->sz[UNV[s][i]]; return u; }

static void costs(long *uBA, long *uAA, long *uBB) {
    bfs(0, &TLL, &TRL, 0);
    *uBA = unc_side(&TRL, 1); *uAA = unc_side(&TLL, 0);
    if (uBB) { bfs(1, &TLR, &TRR, 0); *uBB = unc_side(&TRR, 1); }
}

static uint64_t rst = 88172645463325252ULL;
static inline uint64_t rnd64(void) { rst ^= rst << 13; rst ^= rst >> 7; rst ^= rst << 17; return rst; }

/* normaliser of L (and R) inside PGL(2,q): all n with n L n^-1 = L (and n R n^-1 = R) */
static int NAMB; static int AMB[256][5];
static void build_normalizer(void) {
    int sm2 = M2; M2 = 2; int szm = ZM; ZM = 1;
    uint64_t nkp = 2ULL * H2 * Q * (Q + 1);
    NAMB = 0;
    for (uint64_t k = 0; k < nkp; k++) {
        int n[5], na[5]; decode(k, 2, n); n[4] = 0; ZM = szm; adjm(n, na);
        int ok = 1;
        for (int g = 0; g < GL_.n && ok; g++) { int t[5], p[5]; mulm(n, GL_.e[g], t); mulm(t, na, p); if (!ingrp(&GL_, p)) ok = 0; }
        for (int g = 0; g < GR_.n && ok; g++) { int t[5], p[5]; mulm(n, GR_.e[g], t); mulm(t, na, p); if (!ingrp(&GR_, p)) ok = 0; }
        ZM = 1;
        if (!ok) continue;
        if (NAMB >= 256) fatal("normaliser too big");
        memcpy(AMB[NAMB], n, sizeof n); NAMB++;
    }
    M2 = sm2; ZM = szm;
}

static int parse_z(char **argv, int k, int (*z)[5]) { for (int i = 0; i < k; i++) for (int j = 0; j < 5; j++) z[i][j] = atoi(argv[5 * i + j]); return 5 * k; }

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: cq q psl NL gens.. NR gens.. MODE [args]\n"); return 2; }
    int ai = 1;
    int q = atoi(argv[ai++]); PSL = atoi(argv[ai++]); ZM = atoi(argv[ai++]);
    setup_field(q);
    M2 = PSL ? 1 : 2; H2 = (q - 1) / 2;
    BASE2 = (uint64_t)H2 * q * q * M2; NKEY = (BASE2 + (uint64_t)H2 * q * M2) * ZM;
    GORD = (PSL ? (uint64_t)q * ((uint64_t)q * q - 1) / 2 : (uint64_t)q * ((uint64_t)q * q - 1)) * ZM;
    int nl = atoi(argv[ai++]); int gl[16][5]; for (int i = 0; i < nl; i++) for (int j = 0; j < 5; j++) gl[i][j] = atoi(argv[ai++]);
    int nr = atoi(argv[ai++]); int gr[16][5]; for (int i = 0; i < nr; i++) for (int j = 0; j < 5; j++) gr[i][j] = atoi(argv[ai++]);
    const char *mode = argv[ai++];
    double t0 = now();
    GL_ = closure(nl, gl);
    LEQR = (nr == 0);
    GR_ = LEQR ? GL_ : closure(nr, gr);
    if (GL_.n != GR_.n) fprintf(stderr, "warning: |L| = %d != |R| = %d\n", GL_.n, GR_.n);
    TLL = build_dct(&GL_, &GL_);
    if (LEQR) { TRL = TLL; TRR = TLL; TLR = TLL; }
    else { TRL = build_dct(&GR_, &GL_); TRR = build_dct(&GR_, &GR_); TLR = build_dct(&GL_, &GR_); }
    uint32_t maxn = TLL.n; if (TRL.n > maxn) maxn = TRL.n; if (TRR.n > maxn) maxn = TRR.n; if (TLR.n > maxn) maxn = TLR.n;
    size_t nw = (maxn + 63) / 64;
    VIS[0] = calloc(nw, 8); VIS[1] = calloc(nw, 8); CUR = calloc(nw, 8);
    LEV[0] = malloc(maxn); LEV[1] = malloc(maxn); UNV[0] = malloc(4 * (size_t)maxn); UNV[1] = malloc(4 * (size_t)maxn); FR = malloc(4 * (size_t)maxn); NX = malloc(4 * (size_t)maxn);
    fprintf(stderr, "setup %.1f s: %s(2,%d) |G|=%llu |L|=%d |R|=%d N_A=%llu N_B=%llu orbits LL=%u RL=%u\n", now() - t0,
            PSL ? "PSL" : "PGL", q, (unsigned long long)GORD, GL_.n, GR_.n, (unsigned long long)(GORD / GL_.n),
            (unsigned long long)(GORD / GR_.n), TLL.n, TRL.n);

    if (!strcmp(mode, "info")) {
        uint32_t hist[MAXH + 1] = { 0 };
        for (uint32_t o = 0; o < TRL.n; o++) if (TRL.sz[o] <= MAXH) hist[TRL.sz[o]]++;
        printf("double cosets R g L by #R-cosets:");
        for (int s = 1; s <= MAXH; s++) if (hist[s]) printf(" c%d:%u", s, hist[s]);
        printf("\n");
        for (int i = 0; i < GL_.n; i++) printf("L elt %d order %d\n", i, order_of(GL_.e[i]));
        return 0;
    }
    if (!strcmp(mode, "member") || !strcmp(mode, "prof") || !strcmp(mode, "unc")) {
        int k = atoi(argv[ai++]); int z[16][5]; ai += parse_z(argv + ai, k, z);
        if (set_D(k, z)) fatal("degree too big");
        if (!strcmp(mode, "member")) {
            long uBA, uAA, uBB; double tb = now(); costs(&uBA, &uAA, &uBB);
            printf("member degA %d degB %d uBA %ld uAA %ld uBB %ld C %ld (%.1f ms)\n", NE, ND, uBA, uAA, uBB, uBA + uAA + uBB, (now() - tb) * 1e3);
        } else if (!strcmp(mode, "prof")) {
            bfs(0, &TLL, &TRL, 1);
            long tree = 1; printf("level vertices tree ratio\n");
            for (int L = 0; L <= 8; L++) { printf("%d %ld %ld %.4f\n", L, LEVSZ[L], tree, (double)LEVSZ[L] / tree); tree = L == 0 ? NE : tree * (L % 2 ? ND - 1 : NE - 1); }
            printf("uBA %ld uAA %ld\n", unc_side(&TRL, 1), unc_side(&TLL, 0));
        } else {
            bfs(0, &TLL, &TRL, 0);
            for (int s = 1; s >= 0; s--) {
                DCT *t = s ? &TRL : &TLL;
                for (long i = 0; i < nunv[s]; i++) { uint32_t o = UNV[s][i];
                    printf("A-root uncovered side %c orbit %u size %u stab %d rep %d %d %d %d %d\n", s ? 'B' : 'A', o, t->sz[o], GL_.n / (int)t->sz[o], t->rep[o][0], t->rep[o][1], t->rep[o][2], t->rep[o][3], t->rep[o][4]); }
            }
            bfs(1, &TLR, &TRR, 0);
            for (long i = 0; i < nunv[1]; i++) { uint32_t o = UNV[1][i];
                printf("B-root uncovered side B orbit %u size %u rep %d %d %d %d\n", o, TRR.sz[o], TRR.rep[o][0], TRR.rep[o][1], TRR.rep[o][2], TRR.rep[o][3]); }
        }
        return 0;
    }
    if (!strcmp(mode, "corr")) {
        /* for every regular B-orbit: k = number of its 10 neighbour A-cosets at distance <= 6 from the A root;
           histogram of k against Binomial(10, f6). Also the number of distinct neighbour A-orbits. */
        int k = atoi(argv[ai++]); int z[16][5]; ai += parse_z(argv + ai, k, z);
        if (set_D(k, z)) fatal("degree too big");
        bfs(0, &TLL, &TRL, 0);
        long a6 = 0, a4 = 0; for (uint32_t o = 0; o < TLL.n; o++) { if (LEV[0][o] == 6) a6 += TLL.sz[o]; if (LEV[0][o] <= 4) a4 += TLL.sz[o]; }
        double f6 = (double)a6 / (GORD / GL_.n - a4);
        long hist[MAXDEG + 1] = { 0 }, hd[MAXDEG + 1] = { 0 }, nb = 0;
        for (uint32_t o = 0; o < TRL.n; o++) {
            if (TRL.sz[o] != (uint32_t)GL_.n) continue;
            if (LEV[1][o] <= 5) continue;
            uint32_t ids[MAXDEG]; int kk = 0, nd = 0;
            for (int j = 0; j < ND; j++) { uint32_t w = TLL.oid[nbkey(TRL.rep[o], 1, j)]; ids[j] = w; if (LEV[0][w] <= 6) kk++;
                int dup = 0; for (int i = 0; i < j; i++) if (ids[i] == w) dup = 1; if (!dup) nd++; }
            hist[kk]++; hd[nd]++; nb++;
        }
        printf("f6 %.4f  B-orbits %ld\nk observed binomial(10,f6)\n", f6, nb);
        double c = 1; for (int i = 0; i <= ND; i++) { double p = c * pow(f6, i) * pow(1 - f6, ND - i); printf("%d %ld %.1f\n", i, hist[i], p * nb); c = c * (ND - i) / (i + 1); }
        printf("distinct neighbour orbits:"); for (int i = 0; i <= ND; i++) if (hd[i]) printf(" %d:%ld", i, hd[i]); printf("\n");
        return 0;
    }
    if (!strcmp(mode, "bench")) {
        int n = atoi(argv[ai++]); double tb = now(); long sum = 0; int done = 0;
        int hreg = GL_.n;
        while (done < n) {
            uint32_t o = (uint32_t)(rnd64() % TRL.n); if (TRL.sz[o] != (uint32_t)hreg) continue;
            int z[1][5]; for (int i = 0; i < 5; i++) z[0][i] = TRL.rep[o][i];
            /* rep of R g L; D = L z R needs z with L z R regular: use z = rep^-1 */
            int zi[5]; adjm(z[0], zi); memcpy(z[0], zi, sizeof zi);
            if (set_D(1, z)) continue;
            long a, b; costs(&a, &b, NULL); sum += a + b; done++;
        }
        printf("bench %d A-root BFS: %.2f ms each (mean P %.1f)\n", n, (now() - tb) * 1e3 / n, (double)sum / n);
        return 0;
    }
    if (!strcmp(mode, "scan") || !strcmp(mode, "scanLR")) {
        const char *out = argv[ai++]; long thr = atol(argv[ai++]);
        long start = argc > ai ? atol(argv[ai++]) : 0, step = argc > ai ? atol(argv[ai++]) : 1;
        /* members: double cosets L z R with |L z R| = |L||R| (regular). Indexed by the TLR table (L g R). */
        DCT *T = &TLR;
        uint32_t *par = malloc(4 * (size_t)T->n);
        for (uint32_t i = 0; i < T->n; i++) par[i] = i;
        uint32_t nreg = 0; for (uint32_t i = 0; i < T->n; i++) if (T->sz[i] == (uint32_t)GR_.n) nreg++;
        if (!strcmp(mode, "scan")) {
            if (!LEQR) fatal("scan needs L = R");
            build_normalizer();
            #define FINDP(x) ({ uint32_t _x = (x); while (par[_x] != _x) { par[_x] = par[par[_x]]; _x = par[_x]; } _x; })
            for (uint32_t id = 0; id < T->n; id++) {
                if (T->sz[id] != (uint32_t)GR_.n) continue;
                int z[5] = { T->rep[id][0], T->rep[id][1], T->rep[id][2], T->rep[id][3], T->rep[id][4] }, zi[5]; adjm(z, zi);
                uint32_t a = FINDP(id), b = FINDP(T->oid[keym(zi)]); if (a != b) { if (a < b) par[b] = a; else par[a] = b; }
                for (int k = 0; k < NAMB; k++) { int na[5], t1[5], p[5]; adjm(AMB[k], na); mulm(AMB[k], z, t1); mulm(t1, na, p);
                    int bit = norm_mat(p); if (M2 == 1 && bit) fatal("conjugate leaves PSL");
                    uint32_t c = FINDP(id), d = FINDP(T->oid[keyof(p, bit)]); if (c != d) { if (c < d) par[d] = c; else par[c] = d; } }
            }
        }
        uint32_t *osz = calloc(T->n, 4);
        for (uint32_t id = 0; id < T->n; id++) if (T->sz[id] == (uint32_t)GR_.n) { uint32_t r = id; while (par[r] != r) r = par[r]; osz[r]++; }
        uint32_t ncls = 0; for (uint32_t id = 0; id < T->n; id++) if (osz[id]) ncls++;
        fprintf(stderr, "%s: regular double cosets %u, normaliser %d, classes %u\n", mode, nreg, NAMB, ncls);
        uint8_t *done = calloc(T->n, 1);
        { FILE *f = fopen(out, "r"); if (f) { char line[512]; while (fgets(line, sizeof line, f)) { unsigned id; if (sscanf(line, "M %u", &id) == 1 && id < T->n) done[id] = 1; } fclose(f); } }
        FILE *fo = fopen(out, "a"); if (!fo) fatal("cannot open output");
        double ts = now(); long cnt = 0, idx = 0;
        for (uint32_t id = 0; id < T->n; id++) {
            if (!osz[id]) continue;
            if ((idx++ - start) % step != 0 || idx - 1 < start) continue;
            if (done[id]) continue;
            int z[1][5]; for (int i = 0; i < 5; i++) z[0][i] = T->rep[id][i];
            if (set_D(1, z)) fatal("degree");
            long uBA, uAA, uBB = -1; costs(&uBA, &uAA, NULL);
            if (uBA + uAA <= thr) { long a, b; bfs(1, &TLR, &TRR, 0); uBB = unc_side(&TRR, 1); (void)a; (void)b; }
            fprintf(fo, "M %u %u %ld %ld %ld %d %d %d %d %d\n", id, osz[id], uBA, uAA, uBB, z[0][0], z[0][1], z[0][2], z[0][3], z[0][4]);
            cnt++;
            if (cnt % 2000 == 0) { fflush(fo); fprintf(stderr, "%s: %ld members, %.0f s\n", mode, cnt, now() - ts); }
        }
        fclose(fo);
        fprintf(stderr, "%s done: %ld members in %.0f s\n", mode, cnt, now() - ts);
        return 0;
    }
    if (!strcmp(mode, "sample")) {
        int n = atoi(argv[ai++]); rst ^= (uint64_t)atoll(argv[ai++]) * 0x9E3779B97F4A7C15ULL; int k = atoi(argv[ai++]);
        int want[16]; for (int i = 0; i < k; i++) want[i] = atoi(argv[ai++]);
        /* candidate pools by size class (#L-cosets... use TLR sizes = #L-cosets in L g R) */
        double ts = now();
        for (int t = 0; t < n; t++) {
            int z[16][5];
            for (int i = 0; i < k; i++) {
                uint32_t id; do { id = (uint32_t)(rnd64() % TLR.n); } while (TLR.sz[id] != (uint32_t)want[i]);
                for (int j = 0; j < 5; j++) z[i][j] = TLR.rep[id][j];
            }
            if (set_D(k, z)) { t--; continue; }
            long uBA, uAA, uBB; costs(&uBA, &uAA, &uBB);
            printf("S degA %d degB %d uBA %ld uAA %ld uBB %ld C %ld z", NE, ND, uBA, uAA, uBB, uBA + uAA + uBB);
            for (int i = 0; i < k; i++) printf(" %d %d %d %d %d", z[i][0], z[i][1], z[i][2], z[i][3], z[i][4]);
            printf("\n"); fflush(stdout);
        }
        fprintf(stderr, "sample: %d in %.1f s\n", n, now() - ts);
        return 0;
    }
    fatal("unknown mode");
    return 2;
}
