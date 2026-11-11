/* fastc.c (c8b-coset, handsoff-108): fast exact cost for bipartite coset graphs X(G,H,D), G = PSL(2,q) (q prime),
 * H = C_h in the split torus (h odd, h | (q-1)/2), D = union of two regular double cosets H g H (degree 10 for h = 5).
 * Vertices: left cosets Hx (side A, label LA) and Hy (side B). Edge Hx ~ Hy iff x y^-1 in D.
 *
 * Coset label (exact bijection onto [0, N), N = |G|/h), see NOTES.md:
 *   M(x) = (ac, ad, bc, bd) of x = (a b; c d) in SL(2,q) is invariant under the torus diag(l,1/l) and a complete
 *   invariant of the torus orbit; the class id m(x) in [0, q(q+1)) is assigned from M(x), and
 *   LAB(x) = m(x) * K + dlog(ref) mod K, K = (q-1)/(2h), ref = a if a != 0 else b.
 *   (+-1 and mu_h are exactly the scalars with dlog = 0 mod K.)  Checked at setup: every label is hit by 10 SL elements.
 *
 * Cost (full diameter test, as coset.c but also B-B distances):
 *   uncB_A = #B vertices at distance > 7 from the A root (A-B pairs), uncA_A = #A vertices at distance > 8 from A root,
 *   uncB_B = #B vertices at distance > 8 from the B root (B-B pairs). C = uncB_A + uncA_A + uncB_B.
 *   If D = D^-1 there is a side-swapping automorphism and uncB_B = uncA_A, so C = uncB_A + 2 uncA_A (one BFS).
 *   coset.c / coset2.c omit uncB_B (one BFS only).
 *
 * BFS: direction-optimising (top-down while the frontier is small, bottom-up scan of unvisited vertices otherwise).
 *
 * Modes:
 *   fastc validate <coset2 tsv>       recompute uncB/uncA of the coset2 candidates (same H, conjugated frame); must match
 *   fastc bench <n> <seed>            time n random candidates (full cost)
 *   fastc anneal <seconds> <seed> <COOL> <REHEAT> <K> <tag>   annealing with fresh chains (see NOTES.md)
 *   fastc symscan <out>               all symmetric pairs {DC, DC^-1} (one BFS each)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>
#include <limits.h>

#define MAXQ 256
static int Q, HO, KC, NCL, NN;
static uint8_t MUL[MAXQ][MAXQ];
static int DLK[MAXQ], DLOG[MAXQ], EXPT[MAXQ], INVF[MAXQ];
static uint16_t CL[MAXQ * MAXQ], C0[MAXQ * MAXQ];
#define KCC 18
static uint8_t *BASE, *BKREF, *BSET;   /* class base matrix (4 entries), DLK of its reference entry, set flag */
static uint8_t *CNTL;
static int HM[16][4];       /* H_k = diag(s^k, s^-k) */
static uint32_t IDL;

static inline int addq(int u, int v) { int s = u + v; return s >= Q ? s - Q : s; }

static inline uint32_t LAB(int a, int b, int c, int d) {
    int p = MUL[a][c], r = MUL[a][d], t = MUL[b][d];
    uint32_t m = p ? CL[p * Q + r] : C0[r * Q + t];
    int ref = a ? a : b;
    return m * KC + DLK[ref];
}
static inline void repof(uint32_t l, int *x) {   /* representative of coset label l: torus scaling of the class base */
    uint32_t m = l / KCC; int k = (int)(l - m * KCC);
    const uint8_t *bq = BASE + 4 * (size_t)m;
    int j = k - BKREF[m]; if (j < 0) j += KCC;
    int lam = EXPT[j], li = INVF[lam];
    x[0] = MUL[lam][bq[0]]; x[1] = MUL[lam][bq[1]]; x[2] = MUL[li][bq[2]]; x[3] = MUL[li][bq[3]];
}
static inline void mm(const int *x, const int *y, int *r) {   /* r = x*y, all entries mod Q */
    r[0] = addq(MUL[x[0]][y[0]], MUL[x[1]][y[2]]);
    r[1] = addq(MUL[x[0]][y[1]], MUL[x[1]][y[3]]);
    r[2] = addq(MUL[x[2]][y[0]], MUL[x[3]][y[2]]);
    r[3] = addq(MUL[x[2]][y[1]], MUL[x[3]][y[3]]);
}
static inline void minv(const int *x, int *r) {   /* SL inverse */
    r[0] = x[3]; r[1] = (Q - x[1]) % Q; r[2] = (Q - x[2]) % Q; r[3] = x[0];
}
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void setup(int q, int h) {
    Q = q; HO = h; KC = (q - 1) / (2 * h); NCL = q * (q + 1); NN = NCL * KC;
    for (int x = 0; x < q; x++) for (int y = 0; y < q; y++) MUL[x][y] = (uint8_t)(x * y % q);
    int g = 0;
    for (int c = 2; c < q && !g; c++) {
        int x = 1, cnt = 0;
        do { x = x * c % q; cnt++; } while (x != 1 && cnt < q);
        if (cnt == q - 1) g = c;
    }
    int x = 1;
    for (int i = 0; i < q - 1; i++) { EXPT[i] = x; DLOG[x] = i; x = x * g % q; }
    DLOG[0] = -1;
    for (int v = 1; v < q; v++) { DLK[v] = DLOG[v] % KC; INVF[v] = EXPT[(q - 1 - DLOG[v]) % (q - 1)]; }
    DLK[0] = 0; INVF[0] = 0;
    int step = (q - 1) / h;
    for (int k = 0; k < h; k++) {
        int e1 = (k * step) % (q - 1), e2 = (q - 1 - e1) % (q - 1);
        HM[k][0] = EXPT[e1]; HM[k][1] = 0; HM[k][2] = 0; HM[k][3] = EXPT[e2];
    }
    memset(CL, 0xFF, sizeof CL); memset(C0, 0xFF, sizeof C0);
    BASE = malloc((size_t)NCL * 4); BKREF = malloc(NCL); BSET = calloc(NCL, 1); CNTL = calloc(NN, 1);
    int ncls = 0;
#define PROC(A_, B_, C_, D_) do { int a_ = (A_), b_ = (B_), c_ = (C_), d_ = (D_); \
        int p_ = MUL[a_][c_], r_ = MUL[a_][d_], t_ = MUL[b_][d_]; uint16_t m_; \
        if (p_) { if (CL[p_ * q + r_] == 0xFFFF) CL[p_ * q + r_] = ncls++; m_ = CL[p_ * q + r_]; } \
        else { if (C0[r_ * q + t_] == 0xFFFF) C0[r_ * q + t_] = ncls++; m_ = C0[r_ * q + t_]; } \
        int ref_ = a_ ? a_ : b_; uint32_t L_ = (uint32_t)m_ * KC + DLK[ref_]; \
        if (!BSET[m_]) { BSET[m_] = 1; BASE[4 * (size_t)m_] = a_; BASE[4 * (size_t)m_ + 1] = b_; BASE[4 * (size_t)m_ + 2] = c_; BASE[4 * (size_t)m_ + 3] = d_; BKREF[m_] = (uint8_t)DLK[ref_]; } \
        if (CNTL[L_] < 255) CNTL[L_]++; } while (0)
    for (int a = 1; a < q; a++) {
        int ia = INVF[a];
        for (int b = 0; b < q; b++) for (int c = 0; c < q; c++) {
            int d = MUL[addq(1, MUL[b][c])][ia];
            PROC(a, b, c, d);
        }
    }
    for (int b = 1; b < q; b++) {
        int c = (q - INVF[b]) % q;
        for (int d = 0; d < q; d++) PROC(0, b, c, d);
    }
#undef PROC
    if (ncls != NCL) { fprintf(stderr, "setup: %d classes, expected %d\n", ncls, NCL); exit(2); }
    for (uint32_t l = 0; l < (uint32_t)NN; l++) if (CNTL[l] != 2 * h) { fprintf(stderr, "setup: label %u hit %d times\n", l, CNTL[l]); exit(2); }
    if (KC != KCC) { fprintf(stderr, "KCC mismatch\n"); exit(2); }
    for (uint32_t l = 0; l < (uint32_t)NN; l++) { int x[4]; repof(l, x); if (LAB(x[0], x[1], x[2], x[3]) != l) { fprintf(stderr, "repof check failed at %u\n", l); exit(2); } }
    IDL = LAB(1, 0, 0, 1);
    fprintf(stderr, "setup q=%d h=%d K=%d classes=%d N=%d idlabel=%u (primitive root %d)\n", q, h, KC, ncls, NN, IDL, g);
}

/* ---------- double cosets ---------- */
static int32_t *dc_of;      /* label -> double coset id (regular), -1 (not regular), -2 (unassigned) */
static int nDC;
static uint8_t (*dc_rep)[4];
static int32_t *dc_inv;

static void enum_dc(void) {
    dc_of = malloc(sizeof(int32_t) * NN);
    for (int l = 0; l < NN; l++) dc_of[l] = -2;
    dc_rep = malloc(sizeof(*dc_rep) * (NN / (HO) + 16)); nDC = 0;
    int nonreg = 0;
    for (uint32_t l = 0; l < (uint32_t)NN; l++) {
        if (dc_of[l] != -2) continue;
        int z[4]; repof(l, z);
        uint32_t labs[64]; int reg = 1;
        for (int k = 0; k < HO; k++) { int r[4]; mm(z, HM[k], r); labs[k] = LAB(r[0], r[1], r[2], r[3]); }
        for (int k = 0; k < HO && reg; k++) for (int j = 0; j < k; j++) if (labs[j] == labs[k]) { reg = 0; break; }
        if (reg) {
            int id = nDC++;
            for (int k = 0; k < HO; k++) { if (dc_of[labs[k]] != -2) { fprintf(stderr, "enum: overlap\n"); exit(2); } dc_of[labs[k]] = id; }
            for (int t = 0; t < 4; t++) dc_rep[id][t] = z[t];
        } else {
            nonreg++;
            for (int k = 0; k < HO; k++) dc_of[labs[k]] = -1;
        }
    }
    dc_inv = malloc(sizeof(int32_t) * (nDC + 1));
    for (int i = 0; i < nDC; i++) {
        int z[4] = { dc_rep[i][0], dc_rep[i][1], dc_rep[i][2], dc_rep[i][3] }, zi[4];
        minv(z, zi);
        dc_inv[i] = dc_of[LAB(zi[0], zi[1], zi[2], zi[3])];
    }
    fprintf(stderr, "double cosets: regular %d, non-regular %d\n", nDC, nonreg);
}

/* ---------- BFS ---------- */
static int DLs[10][4], ELs[10][4];   /* d-list (B->A steps) and e-list (A->B steps), one element per coset */
static uint8_t *DIST;
static uint32_t *UN[2], *FR, *NX;
static long nun[2];

static inline uint32_t nbx(const int *x, int side, int j) {   /* neighbour j of the vertex with representative x */
    const int *g = side == 0 ? ELs[j] : DLs[j];
    int r0 = addq(MUL[g[0]][x[0]], MUL[g[1]][x[2]]);
    int r1 = addq(MUL[g[0]][x[1]], MUL[g[1]][x[3]]);
    int r2 = addq(MUL[g[2]][x[0]], MUL[g[3]][x[2]]);
    int r3 = addq(MUL[g[2]][x[1]], MUL[g[3]][x[3]]);
    return LAB(r0, r1, r2, r3);
}

/* BFS from root (side rs, label IDL) up to level 8. Afterwards nun[1-rs]... : nun[s] = unvisited on side s (root excluded). */
static void bfs8(int rs) {
    memset(DIST, 255, 2 * (size_t)NN);
    for (int s = 0; s < 2; s++) {
        uint32_t k = 0;
        for (uint32_t l = 0; l < (uint32_t)NN; l++) if (!(s == rs && l == IDL)) UN[s][k++] = l;
        nun[s] = k;
    }
    DIST[rs * (size_t)NN + IDL] = 0;
    uint32_t nf = 1; FR[0] = IDL; int sL = rs;
    for (int L = 0; L < 8 && nf; L++) {
        int o = 1 - sL;
        uint8_t *Do = DIST + (size_t)o * NN, *Ds = DIST + (size_t)sL * NN;
        uint32_t nn = 0;
        if ((long)nf * 3 < nun[o] * 2) {               /* top-down */
            for (uint32_t i = 0; i < nf; i++) {
                uint32_t v = FR[i]; int x[4]; repof(v, x);
                for (int j = 0; j < 10; j++) { uint32_t w = nbx(x, sL, j); if (Do[w] == 255) { Do[w] = (uint8_t)(L + 1); NX[nn++] = w; } }
            }
            uint32_t k = 0;
            for (long i = 0; i < nun[o]; i++) { uint32_t u = UN[o][i]; if (Do[u] == 255) UN[o][k++] = u; }
            nun[o] = k;
        } else {                                       /* bottom-up */
            uint32_t k = 0;
            for (long i = 0; i < nun[o]; i++) {
                uint32_t u = UN[o][i]; int found = 0; int x[4]; repof(u, x);
                for (int j = 0; j < 10 && !found; j++) { uint32_t w = nbx(x, o, j); if (Ds[w] == L) found = 1; }
                if (found) { Do[u] = (uint8_t)(L + 1); NX[nn++] = u; } else UN[o][k++] = u;
            }
            nun[o] = k;
        }
        uint32_t *t = FR; FR = NX; NX = t; nf = nn; sL = o;
    }
}

static void set_lists(int i, int j) {
    int z1[4], z2[4], zi[4], r[4], h[4];
    for (int t = 0; t < 4; t++) { z1[t] = dc_rep[i][t]; z2[t] = dc_rep[j][t]; }
    for (int k = 0; k < HO; k++) {
        for (int t = 0; t < 4; t++) h[t] = HM[k][t];
        mm(z1, h, r); for (int t = 0; t < 4; t++) DLs[k][t] = r[t];
        mm(z2, h, r); for (int t = 0; t < 4; t++) DLs[HO + k][t] = r[t];
        minv(z1, zi); mm(zi, h, r); for (int t = 0; t < 4; t++) ELs[k][t] = r[t];
        minv(z2, zi); mm(zi, h, r); for (int t = 0; t < 4; t++) ELs[HO + k][t] = r[t];
    }
}

static long long EVALS = 0;
/* exact full cost of the pair (i,j) of double cosets. Returns LLONG_MAX if the A-part already reaches bound. */
static long long cost_pair(int i, int j, long long bound, int *symout) {
    set_lists(i, j);
    int sym = (dc_inv[i] == j) || (dc_inv[i] == i && dc_inv[j] == j);
    if (symout) *symout = sym;
    EVALS++;
    bfs8(0);
    long long uB = nun[1], uA = nun[0];
    if (uB + uA >= bound) return LLONG_MAX;
    if (sym) return uB + 2 * uA;
    bfs8(1);
    return uB + uA + nun[1];
}

/* set the lists from two arbitrary SL matrices (both double cosets must be regular and disjoint) */
static void set_lists_mat(const int *z1, const int *z2) {
    int zi[4], r[4], h[4];
    for (int k = 0; k < HO; k++) {
        for (int t = 0; t < 4; t++) h[t] = HM[k][t];
        mm(z1, h, r); for (int t = 0; t < 4; t++) DLs[k][t] = r[t];
        mm(z2, h, r); for (int t = 0; t < 4; t++) DLs[HO + k][t] = r[t];
        minv(z1, zi); mm(zi, h, r); for (int t = 0; t < 4; t++) ELs[k][t] = r[t];
        minv(z2, zi); mm(zi, h, r); for (int t = 0; t < 4; t++) ELs[HO + k][t] = r[t];
    }
}

/* ---------- validation against coset2 (PGL key encoding of c8-wild/coset2.c, PSL = square determinant) ---------- */
static int VQ, VQ2, VQ3, VNK;
static void vdec(long key, int *x) {
    if (key < VQ3) { x[0] = 1; x[1] = key / VQ2; x[2] = (key / VQ) % VQ; x[3] = key % VQ; }
    else { long k = key - VQ3; x[0] = 0; x[1] = 1; x[2] = k / VQ; x[3] = k % VQ; }
}
static long vkof(const int *x) {
    if (x[0]) { int s = INVF[x[0]]; int b = x[1] * s % VQ, c = x[2] * s % VQ, d = x[3] * s % VQ; return b * (long)VQ2 + c * VQ + d; }
    { int s = INVF[x[1]]; int c = x[2] * s % VQ, d = x[3] * s % VQ; return VQ3 + c * VQ + d; }
}
static int vvalid_psl(long key) {   /* non-singular and square determinant */
    int x[4]; vdec(key, x); int det;
    if (x[0]) det = ((x[3] - x[1] * x[2]) % VQ + VQ) % VQ; else det = (VQ - x[2]) % VQ;
    if (det == 0) return 0;
    int p = 1; for (int e = 0; e < (VQ - 1) / 2; e++) p = p * det % VQ;
    return p == 1;
}
static void vmul(const int *x, const int *y, int *r) {
    r[0] = (x[0] * y[0] + x[1] * y[2]) % VQ; r[1] = (x[0] * y[1] + x[1] * y[3]) % VQ;
    r[2] = (x[2] * y[0] + x[3] * y[2]) % VQ; r[3] = (x[2] * y[1] + x[3] * y[3]) % VQ;
}
/* PGL normal form -> SL matrix (divide by a square root of the determinant) */
static void vtosl(long key, int *m) {
    int x[4]; vdec(key, x); int det;
    if (x[0]) det = ((x[3] - x[1] * x[2]) % VQ + VQ) % VQ; else det = (VQ - x[2]) % VQ;
    int s = -1; for (int t = 1; t < VQ && s < 0; t++) if (t * t % VQ == det) s = t;
    if (s < 0) { fprintf(stderr, "not a square det\n"); exit(2); }
    int si = INVF[s];
    for (int t = 0; t < 4; t++) m[t] = x[t] * si % VQ;
}

static void validate(const char *fn) {
    VQ = Q; VQ2 = Q * Q; VQ3 = Q * Q * Q; VNK = VQ3 + VQ2;
    long g0 = -1;
    for (long k = 0; k < VNK && g0 < 0; k++) {
        if (!vvalid_psl(k)) continue;
        int g[4]; vdec(k, g); int p[4] = { g[0], g[1], g[2], g[3] }; int ord = 1;
        int id[4] = { 1, 0, 0, 1 };
        while (vkof(p) != vkof(id) && ord < HO) { int t[4]; vmul(p, g, t); memcpy(p, t, sizeof t); ord++; }
        if (ord == HO && vkof(p) == vkof(id)) g0 = k;
    }
    int G[4]; vtosl(g0, G);
    int tr = (G[0] + G[3]) % Q; int lam = -1;
    for (int l = 1; l < Q && lam < 0; l++) if ((l * l % Q - tr * l % Q + 1 + Q) % Q == 0) lam = l;
    int mu = INVF[lam];
    /* eigenvectors */
    int v1[2], v2[2];
    if (G[1] || (lam - G[0] + Q) % Q) { v1[0] = G[1]; v1[1] = (lam - G[0] + Q) % Q; }
    else { v1[0] = (lam - G[3] + Q) % Q; v1[1] = G[2]; }
    if (G[1] || (mu - G[0] + Q) % Q) { v2[0] = G[1]; v2[1] = (mu - G[0] + Q) % Q; }
    else { v2[0] = (mu - G[3] + Q) % Q; v2[1] = G[2]; }
    int P[4] = { v1[0], v2[0], v1[1], v2[1] };
    int det = ((P[0] * P[3] - P[1] * P[2]) % Q + Q) % Q; int di = INVF[det];
    int adj[4] = { P[3], (Q - P[1]) % Q, (Q - P[2]) % Q, P[0] };
    /* check: adj(P) G P = det * diag(lam, mu) */
    int t1[4], t2[4]; vmul(adj, G, t1); vmul(t1, P, t2);
    fprintf(stderr, "validate: g0 key %ld lam %d mu %d; conj check offdiag %d %d (diag %d %d)\n", g0, lam, mu, t2[1], t2[2],
            t2[0] * di % Q, t2[3] * di % Q);
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(2); }
    char line[4096]; int nok = 0, nbad = 0; long n = 0;
    while (fgets(line, sizeof line, f)) {
        long idx; long k1, k2; long ub, ua; char w1[16], w2[16], w3[16], w4[16];
        int nf = sscanf(line, "cand %ld %s %ld %ld %s %ld %s %ld", &idx, w1, &k1, &k2, w2, &ub, w3, &ua);
        if (nf != 8) continue;
        /* z's */
        int zz[2][4]; long ks[2] = { k1, k2 };
        for (int e = 0; e < 2; e++) {
            int m[4]; vtosl(ks[e], m);
            int t3[4], t4[4]; vmul(adj, m, t3); vmul(t3, P, t4);
            for (int q4 = 0; q4 < 4; q4++) zz[e][q4] = t4[q4] * di % Q;
        }
        set_lists_mat(zz[0], zz[1]);
        bfs8(0);
        long u1 = nun[1], u2 = nun[0];
        if (u1 == ub && u2 == ua) nok++; else { nbad++; if (nbad < 5) fprintf(stderr, "mismatch cand %ld: mine %ld %ld coset2 %ld %ld\n", idx, u1, u2, ub, ua); }
        n++;
    }
    fclose(f);
    printf("validate %s: %ld candidates, matching (uncB,uncA) %d, mismatching %d\n", fn, n, nok, nbad);
}

/* ---------- random search and annealing ---------- */
static uint64_t rstate = 88172645463325252ULL;
static inline uint64_t rnd64(void) { rstate ^= rstate << 13; rstate ^= rstate >> 7; rstate ^= rstate << 17; return rstate; }
static inline double urand(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static inline int rand_dc(void) { return (int)(rnd64() % (uint64_t)nDC); }

static void write_pair(FILE *f, int i, int j, long long C) {
    fprintf(f, "PAIR %d %d C %lld", i, j, C);
    for (int t = 0; t < 4; t++) fprintf(f, " %d", dc_rep[i][t]);
    for (int t = 0; t < 4; t++) fprintf(f, " %d", dc_rep[j][t]);
    fprintf(f, "\n"); fflush(f);
}

static void anneal(double seconds, uint64_t seed, double COOL, double REHEAT, int K, const char *tag) {
    const double TMAX = 1.5, TMIN = 0.15; const long long REHEATSTEPS = 400;
    rstate ^= seed * 0x9E3779B97F4A7C15ULL; for (int t = 0; t < 10; t++) rnd64();
    char fn[256]; snprintf(fn, sizeof fn, "%s_best.txt", tag); FILE *fb = fopen(fn, "w");
    snprintf(fn, sizeof fn, "%s_chains.log", tag); FILE *fl = fopen(fn, "w");
    double t0 = now(), deadline = t0 + seconds;
    int i = rand_dc(), j; do { j = rand_dc(); } while (j == i);
    long long Cc = cost_pair(i, j, LLONG_MAX, NULL);
    long long chainmin = Cc, gbest = Cc; int gi = i, gj = j;
    double lastheat = now(), lastimp = now(), chain_t0 = now(); long long steps = 0, lastimpstep = 0, chain_e0 = EVALS;
    int nchains = 1; long long nacc = 0;
    double lastprint = now();
    fprintf(fl, "start seed %llu COOL %g REHEAT %g K %d\n", (unsigned long long)seed, COOL, REHEAT, K);
    while (now() < deadline) {
        double tn = now();
        double T = TMAX * pow(0.5, (tn - lastheat) / COOL); if (T < TMIN) T = TMIN;
        int slot = (int)(rnd64() & 1); int other = slot ? i : j;
        long long bestC = LLONG_MAX; int bestn = -1;
        for (int k = 0; k < K; k++) {
            int nw = rand_dc(); if (nw == other) continue;
            long long c = cost_pair(other, nw, bestC, NULL);
            if (c < bestC) { bestC = c; bestn = nw; }
        }
        if (bestn >= 0) {
            double Eb = bestC / 5.0, Ec = Cc / 5.0;
            if (Eb <= Ec || exp((Ec - Eb) / T) > urand()) {
                if (slot) i = bestn; else j = bestn;
                Cc = bestC; nacc++;
            }
        }
        steps++;
        if (Cc < chainmin) { chainmin = Cc; lastimp = now(); lastimpstep = steps; }
        if (Cc < gbest) { gbest = Cc; gi = i; gj = j; write_pair(fb, i, j, Cc); fprintf(fl, "BEST %lld units %.1f t %.0f evals %lld\n", Cc, Cc / 5.0, now() - t0, EVALS); }
        if (now() - lastimp > REHEAT && steps - lastimpstep > REHEATSTEPS) {
            fprintf(fl, "CHAIN %d min %lld units %.1f secs %.0f evals %lld pair %d %d\n", nchains, chainmin, chainmin / 5.0,
                    now() - chain_t0, EVALS - chain_e0, i, j);
            fflush(fl);
            nchains++; chain_t0 = now(); chain_e0 = EVALS;
            i = rand_dc(); do { j = rand_dc(); } while (j == i);
            Cc = cost_pair(i, j, LLONG_MAX, NULL); chainmin = Cc; lastheat = now(); lastimp = now(); lastimpstep = steps; T = TMAX;
        }
        if (now() - lastprint > 60) {
            fprintf(fl, "t %.0f steps %lld evals %lld cur %lld (units %.1f) best %lld T %.2f acc %lld chain %d\n", now() - t0, steps, EVALS, Cc, Cc / 5.0, gbest, T, nacc, nchains);
            fflush(fl); lastprint = now();
        }
    }
    fprintf(fl, "END steps %lld evals %lld best %lld units %.1f pair %d %d chains %d\n", steps, EVALS, gbest, gbest / 5.0, gi, gj, nchains);
    fclose(fl); fclose(fb);
    printf("anneal done: evals %lld best %lld\n", EVALS, gbest);
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: fastc validate|bench|anneal|symscan ...\n"); return 2; }
    setup(181, 5);
    DIST = malloc(2 * (size_t)NN);
    UN[0] = malloc(4 * (size_t)NN); UN[1] = malloc(4 * (size_t)NN); FR = malloc(4 * (size_t)NN); NX = malloc(4 * (size_t)NN);
    if (!strcmp(argv[1], "validate")) {
        enum_dc();   /* not needed for validation, but gives the double coset count */
        validate(argv[2]);
        return 0;
    }
    enum_dc();
    if (!strcmp(argv[1], "bench")) {
        int n = atoi(argv[2]); rstate ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
        double t0 = now(); long long mn = LLONG_MAX, sum = 0; int nsym = 0;
        for (int t = 0; t < n; t++) {
            int i = rand_dc(), j; do { j = rand_dc(); } while (j == i);
            int sym; long long c = cost_pair(i, j, LLONG_MAX, &sym);
            if (c < mn) mn = c; sum += c; nsym += sym;
            printf("bench %d %d C %lld sym %d\n", i, j, c, sym); fflush(stdout);
        }
        fprintf(stderr, "bench: %d pairs, %.2f ms per pair, min %lld mean %.1f sym %d\n", n, (now() - t0) * 1e3 / n, mn, (double)sum / n, nsym);
        return 0;
    }
    if (!strcmp(argv[1], "anneal")) {
        anneal(atof(argv[2]), (uint64_t)atoll(argv[3]), atof(argv[4]), atof(argv[5]), atoi(argv[6]), argv[7]);
        return 0;
    }
    if (!strcmp(argv[1], "symscan")) {
        FILE *f = fopen(argv[2], "w"); double t0 = now(); long n = 0;
        int nself = 0; for (int i = 0; i < nDC; i++) if (dc_inv[i] == i) nself++;
        fprintf(stderr, "self-inverse double cosets: %d\n", nself);
        for (int i = 0; i < nDC; i++) {
            int j = dc_inv[i]; if (j < 0 || j <= i) continue;
            if (j == i) continue;
            int sym; long long c = cost_pair(i, j, LLONG_MAX, &sym);
            fprintf(f, "%d %d C %lld sym %d\n", i, j, c, sym); n++;
            if (n % 5000 == 0) { fprintf(stderr, "symscan %ld pairs, %.0f s\n", n, now() - t0); fflush(f); }
        }
        fclose(f);
        fprintf(stderr, "symscan done: %ld pairs in %.0f s\n", n, now() - t0);
        return 0;
    }
    return 2;
}
