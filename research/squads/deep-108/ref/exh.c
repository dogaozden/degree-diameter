/* exh.c (c6b-exhaust, handsoff-108): exhaustive scan of the regular double cosets H z H of G = PSL(2,q) or
 * PGL(2,q) (q prime) for H = <r, s> dihedral of order 10 given by two matrices.
 *
 * Graph X(G,H,HzH): vertices = left cosets Hx on side A and on side B; Hx (A) ~ Hy (B) iff x y^-1 in HzH. Degree 10.
 * Cost (plain vertices, 0 = diameter 8, as fastc.c of c8b-coset):
 *   C = uBA + uAA + uBB,  uBA = #B at distance > 7 from the A root, uAA = #A at distance > 8 from the A root,
 *   uBB = #B at distance > 8 from the B root.  (A-B pairs and A-A pairs need only the A root, B-B pairs the B root,
 *   because G is transitive on each side.)
 * Labels: every group element is stored under a key (normalised matrix: det scaled to 1 or the non-square class, sign
 * fixed); T[key] = left coset label. Table built once per run (|G| entries).
 * Classes: X(G,H,D^-1) is X(G,H,D) with the sides swapped, and X(G,H,nDn^-1) = X(G,H,D) for n in N_PGL(H)
 * (map Hx -> Hnx). Each class is represented by its smallest double coset id; the class size is its orbit size.
 *
 * usage: exh q psl r00 r01 r10 r11 s00 s01 s10 s11 MODE [args]
 *   info                       group, double cosets, normaliser, classes
 *   member z00 z01 z10 z11     costs of the double coset H z H for the given matrix z (validation)
 *   scanA OUT                  uBA, uAA for every class representative (resumable, appends to OUT)
 *   scanB OUT THR              uBB for every class representative with uBA+uAA <= THR (resumable)
 *   symtest n                  C(D) = C(D^-1) = C(nDn^-1) on random classes; uBB = uAA when D = D^-1
 *   bench n                    time n A-root BFS on random classes
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <sys/mman.h>

#define MAXQ 256
#define HO 10

static int Q, H2, PSL, M2, NSQ;
static uint64_t BASE2, NKEY, GORD;
static uint32_t NN, IDL;
static uint8_t MUL[MAXQ][MAXQ];
static int INVV[MAXQ], LAM[MAXQ], BITD[MAXQ];
static uint32_t *T;                 /* key -> coset label */
static uint8_t (*REP)[4];           /* label -> normalised representative */
static int HL[HO][4];               /* H, HL[0] = identity */
static int GEN[2][4];               /* normalised generators r, s */
static int32_t *DCOF;               /* label -> double coset id, -1 non-regular */
static uint8_t (*DCREP)[4];         /* double coset id -> representative z */
static uint32_t NDC;
static int32_t *INVDC;              /* id -> id of H z^-1 H */
static int NAMB;                    /* normaliser of H in PGL(2,q) (as list of elements) */
static int AMB[64][4];
static int32_t *CONJ[64];           /* CONJ[k][id] = id of n_k z n_k^-1 */
static uint32_t *par, *CLS, *ORB, NCLS;
static int DLSm[HO][4], ELSm[HO][4];
static uint64_t *VIS[2], *CURB;
static uint32_t *UN[2], *FR, *NX;
static long nun[2];

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static int pw(int b, long e) { long r = 1, x = b % Q; while (e) { if (e & 1) r = r * x % Q; x = x * x % Q; e >>= 1; } return (int)r; }
static inline int addq(int u, int v) { int s = u + v; return s >= Q ? s - Q : s; }
static inline int subq(int u, int v) { int s = u - v; return s < 0 ? s + Q : s; }
static void fatal(const char *m) { fprintf(stderr, "FATAL: %s\n", m); exit(2); }

static void setup_field(int q) {
    Q = q; H2 = (q - 1) / 2;
    for (int x = 0; x < q; x++) for (int y = 0; y < q; y++) MUL[x][y] = (uint8_t)(x * y % q);
    INVV[0] = 0; for (int x = 1; x < q; x++) INVV[x] = pw(x, q - 2);
    NSQ = 0; for (int t = 2; t < q; t++) if (pw(t, (q - 1) / 2) == q - 1) { NSQ = t; break; }
    LAM[0] = 0; BITD[0] = 0;
    for (int d = 1; d < q; d++) {
        int sq = (pw(d, (q - 1) / 2) == 1), target = sq ? 1 : NSQ;
        BITD[d] = !sq; LAM[d] = -1;
        for (int l = 1; l < q; l++) if (MUL[MUL[l][l]][d] == target) { LAM[d] = l; break; }
        if (LAM[d] < 0) fatal("no scalar");
    }
}

/* scale to det 1 (square det) or det NSQ (non-square det), then fix the sign; returns the det-class bit */
static inline int norm_mat(int *r) {
    int det = subq(MUL[r[0]][r[3]], MUL[r[1]][r[2]]);
    int lam = LAM[det];                       /* LAM[1] = 1: no branch on the det class */
    int v0 = MUL[lam][r[0]], v1 = MUL[lam][r[1]], v2 = MUL[lam][r[2]], v3 = MUL[lam][r[3]];
    int bit = BITD[det];
    int neg = v0 ? (v0 > H2) : (v1 > H2);     /* sign: make a (or b if a = 0) in the first half */
    int n0 = v0 ? Q - v0 : 0, n1 = v1 ? Q - v1 : 0, n2 = v2 ? Q - v2 : 0, n3 = v3 ? Q - v3 : 0;
    r[0] = neg ? n0 : v0; r[1] = neg ? n1 : v1; r[2] = neg ? n2 : v2; r[3] = neg ? n3 : v3;
    return bit;
}
static inline uint64_t keyof(const int *r, int bit) {
    uint64_t b = (M2 == 2) ? (uint64_t)bit : 0;
    if (r[0]) return ((((uint64_t)(r[0] - 1) * Q + r[1]) * Q + r[2]) * M2) + b;
    return BASE2 + (((uint64_t)(r[1] - 1) * Q + r[3]) * M2) + b;
}
/* key -> normalised matrix; m2 = 1 (PSL keys) or 2 (PGL keys, both det classes) */
static void decode(uint64_t k, int m2, int *r) {
    uint64_t base2 = (uint64_t)H2 * Q * Q * m2;
    if (k < base2) {
        int bit = (m2 == 2) ? (int)(k & 1) : 0;
        uint64_t x = k / m2;
        int c = (int)(x % Q); x /= Q;
        int b = (int)(x % Q); x /= Q;
        int a = (int)x + 1;
        int delta = bit ? NSQ : 1;
        r[0] = a; r[1] = b; r[2] = c; r[3] = MUL[addq(delta, MUL[b][c])][INVV[a]];
    } else {
        uint64_t k2 = k - base2;
        int bit = (m2 == 2) ? (int)(k2 & 1) : 0;
        uint64_t x = k2 / m2;
        int d = (int)(x % Q); x /= Q;
        int b = (int)x + 1;
        int delta = bit ? NSQ : 1;
        r[0] = 0; r[1] = b; r[2] = MUL[(Q - delta) % Q][INVV[b]]; r[3] = d;
    }
}
static inline void mulm(const int *x, const int *y, int *r) {
    r[0] = addq(MUL[x[0]][y[0]], MUL[x[1]][y[2]]);
    r[1] = addq(MUL[x[0]][y[1]], MUL[x[1]][y[3]]);
    r[2] = addq(MUL[x[2]][y[0]], MUL[x[3]][y[2]]);
    r[3] = addq(MUL[x[2]][y[1]], MUL[x[3]][y[3]]);
}
static inline void adjm(const int *x, int *r) { r[0] = x[3]; r[1] = x[1] ? Q - x[1] : 0; r[2] = x[2] ? Q - x[2] : 0; r[0 + 3] = x[0]; }

/* coset label of an arbitrary group element m (H m) */
static inline uint32_t labof(const int *m) {
    int r[4] = { m[0], m[1], m[2], m[3] };
    int bit = norm_mat(r);
    if (M2 == 1 && bit) fatal("labof: non-square det in PSL table");
    return T[keyof(r, bit)];
}

static void make_H(void) {
    int gen[2][4];
    for (int g = 0; g < 2; g++) { for (int i = 0; i < 4; i++) gen[g][i] = GEN[g][i]; if (norm_mat(gen[g]) && M2 == 1) fatal("generator not in PSL"); }
    for (int g = 0; g < 2; g++) for (int i = 0; i < 4; i++) GEN[g][i] = gen[g][i];
    int n = 1; HL[0][0] = 1; HL[0][1] = 0; HL[0][2] = 0; HL[0][3] = 1;
    for (int i = 0; i < n; i++) for (int g = 0; g < 2; g++) {
        int p[4]; mulm(HL[i], gen[g], p);
        int bit = norm_mat(p);
        if (M2 == 1 && bit) fatal("product not in PSL");
        int found = 0; for (int j = 0; j < n; j++) if (!memcmp(HL[j], p, sizeof p)) { found = 1; break; }
        if (!found) { if (n >= HO) fatal("H has more than 10 elements"); memcpy(HL[n], p, sizeof p); n++; }
    }
    if (n != HO) { fprintf(stderr, "H order %d\n", n); fatal("H order is not 10"); }
}

static void label_group(void) {
    size_t tb = ((size_t)NKEY * 4 + (1u << 21) - 1) & ~(size_t)((1u << 21) - 1);
    T = aligned_alloc(1u << 21, tb);               /* 2 MB aligned, huge pages if the kernel allows (fewer TLB misses) */
    if (!T) fatal("alloc T");
    madvise(T, tb, MADV_HUGEPAGE);
    memset(T, 0xff, NKEY * 4);
    REP = malloc((GORD / HO + 16) * 4);
    uint32_t nl = 0;
    for (uint64_t k = 0; k < NKEY; k++) {
        if (T[k] != 0xffffffffu) continue;
        int e[4]; decode(k, M2, e);
        { int t[4] = { e[0], e[1], e[2], e[3] }; int bit = norm_mat(t);
          if (memcmp(t, e, sizeof e) || keyof(e, bit) != k) fatal("decode/keyof mismatch"); }
        for (int j = 0; j < HO; j++) {
            int p[4]; mulm(HL[j], e, p);
            int bit = norm_mat(p); uint64_t kk = keyof(p, bit);
            if (T[kk] != 0xffffffffu) fatal("coset labelling collision");
            T[kk] = nl;
        }
        for (int i = 0; i < 4; i++) REP[nl][i] = (uint8_t)e[i];
        nl++;
    }
    NN = nl;
    if ((uint64_t)NN * HO != GORD) fatal("coset count != |G|/10");
    IDL = labof((int[4]){ 1, 0, 0, 1 });
}

/* regular double cosets = orbits of H acting on the right on H\G with trivial stabiliser */
static void enum_dc(void) {
    DCOF = malloc(sizeof(int32_t) * NN);
    for (uint32_t l = 0; l < NN; l++) DCOF[l] = -2;
    DCREP = malloc(sizeof(*DCREP) * (NN / HO + 16));
    NDC = 0; uint32_t nonreg = 0;
    for (uint32_t l = 0; l < NN; l++) {
        if (DCOF[l] != -2) continue;
        int x[4] = { REP[l][0], REP[l][1], REP[l][2], REP[l][3] };
        uint32_t lab[HO]; int reg = 1;
        for (int j = 0; j < HO; j++) { int p[4]; mulm(x, HL[j], p); lab[j] = labof(p); }
        for (int j = 0; j < HO && reg; j++) for (int i = 0; i < j; i++) if (lab[i] == lab[j]) { reg = 0; break; }
        if (reg) {
            uint32_t id = NDC++;
            for (int j = 0; j < HO; j++) { if (DCOF[lab[j]] != -2) fatal("orbit overlap"); DCOF[lab[j]] = (int32_t)id; }
            for (int i = 0; i < 4; i++) DCREP[id][i] = (uint8_t)x[i];
        } else {
            nonreg++;
            for (int j = 0; j < HO; j++) DCOF[lab[j]] = -1;
        }
    }
    fprintf(stderr, "double cosets: regular %u, labels in non-regular ones %u\n", NDC, nonreg);
}

static void build_inv(void) {
    INVDC = malloc(sizeof(int32_t) * NDC);
    for (uint32_t id = 0; id < NDC; id++) {
        int z[4] = { DCREP[id][0], DCREP[id][1], DCREP[id][2], DCREP[id][3] }, zi[4];
        adjm(z, zi);
        int32_t v = DCOF[labof(zi)];
        if (v < 0) fatal("inverse of a regular double coset is not regular");
        INVDC[id] = v;
    }
}

static void build_normalizer(void) {
    uint64_t nkp = 2ULL * H2 * Q * (Q + 1);      /* all of PGL(2,q) in the PGL key space */
    NAMB = 0;
    for (uint64_t k = 0; k < nkp; k++) {
        int n[4], na[4], t[4], p[4];
        decode(k, 2, n); adjm(n, na);
        mulm(n, GEN[0], t); mulm(t, na, p);
        if (labof(p) != IDL) continue;
        mulm(n, GEN[1], t); mulm(t, na, p);
        if (labof(p) != IDL) continue;
        if (NAMB >= 64) fatal("normaliser too big");
        for (int i = 0; i < 4; i++) AMB[NAMB][i] = n[i];
        NAMB++;
    }
    for (int k = 0; k < NAMB; k++) {
        CONJ[k] = malloc(sizeof(int32_t) * NDC);
        int na[4]; adjm(AMB[k], na);
        for (uint32_t id = 0; id < NDC; id++) {
            int z[4] = { DCREP[id][0], DCREP[id][1], DCREP[id][2], DCREP[id][3] }, t[4], p[4];
            mulm(AMB[k], z, t); mulm(t, na, p);
            int32_t v = DCOF[labof(p)];
            if (v < 0) fatal("conjugate not regular");
            CONJ[k][id] = v;
        }
    }
}

static uint32_t findp(uint32_t x) { while (par[x] != x) { par[x] = par[par[x]]; x = par[x]; } return x; }
static void unite(uint32_t a, uint32_t b) { a = findp(a); b = findp(b); if (a != b) { if (a < b) par[b] = a; else par[a] = b; } }

static void build_classes(void) {
    par = malloc(4 * (size_t)NDC);
    for (uint32_t i = 0; i < NDC; i++) par[i] = i;
    for (uint32_t id = 0; id < NDC; id++) { unite(id, (uint32_t)INVDC[id]); for (int k = 0; k < NAMB; k++) unite(id, (uint32_t)CONJ[k][id]); }
    uint32_t *sz = calloc(NDC, 4);
    for (uint32_t id = 0; id < NDC; id++) sz[findp(id)]++;
    CLS = malloc(4 * (size_t)NDC); ORB = malloc(4 * (size_t)NDC); NCLS = 0;
    for (uint32_t id = 0; id < NDC; id++) if (findp(id) == id) { CLS[NCLS] = id; ORB[NCLS] = sz[id]; NCLS++; }
    free(sz);
}

/* ---------- BFS (as fastc.c, with the generic labels) ---------- */
static inline int getb(const uint64_t *B, uint32_t i) { return (int)((B[i >> 6] >> (i & 63)) & 1); }
static inline void setb(uint64_t *B, uint32_t i) { B[i >> 6] |= 1ULL << (i & 63); }
static inline void clrb(uint64_t *B, uint32_t i) { B[i >> 6] &= ~(1ULL << (i & 63)); }

static void set_lists_mat(const int *z) {
    int zi[4]; adjm(z, zi);
    for (int j = 0; j < HO; j++) { mulm(z, HL[j], DLSm[j]); mulm(zi, HL[j], ELSm[j]); }
}
static inline uint32_t nbx(const int *x, int side, int j) {   /* neighbour j of the vertex with representative x */
    const int *g = side == 0 ? ELSm[j] : DLSm[j];
    int p[4];
    p[0] = addq(MUL[g[0]][x[0]], MUL[g[1]][x[2]]);
    p[1] = addq(MUL[g[0]][x[1]], MUL[g[1]][x[3]]);
    p[2] = addq(MUL[g[2]][x[0]], MUL[g[3]][x[2]]);
    p[3] = addq(MUL[g[2]][x[1]], MUL[g[3]][x[3]]);
    return labof(p);
}
/* batched BFS: the 10 neighbour keys of a few vertices are computed first and prefetched, so the table lookups overlap */
#define BATCH 3
static inline uint64_t keyprod(const int *p) { int r[4] = { p[0], p[1], p[2], p[3] }; int bit = norm_mat(r); return keyof(r, bit); }
static inline void nbkeys(const int *x, int side, uint64_t *kout) {
    for (int j = 0; j < HO; j++) {
        const int *g = side == 0 ? ELSm[j] : DLSm[j];
        int p[4];
        p[0] = addq(MUL[g[0]][x[0]], MUL[g[1]][x[2]]);
        p[1] = addq(MUL[g[0]][x[1]], MUL[g[1]][x[3]]);
        p[2] = addq(MUL[g[2]][x[0]], MUL[g[3]][x[2]]);
        p[3] = addq(MUL[g[2]][x[1]], MUL[g[3]][x[3]]);
        kout[j] = keyprod(p);
    }
}
static inline uint64_t nbkey(const int *x, int side, int j) {
    const int *g = side == 0 ? ELSm[j] : DLSm[j];
    int p[4];
    p[0] = addq(MUL[g[0]][x[0]], MUL[g[1]][x[2]]);
    p[1] = addq(MUL[g[0]][x[1]], MUL[g[1]][x[3]]);
    p[2] = addq(MUL[g[2]][x[0]], MUL[g[3]][x[2]]);
    p[3] = addq(MUL[g[2]][x[1]], MUL[g[3]][x[3]]);
    return keyprod(p);
}
static void bfs8(int rs) {
    size_t nw = ((size_t)NN + 63) / 64;
    memset(VIS[0], 0, nw * 8); memset(VIS[1], 0, nw * 8); memset(CURB, 0, nw * 8);
    for (int s = 0; s < 2; s++) {
        uint32_t k = 0;
        for (uint32_t l = 0; l < NN; l++) if (!(s == rs && l == IDL)) UN[s][k++] = l;
        nun[s] = k;
    }
    setb(VIS[rs], IDL); setb(CURB, IDL);
    uint32_t nf = 1; FR[0] = IDL; int sL = rs;
    uint64_t kb[BATCH * HO];
    for (int L = 0; L < 8 && nf; L++) {
        int o = 1 - sL;
        uint32_t nn = 0;
        if ((long)nf * 3 < nun[o] * 2) {                    /* top-down */
            for (uint32_t i0 = 0; i0 < nf; i0 += BATCH) {
                int nb = (int)((nf - i0 < BATCH) ? (nf - i0) : BATCH);
                for (int b = 0; b < nb; b++) {
                    int x[4] = { REP[FR[i0 + b]][0], REP[FR[i0 + b]][1], REP[FR[i0 + b]][2], REP[FR[i0 + b]][3] };
                    nbkeys(x, sL, kb + b * HO);
                }
                for (int t = 0; t < nb * HO; t++) __builtin_prefetch(&T[kb[t]]);
                for (int t = 0; t < nb * HO; t++) { uint32_t w = T[kb[t]]; if (!getb(VIS[o], w)) { setb(VIS[o], w); NX[nn++] = w; } }
            }
            uint32_t k = 0;
            for (long i = 0; i < nun[o]; i++) { uint32_t u = UN[o][i]; if (!getb(VIS[o], u)) UN[o][k++] = u; }
            nun[o] = k;
        } else {                                            /* bottom-up */
            uint32_t k = 0;
            /* two rounds: neighbours 0-2 for a batch of unvisited vertices (prefetched), then 3-9 for those not found */
            for (long i0 = 0; i0 < nun[o]; i0 += BATCH) {
                int nb = (int)((nun[o] - i0 < BATCH) ? (nun[o] - i0) : BATCH);
                uint32_t uu[BATCH]; int xs[BATCH][4]; int found[BATCH] = { 0 };
                for (int b = 0; b < nb; b++) {
                    uu[b] = UN[o][i0 + b];
                    xs[b][0] = REP[uu[b]][0]; xs[b][1] = REP[uu[b]][1]; xs[b][2] = REP[uu[b]][2]; xs[b][3] = REP[uu[b]][3];
                    for (int j = 0; j < 3; j++) kb[b * HO + j] = nbkey(xs[b], o, j);
                }
                for (int t = 0; t < nb * 3; t++) __builtin_prefetch(&T[kb[(t / 3) * HO + t % 3]]);
                for (int b = 0; b < nb; b++) for (int j = 0; j < 3 && !found[b]; j++) if (getb(CURB, T[kb[b * HO + j]])) found[b] = 1;
                for (int b = 0; b < nb; b++) if (!found[b]) for (int j = 3; j < HO; j++) kb[b * HO + j] = nbkey(xs[b], o, j);
                for (int b = 0; b < nb; b++) if (!found[b]) for (int j = 3; j < HO; j++) __builtin_prefetch(&T[kb[b * HO + j]]);
                for (int b = 0; b < nb; b++) if (!found[b]) for (int j = 3; j < HO && !found[b]; j++) if (getb(CURB, T[kb[b * HO + j]])) found[b] = 1;
                for (int b = 0; b < nb; b++) {
                    if (found[b]) { setb(VIS[o], uu[b]); NX[nn++] = uu[b]; } else UN[o][k++] = uu[b];
                }
            }
            nun[o] = k;
        }
        for (uint32_t i = 0; i < nf; i++) clrb(CURB, FR[i]);
        for (uint32_t i = 0; i < nn; i++) setb(CURB, NX[i]);
        uint32_t *t = FR; FR = NX; NX = t; nf = nn; sL = o;
    }
}
/* costs of the double coset of z (current lists): uBA, uAA from the A root, uBB from the B root */
static void costs(const int *z, long *uBA, long *uAA, long *uBB) {
    set_lists_mat(z);
    bfs8(0); *uBA = nun[1]; *uAA = nun[0];
    if (uBB) { bfs8(1); *uBB = nun[1]; }
}

static uint64_t rst = 88172645463325252ULL;
static inline uint64_t rnd64(void) { rst ^= rst << 13; rst ^= rst >> 7; rst ^= rst << 17; return rst; }

static int load_done(const char *fn, uint8_t *done) {
    FILE *f = fopen(fn, "r"); int n = 0;
    if (!f) return 0;
    char line[512];
    while (fgets(line, sizeof line, f)) {
        unsigned id; char tag;
        if (sscanf(line, "%c %u", &tag, &id) == 2 && id < NDC && (tag == 'A' || tag == 'B')) {
            if (tag == 'A') { if (!done[id]) n++; done[id] |= 1; }
        }
    }
    fclose(f);
    return n;
}

int main(int argc, char **argv) {
    if (argc < 12) { fprintf(stderr, "usage: exh q psl r00 r01 r10 r11 s00 s01 s10 s11 MODE [args]\n"); return 2; }
    int q = atoi(argv[1]); PSL = atoi(argv[2]);
    for (int i = 0; i < 4; i++) { GEN[0][i] = atoi(argv[3 + i]); GEN[1][i] = atoi(argv[7 + i]); }
    const char *mode = argv[11];
    setup_field(q);
    M2 = PSL ? 1 : 2; H2 = (q - 1) / 2;
    BASE2 = (uint64_t)H2 * q * q * M2; NKEY = BASE2 + (uint64_t)H2 * q * M2;
    GORD = PSL ? (uint64_t)q * (q * q - 1) / 2 : (uint64_t)q * (q * q - 1);
    double t0 = now();
    make_H();
    label_group();
    enum_dc();
    build_inv();
    build_normalizer();
    build_classes();
    fprintf(stderr, "setup %.1f s: %s(2,%d) |G|=%llu N=%u regular DC=%u normaliser(PGL)=%d classes=%u (sum of orbits %u)\n",
            now() - t0, PSL ? "PSL" : "PGL", q, (unsigned long long)GORD, NN, NDC, NAMB, NCLS, NDC);
    {
        uint32_t nsym = 0; for (uint32_t id = 0; id < NDC; id++) if (INVDC[id] == (int32_t)id) nsym++;
        fprintf(stderr, "self-inverse double cosets %u\n", nsym);
    }
    size_t nw = ((size_t)NN + 63) / 64;
    VIS[0] = calloc(nw, 8); VIS[1] = calloc(nw, 8); CURB = calloc(nw, 8);
    UN[0] = malloc(4 * (size_t)NN); UN[1] = malloc(4 * (size_t)NN); FR = malloc(4 * (size_t)NN); NX = malloc(4 * (size_t)NN);

    if (!strcmp(mode, "info")) {
        uint32_t hist[64] = { 0 }; uint32_t maxo = 0;
        for (uint32_t c = 0; c < NCLS; c++) { if (ORB[c] < 64) hist[ORB[c]]++; if (ORB[c] > maxo) maxo = ORB[c]; }
        printf("info q=%d psl=%d N=%u NDC=%u NAMB=%d classes=%u maxorbit=%u\n", q, PSL, NN, NDC, NAMB, NCLS, maxo);
        for (int o = 1; o < 64; o++) if (hist[o]) printf("  orbit size %d: %u classes\n", o, hist[o]);
        return 0;
    }
    if (!strcmp(mode, "member")) {
        int z[4]; for (int i = 0; i < 4; i++) z[i] = atoi(argv[12 + i]);
        int zn[4] = { z[0], z[1], z[2], z[3] }; int bit = norm_mat(zn); (void)bit;
        uint32_t lz = labof(zn); int32_t id = DCOF[lz];
        long uBA, uAA, uBB;
        costs(zn, &uBA, &uAA, &uBB);
        long C = uBA + uAA + uBB;
        printf("member z %d %d %d %d regular %d dc %d uBA %ld uAA %ld uBB %ld C %ld\n", zn[0], zn[1], zn[2], zn[3],
               id >= 0, id, uBA, uAA, uBB, C);
        return 0;
    }
    if (!strcmp(mode, "bench")) {
        int n = atoi(argv[12]); double tb = now(); long sum = 0;
        for (int t = 0; t < n; t++) {
            uint32_t id = (uint32_t)(rnd64() % NDC); long a, b;
            set_lists_mat((const int[4]){ DCREP[id][0], DCREP[id][1], DCREP[id][2], DCREP[id][3] });
            bfs8(0); a = nun[1]; b = nun[0]; sum += a + b;
        }
        printf("bench %d A-root BFS: %.1f ms each (mean P %.1f)\n", n, (now() - tb) * 1e3 / n, (double)sum / n);
        return 0;
    }
    if (!strcmp(mode, "symtest")) {
        int n = atoi(argv[12]); int bad = 0, nsymchk = 0, nsymbad = 0;
        for (int t = 0; t < n; t++) {
            uint32_t id = (uint32_t)(rnd64() % NDC);
            if (argc > 13 && !strcmp(argv[13], "sym")) while (INVDC[id] != (int32_t)id) id = (uint32_t)(rnd64() % NDC);
            long uBA, uAA, uBB, iBA, iAA, iBB, cBA, cAA, cBB;
            int z[4] = { DCREP[id][0], DCREP[id][1], DCREP[id][2], DCREP[id][3] };
            costs(z, &uBA, &uAA, &uBB);                       /* C(D) */
            long C = uBA + uAA + uBB;
            int zi[4]; adjm(z, zi);
            costs(zi, &iBA, &iAA, &iBB);                      /* C(D^-1) */
            long Cinv = iBA + iAA + iBB;
            int k = NAMB ? (int)(rnd64() % NAMB) : -1;
            long Cn = -1;
            if (k >= 0) {
                int na[4], tt[4], pp[4]; adjm(AMB[k], na); mulm(AMB[k], z, tt); mulm(tt, na, pp);
                costs(pp, &cBA, &cAA, &cBB); Cn = cBA + cAA + cBB;   /* C(n D n^-1) */
            }
            int sym = (INVDC[id] == (int32_t)id);
            if (sym) { nsymchk++; if (uBB != uAA) nsymbad++; }
            if (Cinv != C || (k >= 0 && Cn != C)) bad++;
            printf("symtest id %u C %ld Cinv %ld Cconj(k=%d) %ld sym %d uBB %ld uAA %ld\n", id, C, Cinv, k, Cn, sym, uBB, uAA);
            fflush(stdout);
        }
        printf("symtest: %d members, C mismatches %d, self-inverse checks %d with uBB!=uAA: %d\n", n, bad, nsymchk, nsymbad);
        return 0;
    }
    if (!strcmp(mode, "scanA") || !strcmp(mode, "scanB")) {
        /* scanA OUT         ; scanB OUT THR AFILE  (OUT gets B lines; AFILE is the scanA output) */
        const char *out = argv[12];
        uint8_t *done = calloc(NDC, 1);
        int resumed = 0;
        if (!strcmp(mode, "scanA")) {
            resumed = load_done(out, done);
        } else {
            FILE *f = fopen(out, "r");
            if (f) { char line[512]; while (fgets(line, sizeof line, f)) { unsigned id; char tag; if (sscanf(line, "%c %u", &tag, &id) == 2 && tag == 'B' && id < NDC) { done[id] |= 2; resumed++; } } fclose(f); }
        }
        FILE *fo = fopen(out, "a");
        if (!fo) fatal("cannot open output");
        if (!strcmp(mode, "scanA")) {
            double ts = now(); uint32_t cnt = 0;
            for (uint32_t c = 0; c < NCLS; c++) {
                uint32_t id = CLS[c];
                if (done[id] & 1) continue;
                int z[4] = { DCREP[id][0], DCREP[id][1], DCREP[id][2], DCREP[id][3] };
                long uBA, uAA; costs(z, &uBA, &uAA, NULL);
                fprintf(fo, "A %u %u %d %ld %ld %d %d %d %d\n", id, ORB[c], INVDC[id] == (int32_t)id, uBA, uAA, z[0], z[1], z[2], z[3]);
                fflush(fo); cnt++;
                if (cnt % 500 == 0) fprintf(stderr, "scanA: %u new classes, %.0f s, class index %u of %u\n", cnt, now() - ts, c, NCLS);
            }
            fprintf(stderr, "scanA done: %u new classes (%d lines were already there)\n", cnt, resumed);
        } else {
            if (argc < 15) fatal("scanB needs THR and AFILE");
            long thr = atol(argv[13]);
            FILE *fa = fopen(argv[14], "r");
            if (!fa) fatal("cannot open the scanA file");
            char line[512]; double ts = now(); uint32_t cnt = 0;
            while (fgets(line, sizeof line, fa)) {
                unsigned id, orb, sym; long uBA, uAA; char tag;
                if (sscanf(line, "%c %u %u %u %ld %ld", &tag, &id, &orb, &sym, &uBA, &uAA) != 6 || tag != 'A') continue;
                if (uBA + uAA > thr) continue;
                if (done[id] & 2) continue;
                long uBB;
                if (sym) uBB = uAA;                       /* D = D^-1: side swap, uBB = uAA */
                else { int z[4] = { DCREP[id][0], DCREP[id][1], DCREP[id][2], DCREP[id][3] }; long a; costs(z, &a, &a, &uBB); }
                fprintf(fo, "B %u %ld %d\n", id, uBB, (int)sym);
                fflush(fo); cnt++;
                if (cnt % 200 == 0) fprintf(stderr, "scanB: %u classes, %.0f s\n", cnt, now() - ts);
            }
            fclose(fa);
            fprintf(stderr, "scanB done: %u classes\n", cnt);
        }
        fclose(fo);
        return 0;
    }
    fatal("unknown mode");
    return 2;
}
