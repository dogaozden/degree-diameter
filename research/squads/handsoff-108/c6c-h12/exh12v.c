/* exh12.c (c6c-h12, handsoff-108): generalisation of c6b-exhaust/exh.c.
 * G = PSL(2,q) or PGL(2,q) (q prime), H = <g0, g1> of order HSZ (<= 16), any order.
 * A graph X(G,H,D): D = union of double cosets H z_i H with sum of c_i = DEG, c_i = |H z_i H| / |H|
 * (number of left cosets; c_i = HSZ / |H cap z_i H z_i^-1|). Vertices: left cosets Hx on sides A and B;
 * Hx ~ Hy iff x y^-1 in D. Simple bipartite graph of degree DEG (the c_i are disjoint, so degrees add up).
 * Cost (plain vertices, 0 = diameter 8): C = uBA + uAA + uBB as in c6b/exh.c.
 * Left-coset labels: T[key] (key = normalised matrix, det class bit for PGL), N = |G|/HSZ.
 * Double cosets: all of them (regular and not), id = DC id, DCC = c, DCREP = representative.
 * Symmetry: D -> D^-1 (sides swap) and D -> n D n^-1 for n in N_PGL(H); together they act on DC ids
 * as a small permutation group GP (closure); a member is canonical if its sorted id tuple is the
 * lexicographically smallest image. Class weight = number of distinct images.
 *
 * usage: exh12 q psl g00 g01 g10 g11 s00 s01 s10 s11 DEG MODE [args]
 *   info                       group, DC counts by c, normaliser, group GP, partitions of DEG with member counts
 *   dcinfo ID..                c and representative of double cosets
 *   cost ID..                  costs of the union of the given double cosets (sym flag)
 *   zcost z00 z01 z10 z11      cost of the single double coset of the matrix z (validation)
 *   check ID..                 symmetric-adjacency and simplicity check of the union (slow, ~1 min)
 *   sample SPEC K SEED         K random members of SPEC (e.g. "6,2,2"): one line per member
 *   scanA SPEC OUT            all canonical members of SPEC ("all" = every partition of DEG), resumable
 *   scanB OUT THR AFILE       uBB for classes of AFILE with uBA+uAA <= THR (resumable)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <sys/mman.h>

#define MAXQ 256
#define MAXH 16
#define MAXD 16
#define MAXN 512
#define MAXG 128
#define BATCH 3

static int Q, H2, PSL, M2, NSQ, HSZ, DEG;
static uint64_t BASE2, NKEY, GORD;
static uint32_t NN;
static uint8_t MUL[MAXQ][MAXQ];
static int INVV[MAXQ], LAM[MAXQ], BITD[MAXQ];
static uint32_t *T;
static uint8_t (*REP)[4];
static int HL[MAXH][4];
static int GEN[2][4];
static int32_t *DCOF;
static uint8_t (*DCREP)[4];
static uint8_t *DCC;
static uint32_t NDC;
static int32_t *INVDC;
static int NAMB;
static int AMB[MAXN][4];
static int32_t *CONJ[MAXN];
static int NG;
static int32_t *GP;
static uint32_t IDL;
static uint32_t *LIST[MAXH + 1];
static uint32_t NLIST[MAXH + 1];
static int DLS[MAXD][4], ELS[MAXD][4];
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
static inline int norm_mat(int *r) {
    int det = subq(MUL[r[0]][r[3]], MUL[r[1]][r[2]]);
    int lam = LAM[det];
    int v0 = MUL[lam][r[0]], v1 = MUL[lam][r[1]], v2 = MUL[lam][r[2]], v3 = MUL[lam][r[3]];
    int bit = BITD[det];
    int neg = v0 ? (v0 > H2) : (v1 > H2);
    int n0 = v0 ? Q - v0 : 0, n1 = v1 ? Q - v1 : 0, n2 = v2 ? Q - v2 : 0, n3 = v3 ? Q - v3 : 0;
    r[0] = neg ? n0 : v0; r[1] = neg ? n1 : v1; r[2] = neg ? n2 : v2; r[3] = neg ? n3 : v3;
    return bit;
}
static inline uint64_t keyof(const int *r, int bit) {
    uint64_t b = (M2 == 2) ? (uint64_t)bit : 0;
    if (r[0]) return ((((uint64_t)(r[0] - 1) * Q + r[1]) * Q + r[2]) * M2) + b;
    return BASE2 + (((uint64_t)(r[1] - 1) * Q + r[3]) * M2) + b;
}
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
static inline void adjm(const int *x, int *r) { r[0] = x[3]; r[1] = x[1] ? Q - x[1] : 0; r[2] = x[2] ? Q - x[2] : 0; r[3] = x[0]; }
static inline uint32_t labof(const int *m) {
    int r[4] = { m[0], m[1], m[2], m[3] };
    int bit = norm_mat(r);
    if (M2 == 1 && bit) fatal("labof: non-square det in PSL table");
    return T[keyof(r, bit)];
}
static inline uint64_t keyprod(const int *p) { int r[4] = { p[0], p[1], p[2], p[3] }; int bit = norm_mat(r); return keyof(r, bit); }

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
        if (!found) { if (n >= MAXH) fatal("H too big"); memcpy(HL[n], p, sizeof p); n++; }
    }
    HSZ = n;
    if (GORD % HSZ) fatal("|H| does not divide |G|");
}

static void label_group(void) {
    size_t tb = ((size_t)NKEY * 4 + (1u << 21) - 1) & ~(size_t)((1u << 21) - 1);
    T = aligned_alloc(1u << 21, tb);
    if (!T) fatal("alloc T");
    madvise(T, tb, MADV_HUGEPAGE);
    memset(T, 0xff, NKEY * 4);
    NN = (uint32_t)(GORD / HSZ);
    REP = malloc((size_t)NN * 4 + 64);
    uint32_t nl = 0;
    for (uint64_t k = 0; k < NKEY; k++) {
        if (T[k] != 0xffffffffu) continue;
        int e[4]; decode(k, M2, e);
        { int t[4] = { e[0], e[1], e[2], e[3] }; int bit = norm_mat(t);
          if (memcmp(t, e, sizeof e) || keyof(e, bit) != k) fatal("decode/keyof mismatch"); }
        for (int j = 0; j < HSZ; j++) {
            int p[4]; mulm(HL[j], e, p);
            int bit = norm_mat(p); uint64_t kk = keyof(p, bit);
            if (T[kk] != 0xffffffffu) fatal("coset labelling collision");
            T[kk] = nl;
        }
        for (int i = 0; i < 4; i++) REP[nl][i] = (uint8_t)e[i];
        nl++;
    }
    if (nl != NN) fatal("coset count != |G|/|H|");
    IDL = labof((int[4]){ 1, 0, 0, 1 });
}

/* all double cosets: orbits of H acting on the right on H\G; c = number of distinct left cosets */
static void enum_dc(void) {
    DCOF = malloc(sizeof(int32_t) * NN);
    for (uint32_t l = 0; l < NN; l++) DCOF[l] = -1;
    DCREP = malloc(sizeof(*DCREP) * (NN + 16));
    DCC = malloc(NN + 16);
    NDC = 0;
    for (uint32_t l = 0; l < NN; l++) {
        if (DCOF[l] >= 0) continue;
        int x[4] = { REP[l][0], REP[l][1], REP[l][2], REP[l][3] };
        uint32_t labs[MAXH]; int c = 0;
        for (int j = 0; j < HSZ; j++) {
            int p[4]; mulm(x, HL[j], p); uint32_t L = labof(p);
            int dup = 0; for (int k = 0; k < c; k++) if (labs[k] == L) { dup = 1; break; }
            if (!dup) labs[c++] = L;
        }
        uint32_t id = NDC++;
        for (int k = 0; k < c; k++) { if (DCOF[labs[k]] >= 0) fatal("double coset overlap"); DCOF[labs[k]] = (int32_t)id; }
        for (int i = 0; i < 4; i++) DCREP[id][i] = (uint8_t)x[i];
        DCC[id] = (uint8_t)c;
    }
    for (int c = 0; c <= HSZ; c++) NLIST[c] = 0;
    for (uint32_t id = 0; id < NDC; id++) NLIST[DCC[id]]++;
    for (int c = 0; c <= HSZ; c++) { LIST[c] = malloc(4 * (NLIST[c] + 1)); NLIST[c] = 0; }
    for (uint32_t id = 0; id < NDC; id++) { int c = DCC[id]; LIST[c][NLIST[c]++] = id; }
}

static void build_inv(void) {
    INVDC = malloc(sizeof(int32_t) * NDC);
    for (uint32_t id = 0; id < NDC; id++) {
        int z[4] = { DCREP[id][0], DCREP[id][1], DCREP[id][2], DCREP[id][3] }, zi[4];
        adjm(z, zi);
        int32_t v = DCOF[labof(zi)];
        if (v < 0) fatal("inverse not a double coset");
        INVDC[id] = v;
    }
}

static void build_normalizer(void) {
    uint64_t nkp = 2ULL * H2 * Q * (Q + 1);
    NAMB = 0;
    for (uint64_t k = 0; k < nkp; k++) {
        int n[4], na[4], t[4], p[4];
        decode(k, 2, n); adjm(n, na);
        mulm(n, GEN[0], t); mulm(t, na, p);
        if (labof(p) != IDL) continue;
        mulm(n, GEN[1], t); mulm(t, na, p);
        if (labof(p) != IDL) continue;
        if (NAMB >= MAXN) fatal("normaliser too big");
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
            if (v < 0) fatal("conjugate not a double coset");
            CONJ[k][id] = v;
        }
    }
}

/* group of permutations of DC ids generated by inversion and conjugation by the normaliser */
static void build_group(void) {
    GP = malloc((size_t)MAXG * NDC * 4);
    int32_t *tmp = malloc(4 * (size_t)NDC);
    NG = 1; for (uint32_t i = 0; i < NDC; i++) GP[i] = (int32_t)i;
    for (int g = 0; g < NG; g++) {
        for (int gi = -1; gi < NAMB; gi++) {
            const int32_t *gen = gi < 0 ? INVDC : CONJ[gi];
            for (uint32_t i = 0; i < NDC; i++) tmp[i] = gen[GP[(size_t)g * NDC + i]];
            int dup = 0;
            for (int k = 0; k < NG && !dup; k++) if (!memcmp(GP + (size_t)k * NDC, tmp, 4 * (size_t)NDC)) dup = 1;
            if (!dup) { if (NG >= MAXG) fatal("group too big"); memcpy(GP + (size_t)NG * NDC, tmp, 4 * (size_t)NDC); NG++; }
        }
    }
    free(tmp);
}

/* ---------- BFS (as c6b exh.c, neighbour lists of length DEG) ---------- */
static inline int getb(const uint64_t *B, uint32_t i) { return (int)((B[i >> 6] >> (i & 63)) & 1); }
static inline void setb(uint64_t *B, uint32_t i) { B[i >> 6] |= 1ULL << (i & 63); }
static inline void clrb(uint64_t *B, uint32_t i) { B[i >> 6] &= ~(1ULL << (i & 63)); }

static inline void nbkeys(const int *x, int side, uint64_t *kout) {
    for (int j = 0; j < DEG; j++) {
        const int *g = side == 0 ? ELS[j] : DLS[j];
        int p[4];
        p[0] = addq(MUL[g[0]][x[0]], MUL[g[1]][x[2]]);
        p[1] = addq(MUL[g[0]][x[1]], MUL[g[1]][x[3]]);
        p[2] = addq(MUL[g[2]][x[0]], MUL[g[3]][x[2]]);
        p[3] = addq(MUL[g[2]][x[1]], MUL[g[3]][x[3]]);
        kout[j] = keyprod(p);
    }
}
static inline uint64_t nbkey(const int *x, int side, int j) {
    const int *g = side == 0 ? ELS[j] : DLS[j];
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
    uint64_t kb[BATCH * MAXD];
    for (int L = 0; L < 8 && nf; L++) {
        int o = 1 - sL;
        uint32_t nn = 0;
        if ((long)nf * 3 < nun[o] * 2) {
            for (uint32_t i0 = 0; i0 < nf; i0 += BATCH) {
                int nb = (int)((nf - i0 < BATCH) ? (nf - i0) : BATCH);
                for (int b = 0; b < nb; b++) {
                    int x[4] = { REP[FR[i0 + b]][0], REP[FR[i0 + b]][1], REP[FR[i0 + b]][2], REP[FR[i0 + b]][3] };
                    nbkeys(x, sL, kb + b * DEG);
                }
                for (int t = 0; t < nb * DEG; t++) __builtin_prefetch(&T[kb[t]]);
                for (int t = 0; t < nb * DEG; t++) { uint32_t w = T[kb[t]]; if (!getb(VIS[o], w)) { setb(VIS[o], w); NX[nn++] = w; } }
            }
            uint32_t k = 0;
            for (long i = 0; i < nun[o]; i++) { uint32_t u = UN[o][i]; if (!getb(VIS[o], u)) UN[o][k++] = u; }
            nun[o] = k;
        } else {
            uint32_t k = 0;
            for (long i0 = 0; i0 < nun[o]; i0 += BATCH) {
                int nb = (int)((nun[o] - i0 < BATCH) ? (nun[o] - i0) : BATCH);
                uint32_t uu[BATCH]; int xs[BATCH][4]; int found[BATCH] = { 0 };
                for (int b = 0; b < nb; b++) {
                    uu[b] = UN[o][i0 + b];
                    xs[b][0] = REP[uu[b]][0]; xs[b][1] = REP[uu[b]][1]; xs[b][2] = REP[uu[b]][2]; xs[b][3] = REP[uu[b]][3];
                    for (int j = 0; j < 3; j++) kb[b * DEG + j] = nbkey(xs[b], o, j);
                }
                for (int t = 0; t < nb * 3; t++) __builtin_prefetch(&T[kb[(t / 3) * DEG + t % 3]]);
                for (int b = 0; b < nb; b++) for (int j = 0; j < 3 && !found[b]; j++) if (getb(CURB, T[kb[b * DEG + j]])) found[b] = 1;
                for (int b = 0; b < nb; b++) if (!found[b]) for (int j = 3; j < DEG; j++) kb[b * DEG + j] = nbkey(xs[b], o, j);
                for (int b = 0; b < nb; b++) if (!found[b]) for (int j = 3; j < DEG; j++) __builtin_prefetch(&T[kb[b * DEG + j]]);
                for (int b = 0; b < nb; b++) if (!found[b]) for (int j = 3; j < DEG && !found[b]; j++) if (getb(CURB, T[kb[b * DEG + j]])) found[b] = 1;
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

/* neighbour lists of the union of the double cosets ids[0..n-1]: DLS = left cosets of D (side B neighbours of an
 * A vertex x are D^-1 x; side A neighbours of a B vertex y are D y), ELS = left cosets of D^-1 */
static void set_lists(const uint32_t *ids, int n) {
    int nd = 0, ne = 0;
    for (int t = 0; t < n; t++) {
        uint32_t id = ids[t];
        int z[4], zi[4];
        for (int i = 0; i < 4; i++) z[i] = DCREP[id][i];
        adjm(z, zi);
        uint32_t sD[MAXH], sE[MAXH]; int cd = 0, ce = 0;
        for (int j = 0; j < HSZ; j++) {
            int p[4];
            mulm(z, HL[j], p);
            uint32_t L = labof(p);
            int dup = 0; for (int k = 0; k < cd; k++) if (sD[k] == L) { dup = 1; break; }
            if (!dup) { sD[cd++] = L; if (nd >= DEG) fatal("too many neighbours"); memcpy(DLS[nd++], p, sizeof p); }
            mulm(zi, HL[j], p);
            L = labof(p);
            dup = 0; for (int k = 0; k < ce; k++) if (sE[k] == L) { dup = 1; break; }
            if (!dup) { sE[ce++] = L; if (ne >= DEG) fatal("too many neighbours"); memcpy(ELS[ne++], p, sizeof p); }
        }
        if (cd != DCC[id] || ce != DCC[id]) fatal("c mismatch");
    }
    if (nd != DEG || ne != DEG) { fprintf(stderr, "degree %d (want %d)\n", nd, DEG); fatal("degree mismatch"); }
}
static void costs_ids(const uint32_t *ids, int n, long *uBA, long *uAA, long *uBB) {
    set_lists(ids, n);
    bfs8(0); *uBA = nun[1]; *uAA = nun[0];
    if (uBB) { bfs8(1); *uBB = nun[1]; }
}

/* ---------- member utilities ---------- */
static void isort(uint32_t *a, int n) { for (int i = 1; i < n; i++) { uint32_t v = a[i]; int j = i - 1; while (j >= 0 && a[j] > v) { a[j + 1] = a[j]; j--; } a[j + 1] = v; } }
static int lexcmp(const uint32_t *a, const uint32_t *b, int n) { for (int i = 0; i < n; i++) { if (a[i] != b[i]) return a[i] < b[i] ? -1 : 1; } return 0; }
static uint64_t hkey(const uint32_t *s, int n) {
    uint64_t h = 1469598103934665603ULL;
    for (int i = 0; i < n; i++) for (int b = 0; b < 4; b++) { h ^= (s[i] >> (8 * b)) & 255; h *= 1099511628211ULL; }
    return h;
}
static char KEYBUF[256];
static const char *keystr(const uint32_t *s, int n) {
    int p = 0;
    for (int i = 0; i < n; i++) p += snprintf(KEYBUF + p, sizeof KEYBUF - p, i ? ".%u" : "%u", s[i]);
    return KEYBUF;
}
static int parse_key(const char *str, uint32_t *s) {
    int n = 0; const char *p = str;
    while (*p) { char *e; unsigned long v = strtoul(p, &e, 10); if (e == p || n >= MAXD) return -1; s[n++] = (uint32_t)v; if (*e == '.') p = e + 1; else if (*e == 0 || *e == ' ' || *e == '\n') break; else return -1; }
    isort(s, n);
    return n;
}
/* canonical form: smallest image under GP; orbit = number of distinct images; sym = (D^-1 == D) */
static void canon_info(const uint32_t *s, int n, int *is_canon, int *orb, int *sym) {
    static uint32_t im[MAXG][MAXD];
    int ni = 0;
    for (int g = 0; g < NG; g++) {
        uint32_t t[MAXD];
        for (int i = 0; i < n; i++) t[i] = (uint32_t)GP[(size_t)g * NDC + s[i]];
        isort(t, n);
        int dup = 0;
        for (int k = 0; k < ni && !dup; k++) if (!memcmp(im[k], t, 4 * n)) dup = 1;
        if (!dup) memcpy(im[ni++], t, 4 * n);
    }
    int mi = 0;
    for (int k = 1; k < ni; k++) if (lexcmp(im[k], im[mi], n) < 0) mi = k;
    *is_canon = lexcmp(im[mi], s, n) == 0;
    *orb = ni;
    uint32_t t[MAXD];
    for (int i = 0; i < n; i++) t[i] = (uint32_t)INVDC[s[i]];
    isort(t, n);
    *sym = lexcmp(t, s, n) == 0;
}

/* ---------- enumeration of the members of a partition (groups of equal c) ---------- */
typedef void (*vfn)(const uint32_t *ids, int n);
static vfn VISIT;
static char PARTSTR[256];
static int NGR, GV[MAXD], GM[MAXD];
static uint32_t MEM[MAXD]; static int NMEM;
static long NMEMB = 0;
static void enum_groups(int g) {
    if (g == NGR) { VISIT(MEM, NMEM); NMEMB++; return; }
    int v = GV[g], m = GM[g]; uint32_t n = NLIST[v];
    if ((uint32_t)m > n) return;
    uint32_t idx[MAXD];
    for (int i = 0; i < m; i++) idx[i] = (uint32_t)i;
    while (1) {
        int save = NMEM;
        for (int i = 0; i < m; i++) MEM[NMEM + i] = LIST[v][idx[i]];
        NMEM += m;
        enum_groups(g + 1);
        NMEM = save;
        int i = m - 1;
        while (i >= 0 && idx[i] == n - m + (uint32_t)i) i--;
        if (i < 0) break;
        idx[i]++;
        for (int j = i + 1; j < m; j++) idx[j] = idx[j - 1] + 1;
    }
}
static int AVAIL[MAXD + 1], NAVAIL;
static int PV[MAXD], PM[MAXD], NPV;
static void parts_rec(int vi, int rem) {
    if (rem == 0) {
        NGR = NPV;
        PARTSTR[0] = 0; int p = 0;
        for (int g = 0; g < NPV; g++) { GV[g] = PV[g]; GM[g] = PM[g]; for (int k = 0; k < PM[g]; k++) p += snprintf(PARTSTR + p, sizeof PARTSTR - p, p ? "+%d" : "%d", PV[g]); }
        NMEM = 0;
        enum_groups(0);
        return;
    }
    if (vi == NAVAIL) return;
    int v = AVAIL[vi];
    int maxm = rem / v; if ((uint32_t)maxm > NLIST[v]) maxm = (int)NLIST[v];
    for (int m = maxm; m >= 0; m--) {
        if (m > 0) { PV[NPV] = v; PM[NPV] = m; NPV++; }
        parts_rec(vi + 1, rem - m * v);
        if (m > 0) NPV--;
    }
}
static void run_spec(const char *spec, vfn visit) {
    VISIT = visit;
    if (!strcmp(spec, "all")) {
        NAVAIL = 0;
        for (int v = DEG; v >= 1; v--) if (NLIST[v] > 0) AVAIL[NAVAIL++] = v;
        NPV = 0; parts_rec(0, DEG);
        return;
    }
    NGR = 0; int tot = 0; const char *p = spec;
    int vals[MAXD], nv = 0;
    while (*p) { char *e; long v = strtol(p, &e, 10); if (e == p) fatal("bad spec"); vals[nv++] = (int)v; tot += (int)v; p = e; if (*p == ',' || *p == '+') p++; if (nv >= MAXD) fatal("spec too long"); }
    if (tot != DEG) fatal("spec does not sum to DEG");
    for (int i = 0; i < nv; i++) {
        int found = -1; for (int g = 0; g < NGR; g++) if (GV[g] == vals[i]) found = g;
        if (found >= 0) GM[found]++;
        else { GV[NGR] = vals[i]; GM[NGR] = 1; NGR++; }
    }
    for (int g = 0; g < NGR; g++) if (NLIST[GV[g]] < (uint32_t)GM[g]) { fprintf(stderr, "no DCs of c=%d\n", GV[g]); exit(3); }
    { int p2 = 0; PARTSTR[0] = 0; for (int i = 0; i < nv; i++) p2 += snprintf(PARTSTR + p2, sizeof PARTSTR - p2, i ? "+%d" : "%d", vals[i]); }
    NMEM = 0;
    enum_groups(0);
}

/* ---------- resumable outputs ---------- */
static uint64_t *DONE_A; static size_t NDONE_A;
static uint64_t *DONE_B; static size_t NDONE_B;
static int cmpu64(const void *a, const void *b) { uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b; return x < y ? -1 : x > y; }
static int has_u64(const uint64_t *arr, size_t n, uint64_t h) { size_t lo = 0, hi = n; while (lo < hi) { size_t mid = (lo + hi) / 2; if (arr[mid] < h) lo = mid + 1; else hi = mid; } return lo < n && arr[lo] == h; }
static void load_done(const char *fn, char tag, uint64_t **arr, size_t *cnt) {
    FILE *f = fopen(fn, "r");
    *arr = NULL; *cnt = 0;
    if (!f) return;
    size_t cap = 1024; *arr = malloc(cap * 8);
    char line[1024];
    while (fgets(line, sizeof line, f)) {
        if (line[0] != tag || line[1] != ' ') continue;
        char *keyp = line + 2; char *sp = strchr(keyp, ' ');
        if (!sp) continue; *sp = 0;
        uint32_t s[MAXD]; int n = parse_key(keyp, s);
        if (n <= 0) continue;
        if (*cnt == cap) { cap *= 2; *arr = realloc(*arr, cap * 8); }
        (*arr)[(*cnt)++] = hkey(s, n);
    }
    fclose(f);
    qsort(*arr, *cnt, 8, cmpu64);
}

static FILE *FOUT; static long NCLS_NEW = 0; static double TSTART;
static void visit_scanA(const uint32_t *ids, int n) {
    uint32_t s[MAXD]; memcpy(s, ids, 4 * n); isort(s, n);
    int is_canon, orb, sym;
    canon_info(s, n, &is_canon, &orb, &sym);
    if (!is_canon) return;
    if (has_u64(DONE_A, NDONE_A, hkey(s, n))) return;
    long uBA, uAA;
    costs_ids(s, n, &uBA, &uAA, NULL);
    fprintf(FOUT, "A %s %d %d %ld %ld %s\n", keystr(s, n), orb, sym, uBA, uAA, PARTSTR);
    fflush(FOUT);
    NCLS_NEW++;
    if (NCLS_NEW % 200 == 0) fprintf(stderr, "scanA: %ld new classes, %.0f s, members seen %ld\n", NCLS_NEW, now() - TSTART, NMEMB);
}
static long NCOUNT_IN_SPEC = 0;
static void visit_count(const uint32_t *ids, int n) { (void)ids; (void)n; NCOUNT_IN_SPEC++; }

static uint64_t rst = 88172645463325252ULL;
static inline uint64_t rnd64(void) { rst ^= rst << 13; rst ^= rst >> 7; rst ^= rst << 17; return rst; }

int main(int argc, char **argv) {
    if (argc < 13) { fprintf(stderr, "usage: exh12 q psl g00 g01 g10 g11 s00 s01 s10 s11 DEG MODE [args]\n"); return 2; }
    int q = atoi(argv[1]); PSL = atoi(argv[2]);
    for (int i = 0; i < 4; i++) { GEN[0][i] = atoi(argv[3 + i]); GEN[1][i] = atoi(argv[7 + i]); }
    DEG = atoi(argv[11]);
    const char *mode = argv[12];
    if (DEG > MAXD) fatal("DEG too big");
    setup_field(q);
    M2 = PSL ? 1 : 2; H2 = (q - 1) / 2;
    BASE2 = (uint64_t)H2 * q * q * M2; NKEY = BASE2 + (uint64_t)H2 * q * M2;
    GORD = PSL ? (uint64_t)q * (q * q - 1) / 2 : (uint64_t)q * (q * q - 1);
    TSTART = now();
    make_H();
    label_group();
    enum_dc();
    build_inv();
    build_normalizer();
    build_group();
    fprintf(stderr, "setup %.1f s: %s(2,%d) |G|=%llu |H|=%d N=%u DC total=%u normaliser(PGL)=%d group on DCs=%d\n",
            now() - TSTART, PSL ? "PSL" : "PGL", q, (unsigned long long)GORD, HSZ, NN, NDC, NAMB, NG);
    size_t nw = ((size_t)NN + 63) / 64;
    VIS[0] = calloc(nw, 8); VIS[1] = calloc(nw, 8); CURB = calloc(nw, 8);
    UN[0] = malloc(4 * (size_t)NN); UN[1] = malloc(4 * (size_t)NN); FR = malloc(4 * (size_t)NN); NX = malloc(4 * (size_t)NN);

    if (!strcmp(mode, "info")) {
        printf("info q=%d psl=%d |H|=%d N=%u DEG=%d DCtotal=%u normaliser=%d groupDC=%d\n", q, PSL, HSZ, NN, DEG, NDC, NAMB, NG);
        for (int c = 1; c <= HSZ; c++) if (NLIST[c]) printf("  c=%d (k=%d): %u double cosets\n", c, HSZ / c, NLIST[c]);
        /* members of each partition of DEG */
        NAVAIL = 0; for (int v = DEG; v >= 1; v--) if (NLIST[v] > 0) AVAIL[NAVAIL++] = v;
        printf("  partitions of DEG=%d (members, by product of binomials):\n", DEG);
        /* simple DP over partitions via recursion with counting */
        {
            double total = 0;
            NPV = 0;
            /* recursion printing each partition with its member count */
            void rec(int vi, int rem) {
                if (rem == 0) {
                    double cnt = 1; char buf[256] = ""; int p = 0;
                    for (int g = 0; g < NPV; g++) {
                        double n = NLIST[PV[g]], m = PM[g], c = 1;
                        for (int k = 0; k < PM[g]; k++) c = c * (n - k) / (k + 1);
                        cnt *= c; (void)m;
                        for (int k = 0; k < PM[g]; k++) p += snprintf(buf + p, sizeof buf - p, p ? "+%d" : "%d", PV[g]);
                    }
                    printf("    %-14s members %.0f\n", buf, cnt); total += cnt; return;
                }
                if (vi == NAVAIL) return;
                int v = AVAIL[vi];
                int maxm = rem / v; if ((uint32_t)maxm > NLIST[v]) maxm = (int)NLIST[v];
                for (int m = maxm; m >= 0; m--) {
                    if (m > 0) { PV[NPV] = v; PM[NPV] = m; NPV++; }
                    rec(vi + 1, rem - m * v);
                    if (m > 0) NPV--;
                }
            }
            rec(0, DEG);
            printf("  total members (all partitions) %.0f\n", total);
        }
        return 0;
    }
    if (!strcmp(mode, "dcinfo")) {
        for (int a = 13; a < argc; a++) {
            uint32_t id = (uint32_t)atol(argv[a]);
            printf("dc %u c %d rep %d %d %d %d\n", id, DCC[id], DCREP[id][0], DCREP[id][1], DCREP[id][2], DCREP[id][3]);
        }
        return 0;
    }
    if (!strcmp(mode, "cost")) {
        uint32_t ids[MAXD]; int n = 0;
        for (int a = 13; a < argc; a++) ids[n++] = (uint32_t)atol(argv[a]);
        long uBA, uAA, uBB; costs_ids(ids, n, &uBA, &uAA, &uBB);
        int is_canon, orb, sym; uint32_t s[MAXD]; memcpy(s, ids, 4 * n); isort(s, n); canon_info(s, n, &is_canon, &orb, &sym);
        printf("cost ids %s uBA %ld uAA %ld uBB %ld C %ld sym %d\n", keystr(s, n), uBA, uAA, uBB, uBA + uAA + uBB, sym);
        return 0;
    }
    if (!strcmp(mode, "dcof")) {
        int z[4]; for (int i = 0; i < 4; i++) z[i] = atoi(argv[13 + i]);
        int bit = norm_mat(z); (void)bit;
        int32_t id = DCOF[labof(z)];
        printf("dcof %d %d %d %d id %d c %d\n", z[0], z[1], z[2], z[3], id, DCC[id]);
        return 0;
    }
    if (!strcmp(mode, "zcost")) {
        int z[4]; for (int i = 0; i < 4; i++) z[i] = atoi(argv[13 + i]);
        int bit = norm_mat(z); (void)bit;
        int32_t id = DCOF[labof(z)];
        uint32_t ids[1] = { (uint32_t)id };
        long uBA, uAA, uBB; costs_ids(ids, 1, &uBA, &uAA, &uBB);
        printf("zcost z %d %d %d %d dc %d c %d uBA %ld uAA %ld uBB %ld C %ld\n", z[0], z[1], z[2], z[3], id, DCC[id], uBA, uAA, uBB, uBA + uAA + uBB);
        return 0;
    }
    if (!strcmp(mode, "check")) {
        uint32_t ids[MAXD]; int n = 0;
        for (int a = 13; a < argc; a++) ids[n++] = (uint32_t)atol(argv[a]);
        set_lists(ids, n);
        long bad = 0, nondist = 0, nodeg = 0;
        for (uint32_t l = 0; l < NN; l++) {
            int x[4] = { REP[l][0], REP[l][1], REP[l][2], REP[l][3] };
            uint32_t ys[MAXD];
            for (int j = 0; j < DEG; j++) { int p[4]; mulm(ELS[j], x, p); ys[j] = labof(p); }
            for (int j = 0; j < DEG; j++) for (int k = 0; k < j; k++) if (ys[j] == ys[k]) nondist++;
            for (int j = 0; j < DEG; j++) {
                uint32_t y = ys[j]; int cnt = 0;
                int yx[4] = { REP[y][0], REP[y][1], REP[y][2], REP[y][3] };
                for (int k = 0; k < DEG; k++) { int p[4]; mulm(DLS[k], yx, p); if (labof(p) == l) cnt++; }
                if (cnt != 1) bad++;
            }
            (void)nodeg;
        }
        printf("check ids %s: N=%u, asymmetric or repeated edges %ld, repeated neighbours %ld\n", keystr(ids, n), NN, bad, nondist);
        return 0;
    }
    if (!strcmp(mode, "sample")) {
        const char *spec = argv[13]; int K = atoi(argv[14]); uint64_t seed = (uint64_t)atoll(argv[15]);
        rst = seed * 0x9E3779B97F4A7C15ULL + 1;
        /* parse spec into groups */
        int vals[MAXD], nv = 0; const char *p = spec;
        while (*p) { char *e; long v = strtol(p, &e, 10); vals[nv++] = (int)v; p = e; if (*p == ',' || *p == '+') p++; }
        NGR = 0;
        for (int i = 0; i < nv; i++) { int found = -1; for (int g = 0; g < NGR; g++) if (GV[g] == vals[i]) found = g; if (found >= 0) GM[found]++; else { GV[NGR] = vals[i]; GM[NGR] = 1; NGR++; } }
        for (int i = 0; i < K; i++) {
            NMEM = 0;
            for (int g = 0; g < NGR; g++) {
                int m = GM[g]; uint32_t n = NLIST[GV[g]];
                uint32_t chosen[MAXD]; int nc = 0;
                while (nc < m) {
                    uint32_t c = LIST[GV[g]][rnd64() % n]; int dup = 0;
                    for (int k = 0; k < nc; k++) if (chosen[k] == c) dup = 1;
                    if (!dup) chosen[nc++] = c;
                }
                for (int k = 0; k < nc; k++) MEM[NMEM++] = chosen[k];
            }
            uint32_t s[MAXD]; memcpy(s, MEM, 4 * NMEM); isort(s, NMEM);
            long uBA, uAA, uBB; costs_ids(s, NMEM, &uBA, &uAA, &uBB);
            int is_canon, orb, sym; canon_info(s, NMEM, &is_canon, &orb, &sym);
            printf("cand %d spec %s key %s uBA %ld uAA %ld uBB %ld C %ld sym %d\n", i, spec, keystr(s, NMEM), uBA, uAA, uBB, uBA + uAA + uBB, sym);
            fflush(stdout);
        }
        return 0;
    }
    if (!strcmp(mode, "scanA")) {
        const char *spec = argv[13]; const char *out = argv[14];
        load_done(out, 'A', &DONE_A, &NDONE_A);
        fprintf(stderr, "scanA %s: %zu classes already in %s\n", spec, NDONE_A, out);
        FOUT = fopen(out, "a"); if (!FOUT) fatal("cannot open output");
        run_spec(spec, visit_scanA);
        fprintf(stderr, "scanA %s done: %ld new classes, members enumerated %ld, %.0f s\n", spec, NCLS_NEW, NMEMB, now() - TSTART);
        fclose(FOUT);
        return 0;
    }
    if (!strcmp(mode, "scanB")) {
        const char *out = argv[13]; long thr = atol(argv[14]); const char *afile = argv[15];
        load_done(out, 'B', &DONE_B, &NDONE_B);
        FILE *fa = fopen(afile, "r"); if (!fa) fatal("cannot open A file");
        FILE *fo = fopen(out, "a"); if (!fo) fatal("cannot open output");
        char line[1024]; long cnt = 0;
        while (fgets(line, sizeof line, fa)) {
            if (line[0] != 'A' || line[1] != ' ') continue;
            char kbuf[512], spec[256]; int orb, sym; long uBA, uAA;
            if (sscanf(line, "A %511s %d %d %ld %ld %255s", kbuf, &orb, &sym, &uBA, &uAA, spec) < 5) continue;
            if (uBA + uAA > thr) continue;
            uint32_t s[MAXD]; int n = parse_key(kbuf, s);
            if (n <= 0) continue;
            if (has_u64(DONE_B, NDONE_B, hkey(s, n))) continue;
            long uBB;
            if (sym) uBB = uAA;
            else { long a, b; costs_ids(s, n, &a, &b, &uBB); }
            fprintf(fo, "B %s %ld %ld %ld\n", keystr(s, n), uBB, uBA, uAA); fflush(fo);
            cnt++;
        }
        fclose(fa); fclose(fo);
        fprintf(stderr, "scanB: %ld classes with uBA+uAA <= %ld\n", cnt, thr);
        return 0;
    }
    fatal("unknown mode");
    return 2;
}
