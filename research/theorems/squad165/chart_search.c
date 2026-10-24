/* Fast search for route charts over F_4^4: A_0..A_3 in GL_4(F_4) (A_0 = I), b_0..b_3 in F_4^4.
   Universal: all 216 nonbacktracking 4-walk matrices nonsingular (chart.py's conditions:
     A side: {A_i2^-1 b_i1, A_i2^-1 b_i2, A_i3^-1 b_i3, A_i3^-1 b_i4} independent,
     B side: {A_i2 A_i1^-1 b_i1, b_i2, b_i3, A_i3 A_i4^-1 b_i4} independent, for i1!=i2!=i3!=i4).
   Pencil-complete (chart2.py): for every ordered pair i != j the 8 vectors
     A: {A_i A_k^-1 b_k : k!=i} u {b_l : l not in {i,j}} u {A_j A_k^-1 b_k : k!=j}   mod <b_i, b_j>
     B: {A_i^-1 b_k : k!=i}    u {c_l : l not in {i,j}} u {A_j^-1 b_k : k!=j}      mod <c_i, c_j>, c_l = A_l^-1 b_l
   hit all 5 points of PG(1,4).  Cost = universal violations + PW * pencil violations.
   usage: chart_search seconds seed [PW] [out]
   out: four lines with the 16 entries of A_0..A_3 (row-major), then four lines with b_0..b_3.
   Encoding: F_4 = {0,1,w,w^2} -> 0,1,2,3 (a + b w -> a + 2b); vector = 4 coords, 2 bits each (coord r in bits 2r..2r+1). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static const int MUL[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}}, INVF[4] = {0,1,3,2};
static int smul[4][256];                  /* scalar * vector */
typedef struct { int c[4]; } mat;         /* columns as packed vectors */
static inline int coord(int v, int r) { return (v >> (2 * r)) & 3; }
static inline int mv(const mat *M, int v) { int out = 0; for (int j = 0; j < 4; j++) out ^= smul[coord(v, j)][M->c[j]]; return out; }
static int rank4(const int *v, int n) {   /* rank of n packed vectors over F_4 */
    int a[8]; memcpy(a, v, n * sizeof(int)); int r = 0;
    for (int col = 0; col < 4 && r < n; col++) {
        int p = -1; for (int i = r; i < n; i++) if (coord(a[i], col)) { p = i; break; }
        if (p < 0) continue;
        int t = a[p]; a[p] = a[r]; a[r] = t;
        int iv = INVF[coord(a[r], col)]; a[r] = smul[iv][a[r]];
        for (int i = 0; i < n; i++) if (i != r && coord(a[i], col)) a[i] ^= smul[coord(a[i], col)][a[r]];
        r++;
    }
    return r;
}
static int inv_mat(const mat *M, mat *R) {
    int X[4][8];
    for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) { X[r][c] = coord(M->c[c], r); X[r][4 + c] = (r == c); }
    for (int col = 0; col < 4; col++) {
        int p = -1; for (int r = col; r < 4; r++) if (X[r][col]) { p = r; break; }
        if (p < 0) return 0;
        for (int c = 0; c < 8; c++) { int t = X[p][c]; X[p][c] = X[col][c]; X[col][c] = t; }
        int iv = INVF[X[col][col]]; for (int c = 0; c < 8; c++) X[col][c] = MUL[iv][X[col][c]];
        for (int r = 0; r < 4; r++) if (r != col && X[r][col]) { int f = X[r][col]; for (int c = 0; c < 8; c++) X[r][c] ^= MUL[f][X[col][c]]; }
    }
    for (int c = 0; c < 4; c++) { int v = 0; for (int r = 0; r < 4; r++) v |= X[r][4 + c] << (2 * r); R->c[c] = v; }
    return 1;
}
static mat A[4], Ai[4]; static int b[4];
/* projective point (0..4) of z modulo W = <w1,w2> in PG(1,4); -1 if z in W or W not 2-dim */
static int quot_point(int w1, int w2, int z) {
    int basis[4] = {w1, w2, 0, 0}, nb = 2;
    for (int r = 0; r < 4 && nb < 4; r++) { basis[nb] = 1 << (2 * r); if (rank4(basis, nb + 1) == nb + 1) nb++; }
    if (nb < 4) return -1;
    mat B, Bi; for (int j = 0; j < 4; j++) B.c[j] = basis[j];
    if (!inv_mat(&B, &Bi)) return -1;
    int x = mv(&Bi, z); int x3 = coord(x, 2), x4 = coord(x, 3);
    if (!x3 && !x4) return -1;
    if (!x3) return 4;                 /* (0:1) */
    return MUL[INVF[x3]][x4];          /* (1:t), t in F_4 -> 0..3 */
}
static int pencil_ok(int w1, int w2, const int *z, int nz) {
    int wv[2] = {w1, w2}; if (rank4(wv, 2) < 2) return 0;
    int seen = 0; for (int i = 0; i < nz; i++) { int p = quot_point(w1, w2, z[i]); if (p >= 0) seen |= 1 << p; }
    return seen == 31;
}
static int univ(void) {
    int bad = 0, v[4];
    for (int i1 = 0; i1 < 4; i1++) for (int i2 = 0; i2 < 4; i2++) if (i2 != i1) for (int i3 = 0; i3 < 4; i3++) if (i3 != i2)
    for (int i4 = 0; i4 < 4; i4++) if (i4 != i3) {
        v[0] = mv(&Ai[i2], b[i1]); v[1] = mv(&Ai[i2], b[i2]); v[2] = mv(&Ai[i3], b[i3]); v[3] = mv(&Ai[i3], b[i4]);
        if (rank4(v, 4) < 4) bad++;
        v[0] = mv(&A[i2], mv(&Ai[i1], b[i1])); v[1] = b[i2]; v[2] = b[i3]; v[3] = mv(&A[i3], mv(&Ai[i4], b[i4]));
        if (rank4(v, 4) < 4) bad++;
    }
    return bad;
}
static int pencil(void) {
    int bad = 0, z[8], c[4]; for (int l = 0; l < 4; l++) c[l] = mv(&Ai[l], b[l]);
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) if (i != j) {
        int n = 0;
        for (int k = 0; k < 4; k++) if (k != i) z[n++] = mv(&A[i], c[k]);
        for (int l = 0; l < 4; l++) if (l != i && l != j) z[n++] = b[l];
        for (int k = 0; k < 4; k++) if (k != j) z[n++] = mv(&A[j], c[k]);
        if (!pencil_ok(b[i], b[j], z, n)) bad++;
        n = 0;
        for (int k = 0; k < 4; k++) if (k != i) z[n++] = mv(&Ai[i], b[k]);
        for (int l = 0; l < 4; l++) if (l != i && l != j) z[n++] = c[l];
        for (int k = 0; k < 4; k++) if (k != j) z[n++] = mv(&Ai[j], b[k]);
        if (!pencil_ok(c[i], c[j], z, n)) bad++;
    }
    return bad;
}
static int PW = 3;
static int cost(void) { for (int i = 0; i < 4; i++) if (!inv_mat(&A[i], &Ai[i])) return 1 << 20; return univ() + PW * pencil(); }
static void rand_gl(mat *M) { mat R; do { for (int j = 0; j < 4; j++) M->c[j] = xr() & 255; } while (!inv_mat(M, &R)); }
static int rand_vec(void) { int v; do v = xr() & 255; while (!v); return v; }
int main(int argc, char **argv) {
    double secs = atof(argv[1]); rs ^= (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; if (argc > 3) PW = atoi(argv[3]);
    const char *out = argc > 4 ? argv[4] : NULL;
    for (int l = 0; l < 4; l++) for (int v = 0; v < 256; v++) { int o = 0; for (int r = 0; r < 4; r++) o |= MUL[l][coord(v, r)] << (2 * r); smul[l][v] = o; }
    clock_t t0 = clock(); int best = 1 << 30; long evals = 0, restarts = 0;
    mat bA[4]; int bb[4];
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs && best > 0) {
        restarts++;
        for (int j = 0; j < 4; j++) A[0].c[j] = 1 << (2 * j);
        for (int i = 1; i < 4; i++) rand_gl(&A[i]);
        for (int i = 0; i < 4; i++) b[i] = rand_vec();
        int c = cost(), stall = 0;
        while (stall < 3000 && c > 0) {
            mat sA[4]; int sb[4]; memcpy(sA, A, sizeof A); memcpy(sb, b, sizeof b);
            if (xr() & 1) { int k = 1 + xr() % 3; int col = xr() % 4, row = xr() % 4;
                A[k].c[col] = (A[k].c[col] & ~(3 << (2 * row))) | ((int)(xr() % 4) << (2 * row)); }
            else b[xr() % 4] = rand_vec();
            int c2 = cost(); evals++;
            if (c2 <= c) { stall = (c2 < c) ? 0 : stall + 1; c = c2; }
            else { memcpy(A, sA, sizeof A); memcpy(b, sb, sizeof b); stall++; }
        }
        if (c < best) { best = c; memcpy(bA, A, sizeof A); memcpy(bb, b, sizeof b);
            for (int i = 0; i < 4; i++) inv_mat(&A[i], &Ai[i]);
            printf("best %d (univ %d, pencil %d) after %ld restarts %ld evals\n", c, univ(), pencil(), restarts, evals); fflush(stdout); }
    }
    if (out) { FILE *f = fopen(out, "w");
        for (int i = 0; i < 4; i++) { for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) fprintf(f, "%d ", coord(bA[i].c[c], r)); fprintf(f, "\n"); }
        for (int i = 0; i < 4; i++) { for (int r = 0; r < 4; r++) fprintf(f, "%d ", coord(bb[i], r)); fprintf(f, "\n"); }
        fclose(f); printf("written %s\n", out); }
    printf("final best %d restarts %ld evals %ld\n", best, restarts, evals);
    return 0;
}
