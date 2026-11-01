/* Route-chart search over F_5 (prime field; port of research/theorems/squad165/chart_search.c).
   A_0 = I, A_1..A_3 in GL_4(F_5), b_0..b_3 in F_5^4.
   Cost = (#singular nonbacktracking 4-patterns, both sides, out of 216) + PW * (#ordered pairs i!=j whose
   pencil set does not meet all 6 points of PG(1,5)).  Pencil-complete = pencil violations 0.
   usage: chart5 seconds seed [PW] [out]
   out: 4 lines of 16 entries (A_0..A_3 row-major), then 4 lines of 4 entries (b_0..b_3). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>
#define P 5
typedef struct { int a[4][4]; } mat;
typedef struct { int v[4]; } vec;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int INV[P] = {0, 1, 3, 2, 4};
static mat A[4], Ai[4]; static vec b[4];
static vec mv(const mat *M, vec x) { vec y; for (int r = 0; r < 4; r++) { int s = 0; for (int c = 0; c < 4; c++) s += M->a[r][c] * x.v[c]; y.v[r] = s % P; } return y; }
static vec vadd(vec x, vec y) { vec z; for (int r = 0; r < 4; r++) z.v[r] = (x.v[r] + y.v[r]) % P; return z; }
static int vzero(vec x) { for (int r = 0; r < 4; r++) if (x.v[r]) return 0; return 1; }
/* row-reduce a copy of n vectors (as rows of length 4), return rank */
static int rank_of(const vec *in, int n) {
    int a[8][4]; for (int i = 0; i < n; i++) for (int c = 0; c < 4; c++) a[i][c] = in[i].v[c];
    int r = 0;
    for (int col = 0; col < 4 && r < n; col++) {
        int p = -1; for (int i = r; i < n; i++) if (a[i][col]) { p = i; break; }
        if (p < 0) continue;
        for (int c = 0; c < 4; c++) { int t = a[p][c]; a[p][c] = a[r][c]; a[r][c] = t; }
        int iv = INV[a[r][col]]; for (int c = 0; c < 4; c++) a[r][c] = a[r][c] * iv % P;
        for (int i = 0; i < n; i++) if (i != r && a[i][col]) { int f = a[i][col]; for (int c = 0; c < 4; c++) a[i][c] = ((a[i][c] - f * a[r][c]) % P + P) % P; }
        r++;
    }
    return r;
}
static int inv_mat(const mat *M, mat *R) {
    int X[4][8];
    for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) { X[r][c] = M->a[r][c]; X[r][4 + c] = (r == c); }
    for (int col = 0; col < 4; col++) {
        int p = -1; for (int r = col; r < 4; r++) if (X[r][col]) { p = r; break; }
        if (p < 0) return 0;
        for (int c = 0; c < 8; c++) { int t = X[p][c]; X[p][c] = X[col][c]; X[col][c] = t; }
        int iv = INV[X[col][col]]; for (int c = 0; c < 8; c++) X[col][c] = X[col][c] * iv % P;
        for (int r = 0; r < 4; r++) if (r != col && X[r][col]) { int f = X[r][col]; for (int c = 0; c < 8; c++) X[r][c] = ((X[r][c] - f * X[col][c]) % P + P) % P; }
    }
    for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) R->a[r][c] = X[r][4 + c];
    return 1;
}
/* pencil_ok: the quotient map F_5^4 -> F_5^2 modulo W = <w1,w2>, then the 8 vectors must hit all 6 points of PG(1,5) */
static int pencil_ok(vec w1, vec w2, const vec *z, int nz) {
    vec wv[2] = {w1, w2}; if (rank_of(wv, 2) < 2) return 0;
    vec basis[4]; basis[0] = w1; basis[1] = w2; int nb = 2;
    for (int r = 0; r < 4 && nb < 4; r++) { vec e = {{0,0,0,0}}; e.v[r] = 1; vec t[4]; for (int i = 0; i < nb; i++) t[i] = basis[i]; t[nb] = e;
        if (rank_of(t, nb + 1) == nb + 1) basis[nb++] = e; }
    mat B, Bi; for (int c = 0; c < 4; c++) for (int r = 0; r < 4; r++) B.a[r][c] = basis[c].v[r];
    if (!inv_mat(&B, &Bi)) return 0;
    int seen = 0;
    for (int i = 0; i < nz; i++) {
        vec x = mv(&Bi, z[i]); int x3 = x.v[2], x4 = x.v[3];
        if (!x3 && !x4) continue;
        int p = !x3 ? 5 : x4 * INV[x3] % P;
        seen |= 1 << p;
    }
    return seen == 63;
}
static int PW = 3;
static int univ(void) {
    int bad = 0; vec v[4];
    for (int i1 = 0; i1 < 4; i1++) for (int i2 = 0; i2 < 4; i2++) if (i2 != i1) for (int i3 = 0; i3 < 4; i3++) if (i3 != i2)
    for (int i4 = 0; i4 < 4; i4++) if (i4 != i3) {
        v[0] = mv(&Ai[i2], b[i1]); v[1] = mv(&Ai[i2], b[i2]); v[2] = mv(&Ai[i3], b[i3]); v[3] = mv(&Ai[i3], b[i4]);
        if (rank_of(v, 4) < 4) bad++;
        v[0] = mv(&A[i2], mv(&Ai[i1], b[i1])); v[1] = b[i2]; v[2] = b[i3]; v[3] = mv(&A[i3], mv(&Ai[i4], b[i4]));
        if (rank_of(v, 4) < 4) bad++;
    }
    return bad;
}
static int pencil(void) {
    int bad = 0; vec z[8], c[4];
    for (int l = 0; l < 4; l++) c[l] = mv(&Ai[l], b[l]);
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
static int cost(void) { for (int i = 0; i < 4; i++) if (!inv_mat(&A[i], &Ai[i])) return 1 << 20; return univ() + PW * pencil(); }
static void rand_gl(mat *M) { do { for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) M->a[r][c] = xr() % P; } while (!inv_mat(M, &Ai[0])); }
static vec rand_vec(void) { vec v; do { for (int r = 0; r < 4; r++) v.v[r] = xr() % P; } while (vzero(v)); return v; }
int main(int argc, char **argv) {
    double secs = atof(argv[1]); rs ^= (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; if (argc > 3) PW = atoi(argv[3]);
    const char *out = argc > 4 ? argv[4] : NULL;
    clock_t t0 = clock(); int best = 1 << 30; long evals = 0, restarts = 0;
    mat bA[4]; vec bb[4];
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs && best > 0) {
        restarts++;
        memset(&A[0], 0, sizeof A[0]); for (int r = 0; r < 4; r++) A[0].a[r][r] = 1;
        for (int i = 1; i < 4; i++) { mat M; do { for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) M.a[r][c] = xr() % P; } while (!inv_mat(&M, &Ai[0])); A[i] = M; }
        for (int i = 0; i < 4; i++) b[i] = rand_vec();
        int c = cost(), stall = 0;
        while (stall < 3000 && c > 0) {
            mat sA[4]; vec sb[4]; memcpy(sA, A, sizeof A); memcpy(sb, b, sizeof b);
            if (xr() & 1) { int k = 1 + xr() % 3; A[k].a[xr() % 4][xr() % 4] = xr() % P; }
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
        for (int i = 0; i < 4; i++) { for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) fprintf(f, "%d ", bA[i].a[r][c]); fprintf(f, "\n"); }
        for (int i = 0; i < 4; i++) { for (int r = 0; r < 4; r++) fprintf(f, "%d ", bb[i].v[r]); fprintf(f, "\n"); }
        fclose(f); printf("written %s\n", out); }
    printf("final best %d restarts %ld evals %ld\n", best, restarts, evals);
    return 0;
}
