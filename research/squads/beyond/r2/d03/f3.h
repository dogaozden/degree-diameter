/* F_3 route-chart helpers. Walk of length 4 with letters c1..c4 (consecutive distinct):
   A-start: steps forward(c1), backward(c2), forward(c3), backward(c4); B-start: backward, forward, backward, forward.
   forward step y -> A_c y + lam b_c ; backward step y -> A_c^{-1} y + lam A_c^{-1} b_c ; lam in F_3.
   Endpoint = P x + sum_k lam_k w_k with w_k = L_4..L_{k+1} c_k; pattern nonsingular iff w_1..w_4 independent. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef struct { int a[4][4]; } mat;
static mat A[6], Ai[6]; static int bv[6][4];
static int inv_mat(const mat *M, mat *R) {
    int X[4][8];
    for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) { X[r][c] = M->a[r][c]; X[r][4 + c] = (r == c); }
    for (int col = 0; col < 4; col++) {
        int p = -1; for (int r = col; r < 4; r++) if (X[r][col] % 3) { p = r; break; }
        if (p < 0) return 0;
        for (int c = 0; c < 8; c++) { int t = X[p][c]; X[p][c] = X[col][c]; X[col][c] = t; }
        if (X[col][col] == 2) for (int c = 0; c < 8; c++) X[col][c] = X[col][c] * 2 % 3;
        for (int r = 0; r < 4; r++) if (r != col && X[r][col] % 3) { int f = X[r][col]; for (int c = 0; c < 8; c++) X[r][c] = ((X[r][c] - f * X[col][c]) % 3 + 3) % 3; }
    }
    for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) R->a[r][c] = X[r][4 + c];
    return 1;
}
static void mmul(const mat *X, const mat *Y, mat *Z) {
    mat T; for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) { int s = 0; for (int k = 0; k < 4; k++) s += X->a[r][k] * Y->a[k][c]; T.a[r][c] = s % 3; }
    *Z = T;
}
static void mvec(const mat *M, const int *x, int *y) { for (int r = 0; r < 4; r++) { int s = 0; for (int c = 0; c < 4; c++) s += M->a[r][c] * x[c]; y[r] = s % 3; } }
static int rank_n(int v[][4], int n) {
    int a[8][4]; memcpy(a, v, sizeof(int) * 4 * n); int r = 0;
    for (int col = 0; col < 4 && r < n; col++) {
        int p = -1; for (int i = r; i < n; i++) if (a[i][col] % 3) { p = i; break; }
        if (p < 0) continue;
        for (int c = 0; c < 4; c++) { int t = a[p][c]; a[p][c] = a[r][c]; a[r][c] = t; }
        if (a[r][col] == 2) for (int c = 0; c < 4; c++) a[r][c] = a[r][c] * 2 % 3;
        for (int i = 0; i < n; i++) if (i != r && a[i][col] % 3) { int f = a[i][col]; for (int c = 0; c < 4; c++) a[i][c] = ((a[i][c] - f * a[r][c]) % 3 + 3) % 3; }
        r++;
    }
    return r;
}
/* side 0 = A-start, 1 = B-start. Returns 1 if the pattern is nonsingular. */
static int pattern_ok(int side, const int *c) {
    mat Pacc; memset(&Pacc, 0, sizeof Pacc); for (int i = 0; i < 4; i++) Pacc.a[i][i] = 1;
    int w[4][4];
    for (int k = 3; k >= 0; k--) {
        int fwd = ((k % 2) == 0) ? (side == 0) : (side == 1); /* step k+1 forward? */
        int cv[4]; mat L;
        if (fwd) { L = A[c[k]]; memcpy(cv, bv[c[k]], sizeof cv); }
        else { L = Ai[c[k]]; mvec(&Ai[c[k]], bv[c[k]], cv); }
        mvec(&Pacc, cv, w[k]);
        mmul(&Pacc, &L, &Pacc);
    }
    return rank_n(w, 4) == 4;
}
static int chart_read(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) return 0;
    for (int t = 0; t < 6; t++) { for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) if (fscanf(f, "%d", &A[t].a[r][c]) != 1) return 0;
        for (int i = 0; i < 4; i++) if (fscanf(f, "%d", &bv[t][i]) != 1) return 0; }
    fclose(f);
    for (int t = 0; t < 6; t++) if (!inv_mat(&A[t], &Ai[t])) return 0;
    return 1;
}
/* good[side][c1][c2][c3][c4] */
static unsigned char good[2][6][6][6][6];
static void compute_good(void) {
    for (int s = 0; s < 2; s++) for (int c1 = 0; c1 < 6; c1++) for (int c2 = 0; c2 < 6; c2++) for (int c3 = 0; c3 < 6; c3++) for (int c4 = 0; c4 < 6; c4++) {
        int c[4] = {c1, c2, c3, c4};
        good[s][c1][c2][c3][c4] = 0;
        if (c1 == c2 || c2 == c3 || c3 == c4) continue;
        good[s][c1][c2][c3][c4] = pattern_ok(s, c);
    }
}
