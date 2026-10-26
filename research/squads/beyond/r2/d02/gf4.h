/* GF(4) = {0,1,2=w,3=w+1}, addition = XOR. Shared by chart and controller programs. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
static const uint8_t MUL[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static const uint8_t INV4[4] = {0,1,3,2};
typedef struct { uint8_t a[4][4]; } M4;
typedef struct { uint8_t v[4]; } V4;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static M4 Ach[5], Aich[5]; static V4 bch[5];
static V4 mv(const M4 *M, V4 x) { V4 y; for (int r = 0; r < 4; r++) { uint8_t s = 0; for (int c = 0; c < 4; c++) s ^= MUL[M->a[r][c]][x.v[c]]; y.v[r] = s; } return y; }
static M4 mm(const M4 *A, const M4 *B) { M4 C; for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) { uint8_t s = 0; for (int k = 0; k < 4; k++) s ^= MUL[A->a[r][k]][B->a[k][c]]; C.a[r][c] = s; } return C; }
/* invert; return 0 if singular */
static int inv4(const M4 *M, M4 *R) {
    uint8_t X[4][8];
    for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) { X[r][c] = M->a[r][c]; X[r][4 + c] = (r == c); }
    for (int col = 0; col < 4; col++) {
        int p = -1; for (int r = col; r < 4; r++) if (X[r][col]) { p = r; break; }
        if (p < 0) return 0;
        for (int c = 0; c < 8; c++) { uint8_t t = X[p][c]; X[p][c] = X[col][c]; X[col][c] = t; }
        uint8_t iv = INV4[X[col][col]]; for (int c = 0; c < 8; c++) X[col][c] = MUL[iv][X[col][c]];
        for (int r = 0; r < 4; r++) if (r != col && X[r][col]) { uint8_t f = X[r][col]; for (int c = 0; c < 8; c++) X[r][c] ^= MUL[f][X[col][c]]; }
    }
    for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) R->a[r][c] = X[r][4 + c];
    return 1;
}
static int rank_n(const V4 *in, int n) {
    uint8_t a[8][4]; for (int i = 0; i < n; i++) for (int c = 0; c < 4; c++) a[i][c] = in[i].v[c];
    int r = 0;
    for (int col = 0; col < 4 && r < n; col++) {
        int p = -1; for (int i = r; i < n; i++) if (a[i][col]) { p = i; break; }
        if (p < 0) continue;
        for (int c = 0; c < 4; c++) { uint8_t t = a[p][c]; a[p][c] = a[r][c]; a[r][c] = t; }
        uint8_t iv = INV4[a[r][col]]; for (int c = 0; c < 4; c++) a[r][c] = MUL[iv][a[r][c]];
        for (int i = 0; i < n; i++) if (i != r && a[i][col]) { uint8_t f = a[i][col]; for (int c = 0; c < 4; c++) a[i][c] ^= MUL[f][a[r][c]]; }
        r++;
    }
    return r;
}
/* Walk of colour word w (length L) starting on side s0 (0 = A, 1 = B).
   Step k: A->B uses (A_t, b_t); B->A uses (A_t^-1, A_t^-1 b_t). Full = directions span F4^4. */
static int word_full(const int *w, int L, int s0) {
    V4 D[5]; M4 P; memset(&P, 0, sizeof P); for (int r = 0; r < 4; r++) P.a[r][r] = 1;
    for (int k = L - 1; k >= 0; k--) {
        int side = s0 ^ (k & 1); int t = w[k];
        const M4 *M = side ? &Aich[t] : &Ach[t];
        V4 c = side ? mv(&Aich[t], bch[t]) : bch[t];
        D[k] = mv(&P, c);
        P = mm(&P, M);
    }
    return rank_n(D, L) == 4;
}
static int read_chart(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) return 0;
    for (int t = 0; t < 5; t++) {
        for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) { int x; if (fscanf(f, "%d", &x) != 1) return 0; Ach[t].a[r][c] = x; }
        for (int r = 0; r < 4; r++) { int x; if (fscanf(f, "%d", &x) != 1) return 0; bch[t].v[r] = x; }
        if (!inv4(&Ach[t], &Aich[t])) return 0;
    }
    fclose(f); return 1;
}
static void write_chart(const char *fn) {
    FILE *f = fopen(fn, "w");
    for (int t = 0; t < 5; t++) { for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) fprintf(f, "%d ", Ach[t].a[r][c]);
        for (int r = 0; r < 4; r++) fprintf(f, "%d ", bch[t].v[r]); fprintf(f, "\n"); }
    fclose(f);
}
