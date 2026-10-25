/* octohex.c: the split Cayley hexagon H(q) from an octonion algebra over F_q (q odd prime): points = singular
   1-spaces of the imaginary octonions V (basis u0..u6, norm sum x_i^2), lines = 2-spaces <x, y> of V with x y = 0.
   For a point x the kernel of y -> x y on V is a totally singular 3-space (the ideal plane of x); its 12 lines
   through x are the hexagon lines on x.  Structure constants T[i][j][k] (8x8x8, index 0 = 1, index a+1 = u_a) are read
   from TFILE.  Output: hexgen.c format (int32 q, N, L; L*(q+1) int32 point ids; N*7 uint8 coordinates), points sorted
   by code sum x_i q^i with first nonzero coordinate 1.  usage: octohex q TFILE OUT.bin */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int q, T[8][8][8], inv[64];
static long codeof(const int *v) { long c = 0; for (int i = 6; i >= 0; i--) c = c * q + v[i]; return c; }
static void norm7(int *v) { int i = 0; while (i < 7 && v[i] % q == 0) i++; if (i == 7) return; int s = inv[(v[i] % q + q) % q]; for (int j = 0; j < 7; j++) v[j] = ((v[j] % q + q) % q) * s % q; }
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: octohex q TFILE OUT.bin\n"); return 1; }
    q = atoi(argv[1]); for (int a = 1; a < q; a++) for (int b = 1; b < q; b++) if (a * b % q == 1) inv[a] = b;
    FILE *f = fopen(argv[2], "r"); for (int i = 0; i < 512; i++) if (fscanf(f, "%d", &T[i / 64][(i / 8) % 8][i % 8]) != 1) return 1; fclose(f);
    long tot = 1; for (int i = 0; i < 7; i++) tot *= q;
    int32_t *lookup = malloc(4 * tot); for (long c = 0; c < tot; c++) lookup[c] = -1;
    int cap = 1 << 18, N = 0; uint8_t *P = malloc(7 * (size_t)cap); int v[7];
    for (long c = 0; c < tot; c++) {
        long t = c; for (int i = 0; i < 7; i++) { v[i] = t % q; t /= q; }
        int i = 0; while (i < 7 && v[i] == 0) i++; if (i == 7 || v[i] != 1) continue;
        int s = 0; for (int j = 0; j < 7; j++) s += v[j] * v[j]; if (s % q) continue;
        if (N == cap) { cap *= 2; P = realloc(P, 7 * (size_t)cap); }
        for (int j = 0; j < 7; j++) P[7 * N + j] = v[j]; lookup[c] = N++;
    }
    fprintf(stderr, "points %d\n", N);
    int Lcap = N + 16, L = 0; int32_t *lines = malloc(sizeof(int32_t) * (q + 1) * (size_t)Lcap);
    for (int x = 0; x < N; x++) {
        int xv[7]; for (int j = 0; j < 7; j++) xv[j] = P[7 * x + j];
        /* M[k][j] = component k of x * u_j */
        int M[8][7];
        for (int k = 0; k < 8; k++) for (int j = 0; j < 7; j++) { int s = 0; for (int i = 0; i < 7; i++) s += xv[i] * T[i + 1][j + 1][k]; M[k][j] = (s % q + q) % q; }
        /* kernel by row reduction */
        int piv[8], np_ = 0, r = 0;
        for (int c = 0; c < 7 && r < 8; c++) {
            int p = -1; for (int i = r; i < 8; i++) if (M[i][c]) { p = i; break; }
            if (p < 0) continue;
            for (int j = 0; j < 7; j++) { int t2 = M[r][j]; M[r][j] = M[p][j]; M[p][j] = t2; }
            int s = inv[M[r][c]]; for (int j = 0; j < 7; j++) M[r][j] = M[r][j] * s % q;
            for (int i = 0; i < 8; i++) if (i != r && M[i][c]) { int fct = M[i][c]; for (int j = 0; j < 7; j++) M[i][j] = ((M[i][j] - fct * M[r][j]) % q + q) % q; }
            piv[np_++] = c; r++;
        }
        int isp[7] = {0}; for (int i = 0; i < np_; i++) isp[piv[i]] = 1;
        int K[7][7], nk = 0;
        for (int fc = 0; fc < 7; fc++) if (!isp[fc]) {
            for (int j = 0; j < 7; j++) K[nk][j] = 0; K[nk][fc] = 1;
            for (int i = 0; i < np_; i++) K[nk][piv[i]] = (q - M[i][fc]) % q;
            nk++;
        }
        if (nk != 3) { fprintf(stderr, "kernel dim %d at point %d\n", nk, x); return 1; }
        /* basis x, b1, b2 of the kernel: pick two kernel vectors independent from x */
        int B[3][7]; for (int j = 0; j < 7; j++) B[0][j] = xv[j];
        int nb = 1;
        for (int t2 = 0; t2 < 3 && nb < 3; t2++) {
            /* check independence of K[t2] from B[0..nb-1] by rank */
            int R[3][7]; for (int a = 0; a < nb; a++) for (int j = 0; j < 7; j++) R[a][j] = B[a][j];
            for (int j = 0; j < 7; j++) R[nb][j] = K[t2][j];
            int rr = 0; int RR[3][7]; memcpy(RR, R, sizeof RR);
            for (int c = 0; c < 7 && rr < nb + 1; c++) {
                int p = -1; for (int i = rr; i <= nb; i++) if (RR[i][c]) { p = i; break; } if (p < 0) continue;
                for (int j = 0; j < 7; j++) { int t3 = RR[rr][j]; RR[rr][j] = RR[p][j]; RR[p][j] = t3; }
                int s = inv[RR[rr][c]]; for (int j = 0; j < 7; j++) RR[rr][j] = RR[rr][j] * s % q;
                for (int i = 0; i <= nb; i++) if (i != rr && RR[i][c]) { int fct = RR[i][c]; for (int j = 0; j < 7; j++) RR[i][j] = ((RR[i][j] - fct * RR[rr][j]) % q + q) % q; }
                rr++;
            }
            if (rr == nb + 1) { for (int j = 0; j < 7; j++) B[nb][j] = K[t2][j]; nb++; }
        }
        if (nb != 3) { fprintf(stderr, "basis failure at %d\n", x); return 1; }
        /* the q+1 lines through x: directions d = b1 + t b2 (t < q) and b2 */
        for (int t2 = 0; t2 <= q; t2++) {
            int d[7]; for (int j = 0; j < 7; j++) d[j] = (t2 < q) ? (B[1][j] + t2 * B[2][j]) % q : B[2][j];
            int ids[32], ok = 1, mn = x;
            ids[0] = x;
            for (int a = 0; a < q; a++) {
                int w[7]; for (int j = 0; j < 7; j++) w[j] = (d[j] + a * xv[j]) % q;
                norm7(w); int id = lookup[codeof(w)];
                if (id < 0) { ok = 0; break; }
                ids[a + 1] = id; if (id < mn) mn = id;
            }
            if (!ok) { fprintf(stderr, "non-singular point on a line at %d\n", x); return 1; }
            if (mn != x) continue;                 /* record each line once, from its smallest point */
            if (L == Lcap) { fprintf(stderr, "too many lines\n"); return 1; }
            for (int a = 0; a <= q; a++) lines[(size_t)L * (q + 1) + a] = ids[a];
            L++;
        }
    }
    fprintf(stderr, "lines %d (want %d)\n", L, N);
    FILE *o = fopen(argv[3], "wb"); int32_t hdr[3] = { q, N, L }; fwrite(hdr, 4, 3, o);
    fwrite(lines, 4, (size_t)L * (q + 1), o); fwrite(P, 1, 7 * (size_t)N, o); fclose(o);
    return L == N ? 0 : 2;
}
