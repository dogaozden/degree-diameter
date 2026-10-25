/* c5: stabiliser of a pairwise-opposite set S in PGO_7(7) (similitudes of Q(6,7) preserving S).
   Usage: stab7 HEXBIN SETFILE OUTMATS   -> prints group order, writes all elements (7x7 matrices, row-major, one per line).
   Method: basis e_0..e_6 chosen inside S; images f_j in S, scalars lam_j, multiplier c; CSP over the 6 free images with
   pairwise Gram constraints; each leaf is a candidate matrix G = F*E^{-1}, checked against all of S. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define P 7
static int inv7[P] = {0, 1, 4, 5, 2, 3, 6};
int q, N, L;
unsigned char *C;           /* N*7 coords */
int ns; int *Sid; int *Spos; /* Spos[point] = index in S or -1 */
int X[300][7];              /* normalised vectors of S */
int BS[300][300];           /* B on S */
int b[7];                   /* basis positions in S */
int Einv[7][7];
int lam[7][300];            /* lam[j][p] for level j (given p1 and c) */
int dom[7][300], ndom[7];
int pick[7];
long nsol = 0, nleaf = 0;
FILE *fout;
int ptidx(int *v) { int code = 0, m = 1; for (int i = 0; i < 7; i++) { code += v[i] * m; m *= 7; } return code; }
unsigned char *idxmap;     /* code -> point id or 255 */
int *idxp;
static int mod7(int x) { x %= P; if (x < 0) x += P; return x; }
int inv_mat(int A[7][7], int R[7][7]) { /* Gauss-Jordan mod 7 */
    int M[7][14];
    for (int i = 0; i < 7; i++) for (int j = 0; j < 7; j++) { M[i][j] = mod7(A[i][j]); M[i][7 + j] = (i == j); }
    for (int c = 0; c < 7; c++) {
        int piv = -1; for (int i = c; i < 7; i++) if (M[i][c]) { piv = i; break; }
        if (piv < 0) return 0;
        for (int j = 0; j < 14; j++) { int t = M[c][j]; M[c][j] = M[piv][j]; M[piv][j] = t; }
        int iv = inv7[M[c][c]];
        for (int j = 0; j < 14; j++) M[c][j] = (M[c][j] * iv) % P;
        for (int i = 0; i < 7; i++) if (i != c && M[i][c]) { int f = M[i][c]; for (int j = 0; j < 14; j++) M[i][j] = mod7(M[i][j] - f * M[c][j]); }
    }
    for (int i = 0; i < 7; i++) for (int j = 0; j < 7; j++) R[i][j] = M[i][7 + j];
    return 1;
}
static inline int Bf(const int *x, const int *y) { return mod7(x[0]*y[4] + x[4]*y[0] + x[1]*y[5] + x[5]*y[1] + x[2]*y[6] + x[6]*y[2] - 2*x[3]*y[3]); }
int BEE[7][7];
int cc;               /* multiplier */
int p1;               /* image of basis e_0 */
int ok_check(int G[7][7]) {
    /* images of all S points under g = G*Einv ... we apply to S directly: g(x) = G*Einv*x */
    static int M[7][7]; int Mx[7][7];
    for (int i = 0; i < 7; i++) for (int j = 0; j < 7; j++) { int s = 0; for (int k = 0; k < 7; k++) s += G[i][k] * Einv[k][j]; M[i][j] = mod7(s); }
    for (int t = 0; t < ns; t++) {
        int v[7];
        for (int i = 0; i < 7; i++) { int s = 0; for (int k = 0; k < 7; k++) s += M[i][k] * X[t][k]; v[i] = mod7(s); }
        int nz = 0; while (nz < 7 && v[nz] == 0) nz++;
        if (nz == 7) return 0;
        int iv = inv7[v[nz]]; for (int i = 0; i < 7; i++) v[i] = (v[i] * iv) % P;
        int code = ptidx(v);
        int pt = idxp[code];
        if (pt < 0) return 0;
        if (Spos[pt] < 0) return 0;
    }
    (void)Mx;
    return 1;
}
int rank7(int G[7][7]) { int M[7][7]; for (int i = 0; i < 7; i++) for (int j = 0; j < 7; j++) M[i][j] = mod7(G[i][j]);
  int r = 0; for (int c = 0; c < 7; c++) { int piv = -1; for (int i = r; i < 7; i++) if (M[i][c]) { piv = i; break; } if (piv < 0) continue;
    for (int k = 0; k < 7; k++) { int t = M[r][k]; M[r][k] = M[piv][k]; M[piv][k] = t; }
    int iv = inv7[M[r][c]]; for (int k = 0; k < 7; k++) M[r][k] = (M[r][k] * iv) % P;
    for (int i = 0; i < 7; i++) if (i != r && M[i][c]) { int f = M[i][c]; for (int k = 0; k < 7; k++) M[i][k] = mod7(M[i][k] - f * M[r][k]); }
    r++; } return r; }
void leaf(void) {
    nleaf++;
    /* F columns: lam_0 = 1 with f_0 = X[p1]; lam_j X[pick[j]] */
    int G[7][7];
    int lamv[7];
    lamv[0] = 1; for (int j = 1; j < 7; j++) lamv[j] = lam[j][pick[j]];
    int fpos[7]; fpos[0] = p1; for (int j = 1; j < 7; j++) fpos[j] = pick[j];
    for (int i = 0; i < 7; i++) for (int j = 0; j < 7; j++) G[i][j] = (lamv[j] * X[fpos[j]][i]) % P;
    /* G maps e_j (columns of identity in basis of e) ... g = G * Einv where Einv = inverse of E=[X[b_0]..X[b_6]] columns */
    if (rank7(G) == 7 && ok_check(G)) {
        nsol++;
        /* write g = G*Einv */
        int M[7][7];
        for (int i = 0; i < 7; i++) for (int j = 0; j < 7; j++) { int s = 0; for (int k = 0; k < 7; k++) s += G[i][k] * Einv[k][j]; M[i][j] = mod7(s); }
        for (int i = 0; i < 7; i++) for (int j = 0; j < 7; j++) fprintf(fout, "%d ", M[i][j]);
        fprintf(fout, "\n");
    }
}
void dfs(int j) {
    if (j == 7) { leaf(); return; }
    for (int t = 0; t < ndom[j]; t++) {
        int p = dom[j][t]; int ok = 1;
        for (int k = 1; k < j && ok; k++) {
            int pk = pick[k];
            int lhs = (lam[k][pk] * lam[j][p] % P) * BS[pk][p] % P;
            int rhs = (cc * BEE[k][j]) % P;
            if (lhs != rhs) ok = 0;
        }
        if (!ok) continue;
        pick[j] = p; dfs(j + 1);
    }
}
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: stab7 HEXBIN SETFILE OUTMATS\n"); return 2; }
    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3]; if (!f || fread(hdr, 4, 3, f) != 3) return 2;
    q = hdr[0]; N = hdr[1]; L = hdr[2];
    fseek(f, 12 + 4L * L * (q + 1), SEEK_SET);
    C = malloc((size_t)N * 7); if (fread(C, 1, (size_t)N * 7, f) != (size_t)N * 7) return 2; fclose(f);
    idxmap = NULL; idxp = malloc(sizeof(int) * 823543); for (int i = 0; i < 823543; i++) idxp[i] = -1;
    for (int p = 0; p < N; p++) { int code = 0, m = 1; for (int i = 0; i < 7; i++) { code += C[p * 7 + i] * m; m *= 7; } idxp[code] = p; }
    Spos = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) Spos[i] = -1;
    Sid = malloc(sizeof(int) * 300);
    f = fopen(argv[2], "r"); int x; ns = 0; while (fscanf(f, "%d", &x) == 1) { Sid[ns] = x; Spos[x] = ns; ns++; } fclose(f);
    for (int s = 0; s < ns; s++) for (int i = 0; i < 7; i++) X[s][i] = C[Sid[s] * 7 + i];
    for (int s = 0; s < ns; s++) for (int t = 0; t < ns; t++) BS[s][t] = Bf(X[s], X[t]);
    /* basis: greedy independent points of S */
    int Rk[7][7]; int nb = 0; int cur[7][7]; (void)cur;
    {
        int rows[7][7]; int r = 0;
        for (int s = 0; s < ns && nb < 7; s++) {
            int test[8][7]; for (int i = 0; i < r; i++) memcpy(test[i], rows[i], sizeof(int) * 7); memcpy(test[r], X[s], sizeof(int) * 7);
            /* rank of r+1 rows mod 7 */
            int M[8][7]; for (int i = 0; i <= r; i++) for (int k = 0; k < 7; k++) M[i][k] = test[i][k];
            int rank = 0; int row = 0;
            for (int c = 0; c < 7 && row <= r; c++) {
                int piv = -1; for (int i = row; i <= r; i++) if (M[i][c]) { piv = i; break; }
                if (piv < 0) continue;
                for (int k = 0; k < 7; k++) { int t2 = M[row][k]; M[row][k] = M[piv][k]; M[piv][k] = t2; }
                int iv = inv7[M[row][c]]; for (int k = 0; k < 7; k++) M[row][k] = (M[row][k] * iv) % P;
                for (int i = 0; i <= r; i++) if (i != row && M[i][c]) { int fct = M[i][c]; for (int k = 0; k < 7; k++) M[i][k] = mod7(M[i][k] - fct * M[row][k]); }
                row++; rank++;
            }
            if (rank == r + 1) { memcpy(rows[r], X[s], sizeof(int) * 7); b[nb++] = s; r++; }
        }
    }
    if (nb < 7) { fprintf(stderr, "no basis\n"); return 1; }
    /* E columns = X[b_j]; Einv */
    int E[7][7]; for (int i = 0; i < 7; i++) for (int j = 0; j < 7; j++) E[i][j] = X[b[j]][i];
    if (!inv_mat(E, Einv)) { fprintf(stderr, "singular\n"); return 1; }
    for (int j = 0; j < 7; j++) for (int k = 0; k < 7; k++) BEE[j][k] = BS[b[j]][b[k]];
    fprintf(stderr, "ns=%d basis=%d %d %d %d %d %d %d\n", ns, b[0], b[1], b[2], b[3], b[4], b[5], b[6]);
    fout = fopen(argv[3], "w");
    int nscan = (argc > 4) ? atoi(argv[4]) : ns;
    for (p1 = 0; p1 < nscan; p1++) {
        for (cc = 1; cc < P; cc++) {
            /* level 0 fixed to p1; levels j>=1: domain = {p : BS[p1][p] != 0}, lam_j(p) = cc*BEE[0][j]/BS[p1][p] */
            for (int j = 1; j < 7; j++) {
                ndom[j] = 0;
                for (int p = 0; p < ns; p++) {
                    if (BS[p1][p] == 0) continue;
                    lam[j][p] = (cc * BEE[0][j] % P) * inv7[BS[p1][p]] % P;
                    dom[j][ndom[j]++] = p;
                }
            }
            if (BEE[0][0] != 0) {}  /* unused */
            dfs(1);
        }
        if (p1 % 48 == 47) fprintf(stderr, "p1=%d nsol=%ld leaves=%ld\n", p1, nsol, nleaf);
    }
    fclose(fout);
    printf("leaves %ld group_order %ld\n", nleaf, nsol);
    return 0;
}
