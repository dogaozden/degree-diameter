/* Route charts over F_3^4 for the bipartite controller lift at (12,5): 4 letters x 3 scalars, degree 12.
   Chart: A_0..A_3 in GL_4(F_3) (gauge A_0 = I), b_0..b_3 in F_3^4.  Lift of a properly 4-edge-coloured 4-regular
   bipartite controller: (a, x)_A ~ (b, A_c x + lam b_c)_B, lam in F_3, c = colour of the controller edge ab.
   Conditions (derivation in research/d12D5/README.md, same as squad165/chart_search.c with q = 3):
     A-side pattern i1 i2 i3 i4 nonsingular iff {A_i2^-1 b_i1, A_i2^-1 b_i2, A_i3^-1 b_i3, A_i3^-1 b_i4} is a basis,
     B-side pattern nonsingular iff {A_i2 A_i1^-1 b_i1, b_i2, b_i3, A_i3 A_i4^-1 b_i4} is a basis (i1!=i2!=i3!=i4).
     Pencil (i != j): A: Z = {A_i A_k^-1 b_k : k!=i} u {b_l : l not in {i,j}} u {A_j A_k^-1 b_k : k!=j} mod <b_i,b_j>
                      B: Z = {A_i^-1 b_k : k!=i} u {c_l : l not in {i,j}} u {A_j^-1 b_k : k!=j} mod <c_i,c_j>,
                         c_l = A_l^-1 b_l;  Z must hit all 4 points of PG(1,3) = the 4 hyperplanes through the 2-space.
   Cost = singular patterns (of 216) + PW * pencil violations (of 24).
   usage: chart3 seconds seed [PW] [out]          (search; prints best; writes chart text file)
          chart3 -p chart.txt patterns.txt         (write the 216-line pattern table "side i1 i2 i3 i4 rank" + report)
   Chart text format: 4 lines of 16 entries (A_0..A_3 row-major), then 4 lines b_0..b_3 (entries 0,1,2).
   Vector encoding: v = x0 + 3 x1 + 9 x2 + 27 x3. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
#define NV 81
static int ADD[NV][NV], SMUL[3][NV], P3[4] = {1, 3, 9, 27};
static inline int coord(int v, int r) { return (v / P3[r]) % 3; }
typedef struct { int c[4]; } mat;            /* columns as vectors */
static inline int mv(const mat *M, int v) { int o = 0; for (int j = 0; j < 4; j++) o = ADD[o][SMUL[coord(v, j)][M->c[j]]]; return o; }
static int rank3(const int *v, int n) {
    int a[16]; memcpy(a, v, n * sizeof(int)); int r = 0;
    for (int col = 0; col < 4 && r < n; col++) {
        int p = -1; for (int i = r; i < n; i++) if (coord(a[i], col)) { p = i; break; }
        if (p < 0) continue;
        int t = a[p]; a[p] = a[r]; a[r] = t;
        if (coord(a[r], col) == 2) a[r] = SMUL[2][a[r]];
        for (int i = 0; i < n; i++) if (i != r && coord(a[i], col)) a[i] = ADD[a[i]][SMUL[3 - coord(a[i], col)][a[r]]];
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
        if (X[col][col] == 2) for (int c = 0; c < 8; c++) X[col][c] = (2 * X[col][c]) % 3;
        for (int r = 0; r < 4; r++) if (r != col && X[r][col]) { int f = X[r][col]; for (int c = 0; c < 8; c++) X[r][c] = (X[r][c] + 3 * 3 - f * X[col][c]) % 3; }
    }
    for (int c = 0; c < 4; c++) { int v = 0; for (int r = 0; r < 4; r++) v += X[r][4 + c] * P3[r]; R->c[c] = v; }
    return 1;
}
/* 2-spaces: id 0..129; span2[u][v] = id or -1; hyp[W][z] = index 0..3 of the hyperplane through W containing z, -1 if z in W */
static int span2[NV][NV], nsp = 0; static uint64_t spm[130][2]; static signed char hyp[130][NV];
static void setbit(uint64_t *m, int v) { m[v >> 6] |= 1ULL << (v & 63); }
static int getbit(const uint64_t *m, int v) { return (m[v >> 6] >> (v & 63)) & 1; }
static void init(void) {
    for (int u = 0; u < NV; u++) for (int v = 0; v < NV; v++) { int w = 0; for (int r = 0; r < 4; r++) w += ((coord(u, r) + coord(v, r)) % 3) * P3[r]; ADD[u][v] = w; }
    for (int l = 0; l < 3; l++) for (int v = 0; v < NV; v++) { int w = 0; for (int r = 0; r < 4; r++) w += ((l * coord(v, r)) % 3) * P3[r]; SMUL[l][v] = w; }
    for (int u = 0; u < NV; u++) for (int v = 0; v < NV; v++) {
        int pr[2] = {u, v}; if (rank3(pr, 2) < 2) { span2[u][v] = -1; continue; }
        uint64_t m[2] = {0, 0}; for (int a = 0; a < 3; a++) for (int b = 0; b < 3; b++) setbit(m, ADD[SMUL[a][u]][SMUL[b][v]]);
        int id = -1; for (int s = 0; s < nsp; s++) if (spm[s][0] == m[0] && spm[s][1] == m[1]) { id = s; break; }
        if (id < 0) { id = nsp++; spm[id][0] = m[0]; spm[id][1] = m[1]; }
        span2[u][v] = id;
    }
    if (nsp != 130) { fprintf(stderr, "expected 130 2-spaces, got %d\n", nsp); exit(1); }
    for (int s = 0; s < nsp; s++) {
        int nh = 0; uint64_t H[4][2]; int base[2] = {-1, -1};
        for (int v = 1; v < NV && base[1] < 0; v++) if (getbit(spm[s], v)) { if (base[0] < 0) base[0] = v; else { int pr[2] = {base[0], v}; if (rank3(pr, 2) == 2) base[1] = v; } }
        for (int z = 0; z < NV; z++) {
            if (getbit(spm[s], z)) { hyp[s][z] = -1; continue; }
            int h = -1; for (int t = 0; t < nh; t++) if (getbit(H[t], z)) { h = t; break; }
            if (h < 0) { h = nh++; H[h][0] = H[h][1] = 0;
                for (int a = 0; a < 3; a++) for (int b = 0; b < 3; b++) for (int c = 0; c < 3; c++) setbit(H[h], ADD[ADD[SMUL[a][base[0]]][SMUL[b][base[1]]]][SMUL[c][z]]); }
            hyp[s][z] = h;
        }
        if (nh != 4) { fprintf(stderr, "expected 4 hyperplanes, got %d\n", nh); exit(1); }
    }
}
static mat A[4], Ai[4]; static int b[4];
static int singA[4][4][4][4], singB[4][4][4][4];
static int univ(void) {
    int bad = 0, v[4];
    for (int i1 = 0; i1 < 4; i1++) for (int i2 = 0; i2 < 4; i2++) if (i2 != i1) for (int i3 = 0; i3 < 4; i3++) if (i3 != i2)
    for (int i4 = 0; i4 < 4; i4++) if (i4 != i3) {
        v[0] = mv(&Ai[i2], b[i1]); v[1] = mv(&Ai[i2], b[i2]); v[2] = mv(&Ai[i3], b[i3]); v[3] = mv(&Ai[i3], b[i4]);
        singA[i1][i2][i3][i4] = rank3(v, 4); if (singA[i1][i2][i3][i4] < 4) bad++;
        v[0] = mv(&A[i2], mv(&Ai[i1], b[i1])); v[1] = b[i2]; v[2] = b[i3]; v[3] = mv(&A[i3], mv(&Ai[i4], b[i4]));
        singB[i1][i2][i3][i4] = rank3(v, 4); if (singB[i1][i2][i3][i4] < 4) bad++;
    }
    return bad;
}
static int pencil_ok(int w1, int w2, const int *z, int nz) {
    int s = span2[w1][w2]; if (s < 0) return 0;
    int seen = 0; for (int i = 0; i < nz; i++) { int h = hyp[s][z[i]]; if (h >= 0) seen |= 1 << h; }
    return seen == 15;
}
static int pencA[4][4], pencB[4][4];
static int pencil(void) {
    int bad = 0, z[8], c[4]; for (int l = 0; l < 4; l++) c[l] = mv(&Ai[l], b[l]);
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) if (i != j) {
        int n = 0;
        for (int k = 0; k < 4; k++) if (k != i) z[n++] = mv(&A[i], c[k]);
        for (int l = 0; l < 4; l++) if (l != i && l != j) z[n++] = b[l];
        for (int k = 0; k < 4; k++) if (k != j) z[n++] = mv(&A[j], c[k]);
        pencA[i][j] = pencil_ok(b[i], b[j], z, n); if (!pencA[i][j]) bad++;
        n = 0;
        for (int k = 0; k < 4; k++) if (k != i) z[n++] = mv(&Ai[i], b[k]);
        for (int l = 0; l < 4; l++) if (l != i && l != j) z[n++] = c[l];
        for (int k = 0; k < 4; k++) if (k != j) z[n++] = mv(&Ai[j], b[k]);
        pencB[i][j] = pencil_ok(c[i], c[j], z, n); if (!pencB[i][j]) bad++;
    }
    return bad;
}
static int PW = 3;
static int cost(void) { for (int i = 0; i < 4; i++) if (!inv_mat(&A[i], &Ai[i])) return 1 << 20; return univ() + PW * pencil(); }
static void rand_gl(mat *M) { mat R; do { for (int j = 0; j < 4; j++) M->c[j] = xr() % NV; } while (!inv_mat(M, &R)); }
static int rand_vec(void) { int v; do v = xr() % NV; while (!v); return v; }
static void write_chart(const char *fn, mat *MA, int *bb) {
    FILE *f = fopen(fn, "w");
    for (int i = 0; i < 4; i++) { for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) fprintf(f, "%d ", coord(MA[i].c[c], r)); fprintf(f, "\n"); }
    for (int i = 0; i < 4; i++) { for (int r = 0; r < 4; r++) fprintf(f, "%d ", coord(bb[i], r)); fprintf(f, "\n"); }
    fclose(f);
}
static void read_chart(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(2); }
    for (int i = 0; i < 4; i++) { int e[16]; for (int t = 0; t < 16; t++) if (fscanf(f, "%d", &e[t]) != 1) exit(3);
        for (int c = 0; c < 4; c++) { int v = 0; for (int r = 0; r < 4; r++) v += (e[4 * r + c] % 3) * P3[r]; A[i].c[c] = v; } }
    for (int i = 0; i < 4; i++) { int v = 0; for (int r = 0; r < 4; r++) { int x; if (fscanf(f, "%d", &x) != 1) exit(4); v += (x % 3) * P3[r]; } b[i] = v; }
    fclose(f);
}
int main(int argc, char **argv) {
    init();
    if (argc >= 4 && !strcmp(argv[1], "-p")) {
        read_chart(argv[2]); for (int i = 0; i < 4; i++) if (!inv_mat(&A[i], &Ai[i])) { printf("singular A_%d\n", i); return 5; }
        int u = univ(), p = pencil(); FILE *f = fopen(argv[3], "w");
        for (int i1 = 0; i1 < 4; i1++) for (int i2 = 0; i2 < 4; i2++) if (i2 != i1) for (int i3 = 0; i3 < 4; i3++) if (i3 != i2)
        for (int i4 = 0; i4 < 4; i4++) if (i4 != i3) fprintf(f, "A %d %d %d %d %d\nB %d %d %d %d %d\n", i1, i2, i3, i4, singA[i1][i2][i3][i4], i1, i2, i3, i4, singB[i1][i2][i3][i4]);
        fclose(f);
        printf("singular patterns %d, pencil violations %d\n", u, p);
        for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) if (i != j && (!pencA[i][j] || !pencB[i][j])) printf("  pencil fails: (%d,%d)%s%s\n", i, j, pencA[i][j] ? "" : " A", pencB[i][j] ? "" : " B");
        for (int i1 = 0; i1 < 4; i1++) for (int i2 = 0; i2 < 4; i2++) if (i2 != i1) for (int i3 = 0; i3 < 4; i3++) if (i3 != i2)
        for (int i4 = 0; i4 < 4; i4++) if (i4 != i3) { if (singA[i1][i2][i3][i4] < 4) printf("  singular A %d%d%d%d\n", i1, i2, i3, i4); if (singB[i1][i2][i3][i4] < 4) printf("  singular B %d%d%d%d\n", i1, i2, i3, i4); }
        return 0;
    }
    double secs = atof(argv[1]); rs ^= (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; if (argc > 3) PW = atoi(argv[3]);
    const char *out = argc > 4 ? argv[4] : NULL;
    clock_t t0 = clock(); int best = 1 << 30; long evals = 0, restarts = 0;
    mat bA[4]; int bb[4];
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs && best > 0) {
        restarts++;
        for (int j = 0; j < 4; j++) A[0].c[j] = P3[j];
        for (int i = 1; i < 4; i++) rand_gl(&A[i]);
        for (int i = 0; i < 4; i++) b[i] = rand_vec();
        int c = cost(), stall = 0;
        while (stall < 3000 && c > 0) {
            mat sA[4]; int sb[4]; memcpy(sA, A, sizeof A); memcpy(sb, b, sizeof b);
            if (xr() & 1) { int k = 1 + xr() % 3; int col = xr() % 4, row = xr() % 4;
                int v = A[k].c[col], old = coord(v, row), nw = (old + 1 + xr() % 2) % 3; A[k].c[col] = v + (nw - old) * P3[row]; }
            else b[xr() % 4] = rand_vec();
            int c2 = cost(); evals++;
            if (c2 <= c) { stall = (c2 < c) ? 0 : stall + 1; c = c2; }
            else { memcpy(A, sA, sizeof A); memcpy(b, sb, sizeof b); stall++; }
        }
        if (c < best) { best = c; memcpy(bA, A, sizeof A); memcpy(bb, b, sizeof b);
            for (int i = 0; i < 4; i++) inv_mat(&A[i], &Ai[i]);
            printf("best %d (univ %d, pencil %d) after %ld restarts %ld evals\n", c, univ(), pencil(), restarts, evals); fflush(stdout);
            if (out) write_chart(out, bA, bb); }
    }
    printf("final best %d restarts %ld evals %ld\n", best, restarts, evals);
    return 0;
}
