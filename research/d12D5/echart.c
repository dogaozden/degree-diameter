/* Per-edge route charts over F_3^4 for the bipartite controller lift at (12,5) (cell-12-5, resumed session).
   A colour chart gives the 4 letters (A_c, b_c) to the 4 colours; universal3.py proves no colour chart over F_3 has
   all 216 patterns nonsingular.  Here every BASE edge e gets its own letter (A_e, b_e); a controller edge inherits
   the letter of the base edge it lies over, so a controller walk is singular iff its projection to the base is.
   Lift: (a, x)_A ~ (b, A_e x + lam b_e)_B, lam in F_3.  Conditions (derivation in research/d12D5/EDGECHART.md):
     A-side NB walk e1 e2 e3 e4 (middle A-vertex y = EA[e2] = EA[e3]):
        nonsingular iff {A_e2^-1 b_e1, A_e2^-1 b_e2, A_e3^-1 b_e3, A_e3^-1 b_e4} is a basis;
     B-side NB walk (middle B-vertex w): {A_e2 A_e1^-1 b_e1, b_e2, b_e3, A_e3 A_e4^-1 b_e4} is a basis;
     pencil, A-side pair through B-vertex a, edges e != f at a, u = EA[e], v = EA[f]:
        Z = {A_e A_k^-1 b_k : k != e at u} u {b_l : l at a, l != e, f} u {A_f A_k^-1 b_k : k != f at v}
        must meet all 4 hyperplanes through <b_e, b_f>;
     pencil, B-side pair through A-vertex a: Z = {A_e^-1 b_k : k != e at u} u {c_l : l at a, l != e, f}
        u {A_f^-1 b_k : k != f at v} against <c_e, c_f>, c_l = A_l^-1 b_l.
   Cost = singular NB walks + PW * pencil failures.
   usage: echart BASE seconds seed [PW] [out]      (anneal; out gets one line per base edge: 16 entries of A_e
                                                     row-major, then the 4 entries of b_e)
          echart BASE -p chart patterns            (write the pattern file: "S side e1 e2 e3 e4" per singular walk,
                                                     "P side e f" per pencil failure, then a summary line) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int k, ne, EA[64], EB[64];
int atA[32][4], atB[32][4];                 /* edges at each A-vertex / B-vertex */
typedef struct { int m[4][4]; } M4;
M4 A[64], Ai[64]; int b[64][4];
static void mv(const M4 *M, const int *x, int *y) { for (int r = 0; r < 4; r++) { int s = 0; for (int c = 0; c < 4; c++) s += M->m[r][c] * x[c]; y[r] = s % 3; } }
static int inv(const M4 *M, M4 *R) {
    int X[4][8];
    for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) { X[r][c] = M->m[r][c]; X[r][4 + c] = (r == c); }
    for (int col = 0; col < 4; col++) {
        int p = -1; for (int r = col; r < 4; r++) if (X[r][col]) { p = r; break; }
        if (p < 0) return 0;
        for (int c = 0; c < 8; c++) { int t = X[p][c]; X[p][c] = X[col][c]; X[col][c] = t; }
        if (X[col][col] == 2) for (int c = 0; c < 8; c++) X[col][c] = (2 * X[col][c]) % 3;
        for (int r = 0; r < 4; r++) if (r != col && X[r][col]) { int f = X[r][col]; for (int c = 0; c < 8; c++) X[r][c] = (X[r][c] + 9 - f * X[col][c]) % 3; }
    }
    for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) R->m[r][c] = X[r][4 + c];
    return 1;
}
static int rank(int v[][4], int n) {
    int a[16][4]; memcpy(a, v, n * sizeof(a[0])); int r = 0;
    for (int col = 0; col < 4 && r < n; col++) {
        int p = -1; for (int i = r; i < n; i++) if (a[i][col]) { p = i; break; }
        if (p < 0) continue;
        for (int c = 0; c < 4; c++) { int t = a[p][c]; a[p][c] = a[r][c]; a[r][c] = t; }
        if (a[r][col] == 2) for (int c = 0; c < 4; c++) a[r][c] = (2 * a[r][c]) % 3;
        for (int i = 0; i < n; i++) if (i != r && a[i][col]) { int f = a[i][col]; for (int c = 0; c < 4; c++) a[i][c] = (a[i][c] + 9 - f * a[r][c]) % 3; }
        r++;
    }
    return r;
}
/* hyperplanes of F_3^4: 40 normal vectors (first nonzero entry 1) */
int HN[40][4]; int nh = 0;
static int dot(const int *h, const int *x) { return (h[0] * x[0] + h[1] * x[1] + h[2] * x[2] + h[3] * x[3]) % 3; }
/* pencil: Z (nz vectors) must meet every hyperplane through <p, q>; returns 1 if OK */
static int pencil_ok(int p[4], int q[4], int Z[][4], int nz) {
    int two[2][4]; memcpy(two[0], p, sizeof two[0]); memcpy(two[1], q, sizeof two[1]);
    if (rank(two, 2) < 2) return 0;
    for (int h = 0; h < nh; h++) {
        if (dot(HN[h], p) || dot(HN[h], q)) continue;
        int hit = 0; for (int i = 0; i < nz; i++) if (!dot(HN[h], Z[i])) { int t[3][4]; memcpy(t[0], p, 16); memcpy(t[1], q, 16); memcpy(t[2], Z[i], 16); if (rank(t, 3) == 3) { hit = 1; break; } }
        if (!hit) return 0;
    }
    return 1;
}
FILE *pf = NULL; int PW = 4, DW = 0, ndm = 0;
static int plane_cover(int P[][4], int Q[][4], int np) {
    static unsigned char hit[81]; memset(hit, 0, 81); int cnt = 0;
    for (int i = 0; i < np; i++) for (int a = 0; a < 3; a++) for (int c = 0; c < 3; c++) {
        int v = 0, mlt = 1; for (int r = 0; r < 4; r++) { v += ((a * P[i][r] + c * Q[i][r]) % 3) * mlt; mlt *= 3; }
        if (!hit[v]) { hit[v] = 1; cnt++; } }
    return cnt;   /* 81 = complete */
}
static int cost(int *nsing, int *npen) {
    int s = 0, p = 0, v[4][4], t[4];
    for (int y = 0; y < k; y++) for (int i2 = 0; i2 < 4; i2++) for (int i3 = 0; i3 < 4; i3++) if (i2 != i3) {
        int e2 = atA[y][i2], e3 = atA[y][i3], w1 = EB[e2], w2 = EB[e3];
        for (int j1 = 0; j1 < 4; j1++) { int e1 = atB[w1][j1]; if (e1 == e2) continue;
            for (int j4 = 0; j4 < 4; j4++) { int e4 = atB[w2][j4]; if (e4 == e3) continue;
                mv(&Ai[e2], b[e1], v[0]); mv(&Ai[e2], b[e2], v[1]); mv(&Ai[e3], b[e3], v[2]); mv(&Ai[e3], b[e4], v[3]);
                if (rank(v, 4) < 4) { s++; if (pf) fprintf(pf, "S A %d %d %d %d\n", e1, e2, e3, e4); } } }
    }
    for (int w = 0; w < k; w++) for (int i2 = 0; i2 < 4; i2++) for (int i3 = 0; i3 < 4; i3++) if (i2 != i3) {
        int e2 = atB[w][i2], e3 = atB[w][i3], y1 = EA[e2], y2 = EA[e3];
        for (int j1 = 0; j1 < 4; j1++) { int e1 = atA[y1][j1]; if (e1 == e2) continue;
            for (int j4 = 0; j4 < 4; j4++) { int e4 = atA[y2][j4]; if (e4 == e3) continue;
                mv(&Ai[e1], b[e1], t); mv(&A[e2], t, v[0]); memcpy(v[1], b[e2], 16); memcpy(v[2], b[e3], 16);
                mv(&Ai[e4], b[e4], t); mv(&A[e3], t, v[3]);
                if (rank(v, 4) < 4) { s++; if (pf) fprintf(pf, "S B %d %d %d %d\n", e1, e2, e3, e4); } } }
    }
    /* pencils: A-side pairs through B-vertex a */
    for (int a = 0; a < k; a++) for (int i = 0; i < 4; i++) for (int j = i + 1; j < 4; j++) {
        int e = atB[a][i], f = atB[a][j], u = EA[e], vv = EA[f], Z[16][4], nz = 0;
        for (int x = 0; x < 4; x++) { int kk = atA[u][x]; if (kk == e) continue; mv(&Ai[kk], b[kk], t); mv(&A[e], t, Z[nz++]); }
        for (int x = 0; x < 4; x++) { int l = atB[a][x]; if (l == e || l == f) continue; memcpy(Z[nz++], b[l], 16); }
        for (int x = 0; x < 4; x++) { int kk = atA[vv][x]; if (kk == f) continue; mv(&Ai[kk], b[kk], t); mv(&A[f], t, Z[nz++]); }
        if (!pencil_ok(b[e], b[f], Z, nz)) { p++; if (pf) fprintf(pf, "P A %d %d\n", e, f); }
    }
    for (int a = 0; a < k; a++) for (int i = 0; i < 4; i++) for (int j = i + 1; j < 4; j++) {
        int e = atA[a][i], f = atA[a][j], u = EB[e], vv = EB[f], Z[16][4], nz = 0, ce[4], cf[4];
        for (int x = 0; x < 4; x++) { int kk = atB[u][x]; if (kk == e) continue; mv(&Ai[e], b[kk], Z[nz++]); }
        for (int x = 0; x < 4; x++) { int l = atA[a][x]; if (l == e || l == f) continue; mv(&Ai[l], b[l], Z[nz++]); }
        for (int x = 0; x < 4; x++) { int kk = atB[vv][x]; if (kk == f) continue; mv(&Ai[f], b[kk], Z[nz++]); }
        mv(&Ai[e], b[e], ce); mv(&Ai[f], b[f], cf);
        if (!pencil_ok(ce, cf, Z, nz)) { p++; if (pf) fprintf(pf, "P B %d %d\n", e, f); }
    }
    int dmiss = 0;
    for (int y = 0; y < k; y++) { int P[64][4], Q[64][4], np = 0, c1[4];
        for (int x = 0; x < 4; x++) { int e = atA[y][x]; mv(&Ai[e], b[e], c1);
            for (int x2 = x + 1; x2 < 4; x2++) { memcpy(P[np], c1, 16); mv(&Ai[atA[y][x2]], b[atA[y][x2]], Q[np++]); }
            for (int t2 = 0; t2 < 4; t2++) { int l = atB[EB[e]][t2]; if (l != e) { memcpy(P[np], c1, 16); mv(&Ai[e], b[l], Q[np++]); } } }
        int cv = plane_cover(P, Q, np); dmiss += 81 - cv; if (pf && cv < 81) fprintf(pf, "D A %d %d\n", y, cv); }
    for (int w = 0; w < k; w++) { int P[64][4], Q[64][4], np = 0, c1[4];
        for (int x = 0; x < 4; x++) { int e = atB[w][x];
            for (int x2 = x + 1; x2 < 4; x2++) { memcpy(P[np], b[e], 16); memcpy(Q[np++], b[atB[w][x2]], 16); }
            for (int t2 = 0; t2 < 4; t2++) { int l = atA[EA[e]][t2]; if (l != e) { memcpy(P[np], b[e], 16); mv(&Ai[l], b[l], c1); mv(&A[e], c1, Q[np++]); } } }
        int cv = plane_cover(P, Q, np); dmiss += 81 - cv; if (pf && cv < 81) fprintf(pf, "D B %d %d\n", w, cv); }
    ndm = dmiss;
    *nsing = s; *npen = p; return s + PW * p + DW * dmiss;
}
static void rand_mat(M4 *M, M4 *Mi) { do { for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) M->m[r][c] = xr() % 3; } while (!inv(M, Mi)); }
static void rand_vec(int *x) { do { for (int r = 0; r < 4; r++) x[r] = xr() % 3; } while (!x[0] && !x[1] && !x[2] && !x[3]); }
static void write_chart(const char *fn) {
    FILE *f = fopen(fn, "w");
    for (int e = 0; e < ne; e++) { for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) fprintf(f, "%d ", A[e].m[r][c]); fprintf(f, "%d %d %d %d\n", b[e][0], b[e][1], b[e][2], b[e][3]); }
    fclose(f);
}
static int read_chart(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) return 0;
    for (int e = 0; e < ne; e++) { for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) if (fscanf(f, "%d", &A[e].m[r][c]) != 1) return 0;
        for (int r = 0; r < 4; r++) if (fscanf(f, "%d", &b[e][r]) != 1) return 0; if (!inv(&A[e], &Ai[e])) return 0; }
    fclose(f); return 1;
}
int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: echart BASE secs seed [PW] [out] | echart BASE -p chart patterns\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d", &k) != 1) return 2;
    ne = 4 * k; int dA[32] = {0}, dB[32] = {0};
    for (int i = 0; i < ne; i++) { if (fscanf(f, "%d %d", &EA[i], &EB[i]) != 2) return 3; atA[EA[i]][dA[EA[i]]++] = i; atB[EB[i]][dB[EB[i]]++] = i; }
    fclose(f);
    for (int x = 0; x < 81; x++) { int h[4] = {x % 3, x / 3 % 3, x / 9 % 3, x / 27}; int fnz = -1; for (int r = 0; r < 4; r++) if (h[r]) { fnz = r; break; }
        if (fnz >= 0 && h[fnz] == 1) memcpy(HN[nh++], h, 16); }
    if (!strcmp(argv[2], "-p")) {
        if (!read_chart(argv[3])) { fprintf(stderr, "bad chart\n"); return 4; }
        pf = fopen(argv[4], "w"); int s, p; cost(&s, &p);
        fprintf(pf, "# singular %d pencil_fail %d\n", s, p); fclose(pf);
        printf("singular %d of %d, pencil failures %d of %d, diag missing points %d\n", s, 2 * k * 108, p, 12 * k, ndm); return 0;
    }
    double secs = atof(argv[2]); rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) xr();
    if (argc > 4) PW = atoi(argv[4]); if (getenv("DW")) DW = atoi(getenv("DW")); const char *out = argc > 5 ? argv[5] : NULL;
    const char *init = getenv("INIT"); if (!(init && read_chart(init))) for (int e = 0; e < ne; e++) { rand_mat(&A[e], &Ai[e]); rand_vec(b[e]); }
    int s, p, c = cost(&s, &p), best = c; M4 bA[64]; int bb[64][4]; memcpy(bA, A, sizeof A); memcpy(bb, b, sizeof b);
    double T = 2.0, t0 = clock(); long it = 0;
    while (1) {
        if ((it & 255) == 0) { double el = (clock() - t0) / CLOCKS_PER_SEC; if (el > secs || best == 0) break; T = 2.0 * (1 - el / secs) + 0.05; }
        it++;
        int e = xr() % ne; M4 sA = A[e], sAi = Ai[e]; int sb[4]; memcpy(sb, b[e], 16);
        if (xr() % 5 == 0) { do { b[e][xr() % 4] = xr() % 3; } while (!b[e][0] && !b[e][1] && !b[e][2] && !b[e][3]); }
        else { int r = xr() % 4, cc = xr() % 4; A[e].m[r][cc] = (A[e].m[r][cc] + 1 + xr() % 2) % 3; if (!inv(&A[e], &Ai[e])) { A[e] = sA; continue; } }
        int s2, p2, c2 = cost(&s2, &p2);
        if (c2 <= c || exp((c - c2) / T) > (xr() % 1000000) / 1e6) { c = c2; s = s2; p = p2;
            if (c < best) { best = c; memcpy(bA, A, sizeof A); memcpy(bb, b, sizeof b); printf("it %ld cost %d (sing %d pen %d diagmiss %d)\n", it, c, s, p, ndm); fflush(stdout); } }
        else { A[e] = sA; Ai[e] = sAi; memcpy(b[e], sb, 16); }
    }
    memcpy(A, bA, sizeof A); memcpy(b, bb, sizeof b); for (int e = 0; e < ne; e++) inv(&A[e], &Ai[e]);
    int cc = cost(&s, &p); printf("best_cost %d singular %d pencil_fail %d diagmiss %d iters %ld\n", cc, s, p, ndm, it);
    if (out) write_chart(out);
    return 0;
}
