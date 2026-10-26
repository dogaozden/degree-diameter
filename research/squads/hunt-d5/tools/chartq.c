/* chartq: route charts over F_q^4, q in {2,3,4,5}, with L = 3 letters (hunt-d5).  Generalizes chart3.c.
   Lift of a properly 3-edge-coloured cubic bipartite controller: (u,x) ~ (v, M_c x + lam b_c), lam in F_q; degree 3q.
   Conditions (cost = number failed):
     universal (both sides): every nonbacktracking colour pattern c1c2c3c4 (consecutive distinct) is nonsingular:
        A: M_c3 M_c2^-1 <b_c1,b_c2> + <b_c3,b_c4> = F^4;  B: the same with (M_c^-1, d_c = M_c^-1 b_c)
     pencil (both sides, i != j): Z(i,j) = {M_i M_k^-1 b_k: k!=i} u {b_l: l!={i,j}} u {M_j M_k^-1 b_k: k!=j} hits all
        q+1 points of PG(F^4/<b_i,b_j>)
     diag (env DIAG=1, both sides): the 9 planes <d_c,d_c'> (c<c') and <d_c, M_c^-1 b_c'> (c != c') cover F^4
        (then no 4-cycles are needed in the controller; possible only for q = 2).
   Usage: chartq q seconds seed   -> "RESULT ..." and lines "M<c> <16 digits> b<c> <4 digits>" (digits = field elements;
   GF(4) = {0,1,w,w+1} as 0,1,2,3 with w^2 = w+1). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#define n 4
#define L 3
static int q, ADD[8][8], MUL[8][8], NEG[8], INV[8];
static void field(void) {
    if (q == 4) {
        for (int a = 0; a < 4; a++) for (int b = 0; b < 4; b++) ADD[a][b] = a ^ b;
        /* elements as polynomials over F2: 2 = w, 3 = w+1, w^2 = w+1 */
        for (int a = 0; a < 4; a++) for (int b = 0; b < 4; b++) {
            int r = 0, x = a, y = b; /* poly mult mod w^2+w+1 */
            int p = 0; for (int i = 0; i < 2; i++) if ((y >> i) & 1) p ^= x << i;
            if (p & 4) p ^= 7; r = p; MUL[a][b] = r;
        }
    } else for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) { ADD[a][b] = (a + b) % q; MUL[a][b] = a * b % q; }
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) { if (ADD[a][b] == 0) NEG[a] = b; if (MUL[a][b] == 1) INV[a] = b; }
}
typedef struct { int a[n][n]; } mat;
typedef struct { int v[n]; } vec;
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static int rank_rows(int r[][n], int k) {
    int a[16][n]; memcpy(a, r, sizeof(int) * n * k); int rk = 0;
    for (int col = 0; col < n && rk < k; col++) {
        int p = -1; for (int i = rk; i < k; i++) if (a[i][col]) { p = i; break; }
        if (p < 0) continue;
        for (int j = 0; j < n; j++) { int t = a[rk][j]; a[rk][j] = a[p][j]; a[p][j] = t; }
        int iv = INV[a[rk][col]]; for (int j = 0; j < n; j++) a[rk][j] = MUL[a[rk][j]][iv];
        for (int i = 0; i < k; i++) if (i != rk && a[i][col]) { int f = a[i][col]; for (int j = 0; j < n; j++) a[i][j] = ADD[a[i][j]][NEG[MUL[f][a[rk][j]]]]; }
        rk++;
    }
    return rk;
}
static mat mmul(mat A, mat B) { mat C; for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) { int s = 0; for (int k = 0; k < n; k++) s = ADD[s][MUL[A.a[i][k]][B.a[k][j]]]; C.a[i][j] = s; } return C; }
static vec mvec(mat A, vec x) { vec y; for (int i = 0; i < n; i++) { int s = 0; for (int k = 0; k < n; k++) s = ADD[s][MUL[A.a[i][k]][x.v[k]]]; y.v[i] = s; } return y; }
static int minv(mat A, mat *R) {
    int a[n][2 * n]; for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) { a[i][j] = A.a[i][j]; a[i][n + j] = i == j; }
    for (int col = 0; col < n; col++) {
        int p = -1; for (int i = col; i < n; i++) if (a[i][col]) { p = i; break; }
        if (p < 0) return 0;
        for (int j = 0; j < 2 * n; j++) { int t = a[col][j]; a[col][j] = a[p][j]; a[p][j] = t; }
        int iv = INV[a[col][col]]; for (int j = 0; j < 2 * n; j++) a[col][j] = MUL[a[col][j]][iv];
        for (int i = 0; i < n; i++) if (i != col && a[i][col]) { int f = a[i][col]; for (int j = 0; j < 2 * n; j++) a[i][j] = ADD[a[i][j]][NEG[MUL[f][a[col][j]]]]; }
    }
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) R->a[i][j] = a[i][n + j];
    return 1;
}
static int vzero(vec x) { for (int i = 0; i < n; i++) if (x.v[i]) return 0; return 1; }
static mat M[L], Mi[L]; static vec b[L], dv[L]; static int DIAG = 0;
static int side_univ(mat *P, mat *Pi, vec *w) {
    int bad = 0;
    for (int c2 = 0; c2 < L; c2++) for (int c3 = 0; c3 < L; c3++) { if (c3 == c2) continue;
        mat T = mmul(P[c3], Pi[c2]);
        for (int c1 = 0; c1 < L; c1++) { if (c1 == c2) continue; vec x1 = mvec(T, w[c1]), x2 = mvec(T, w[c2]);
            for (int c4 = 0; c4 < L; c4++) { if (c4 == c3) continue;
                int r[4][n]; memcpy(r[0], x1.v, sizeof r[0]); memcpy(r[1], x2.v, sizeof r[0]); memcpy(r[2], w[c3].v, sizeof r[0]); memcpy(r[3], w[c4].v, sizeof r[0]);
                if (rank_rows(r, 4) < 4) bad++; } } }
    return bad;
}
static int side_pencil(mat *P, mat *Pi, vec *w) {
    int bad = 0;
    for (int i = 0; i < L; i++) for (int j = 0; j < L; j++) { if (i == j) continue;
        vec Z[16]; int nz = 0;
        for (int k = 0; k < L; k++) if (k != i) Z[nz++] = mvec(mmul(P[i], Pi[k]), w[k]);
        for (int l = 0; l < L; l++) if (l != i && l != j) Z[nz++] = w[l];
        for (int k = 0; k < L; k++) if (k != j) Z[nz++] = mvec(mmul(P[j], Pi[k]), w[k]);
        int pts[16], np = 0;
        for (int a = 0; a < nz; a++) {
            int r[3][n]; memcpy(r[0], w[i].v, sizeof r[0]); memcpy(r[1], w[j].v, sizeof r[0]); memcpy(r[2], Z[a].v, sizeof r[0]);
            if (rank_rows(r, 3) < 3) continue;
            int dup = 0;
            for (int t = 0; t < np && !dup; t++) { int r4[4][n]; memcpy(r4, r, sizeof r); memcpy(r4[3], Z[pts[t]].v, sizeof r[0]); if (rank_rows(r4, 4) < 4) dup = 1; }
            if (!dup) pts[np++] = a;
        }
        if (np < q + 1) bad++; }
    return bad;
}
/* diagonal: union of the 9 planes through 0 covers F^4 */
static int side_diag(mat *P, mat *Pi, vec *w) {
    vec d[L]; for (int c = 0; c < L; c++) d[c] = mvec(Pi[c], w[c]);
    vec pl[16][2]; int np = 0;
    for (int c = 0; c < L; c++) for (int c2 = c + 1; c2 < L; c2++) { pl[np][0] = d[c]; pl[np][1] = d[c2]; np++; }
    for (int c = 0; c < L; c++) for (int c2 = 0; c2 < L; c2++) if (c2 != c) { pl[np][0] = d[c]; pl[np][1] = mvec(Pi[c], w[c2]); np++; }
    int Q4 = q * q * q * q; char cov[625] = {0}; int ncov = 0;
    for (int p = 0; p < np; p++) for (int s = 0; s < q; s++) for (int t = 0; t < q; t++) {
        int idx = 0, mulq = 1;
        for (int i = 0; i < n; i++) { int v = ADD[MUL[s][pl[p][0].v[i]]][MUL[t][pl[p][1].v[i]]]; idx += v * mulq; mulq *= q; }
        if (!cov[idx]) { cov[idx] = 1; ncov++; }
    }
    return Q4 - ncov;
}
static int indep(void) {
    for (int i = 0; i < L; i++) for (int j = i + 1; j < L; j++) {
        int r[2][n]; memcpy(r[0], b[i].v, sizeof r[0]); memcpy(r[1], b[j].v, sizeof r[0]); if (rank_rows(r, 2) < 2) return 0;
        memcpy(r[0], dv[i].v, sizeof r[0]); memcpy(r[1], dv[j].v, sizeof r[0]); if (rank_rows(r, 2) < 2) return 0; }
    return 1;
}
static int parts[6];
static int costv(void) {
    for (int c = 0; c < L; c++) { if (!minv(M[c], &Mi[c])) return 10000; if (vzero(b[c])) return 10000; dv[c] = mvec(Mi[c], b[c]); }
    if (!indep()) return 5000;
    parts[0] = side_univ(M, Mi, b); parts[1] = side_univ(Mi, M, dv); parts[2] = side_pencil(M, Mi, b); parts[3] = side_pencil(Mi, M, dv);
    parts[4] = DIAG ? (side_diag(M, Mi, b) > 0) : 0; parts[5] = DIAG ? (side_diag(Mi, M, dv) > 0) : 0;
    return parts[0] + parts[1] + parts[2] + parts[3] + 3 * (parts[4] + parts[5]);
}
int main(int argc, char **argv) {
    q = atoi(argv[1]); double secs = atof(argv[2]); rs ^= strtoull(argv[3], 0, 10) * 0x9E3779B97F4A7C15ULL;
    DIAG = getenv("DIAG") ? atoi(getenv("DIAG")) : 0; field();
    for (int i = 0; i < 30; i++) rnd();
    double t0 = now(); int best = 1 << 30; mat bM[L]; vec bb[L]; long rest = 0;
    while (now() - t0 < secs && best > 0) {
        rest++;
        for (int c = 0; c < L; c++) { do { for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) M[c].a[i][j] = c == 0 ? (i == j) : (int)(rnd() % q); } while (!minv(M[c], &Mi[c]));
            do { for (int i = 0; i < n; i++) b[c].v[i] = rnd() % q; } while (vzero(b[c])); }
        int cur = costv(), stall = 0;
        while (stall < 4000 && now() - t0 < secs) {
            mat sM[L]; vec sb[L]; memcpy(sM, M, sizeof M); memcpy(sb, b, sizeof b);
            int c = rnd() % L;
            if (c == 0 || rnd() % 3 == 0) b[c].v[rnd() % n] = rnd() % q; else M[c].a[rnd() % n][rnd() % n] = rnd() % q;
            int c2 = costv();
            if (c2 <= cur) { stall = c2 < cur ? 0 : stall + 1; cur = c2; } else { memcpy(M, sM, sizeof M); memcpy(b, sb, sizeof b); stall++; }
            if (cur < best) { best = cur; memcpy(bM, M, sizeof M); memcpy(bb, b, sizeof b);
                fprintf(stderr, "t=%.1f best=%d (uA %d uB %d pA %d pB %d dA %d dB %d)\n", now() - t0, best, parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]); }
            if (best == 0) break;
        }
    }
    memcpy(M, bM, sizeof M); memcpy(b, bb, sizeof b); costv();
    printf("RESULT chartq q=%d best=%d uA=%d uB=%d pA=%d pB=%d dA=%d dB=%d restarts=%ld\n", q, best, parts[0], parts[1], parts[2], parts[3], parts[4], parts[5], rest);
    for (int c = 0; c < L; c++) { printf("M%d ", c); for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) printf("%d", M[c].a[i][j]);
        printf(" b%d ", c); for (int i = 0; i < n; i++) printf("%d", b[c].v[i]); printf("\n"); }
    return 0;
}
