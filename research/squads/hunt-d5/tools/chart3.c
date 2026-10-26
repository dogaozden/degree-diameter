/* chart3: search for route charts over F_3^n (n = 4) with L letters (default 3), for bipartite route-chart lifts at
   (9,5) (hunt-d5 job; the q = 3 analogue of research/theorems/BEAT_16_5_SQUAD.md section 2).

   Lift of a properly L-edge-coloured cubic bipartite controller C: (u,x) ~ (v, M_c x + lam b_c), lam in F_3, for each
   edge uv of colour c (u on side A).  Conditions (all must hold for a "perfect" chart):
     A-universal: for c1!=c2!=c3!=c4 (consecutive distinct): M_c3 M_c2^-1 <b_c1,b_c2> + <b_c3,b_c4> = F_3^4
     B-universal: the same with (M_c, b_c) -> (M_c^-1, d_c = M_c^-1 b_c)
     A-pencil (i != j): Z = {M_i M_k^-1 b_k : k!=i} u {b_l : l not in {i,j}} u {M_j M_k^-1 b_k : k!=j} meets every
                        hyperplane class: its image in F_3^4/<b_i,b_j> hits all 4 points of PG(1,3)
     B-pencil: the same with (M_c^-1, d_c).
   Usage: chart3 seconds seed [L]   prints the best chart found (cost = number of failed conditions) as
          "M0 ... ; b ..." lines: each matrix row-major 16 digits, each vector 4 digits.
   Env: WPEN (weight of a pencil failure, default 1), WDIAG (unused). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define n 4
typedef struct { int a[n][n]; } mat;
typedef struct { int v[n]; } vec;
static int L = 3;
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static inline int md(int x) { x %= 3; return x < 0 ? x + 3 : x; }

static int rank_rows(int r[][n], int k) { /* rank of k row vectors */
    int a[8][n]; memcpy(a, r, sizeof(int) * n * k); int rk = 0;
    for (int col = 0; col < n && rk < k; col++) {
        int p = -1; for (int i = rk; i < k; i++) if (a[i][col]) { p = i; break; }
        if (p < 0) continue;
        for (int j = 0; j < n; j++) { int t = a[rk][j]; a[rk][j] = a[p][j]; a[p][j] = t; }
        int inv = a[rk][col] == 1 ? 1 : 2;
        for (int j = 0; j < n; j++) a[rk][j] = md(a[rk][j] * inv);
        for (int i = 0; i < k; i++) if (i != rk && a[i][col]) { int f = a[i][col]; for (int j = 0; j < n; j++) a[i][j] = md(a[i][j] - f * a[rk][j]); }
        rk++;
    }
    return rk;
}
static mat mmul(mat A, mat B) { mat C; for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) { int s = 0; for (int k = 0; k < n; k++) s += A.a[i][k] * B.a[k][j]; C.a[i][j] = md(s); } return C; }
static vec mvec(mat A, vec x) { vec y; for (int i = 0; i < n; i++) { int s = 0; for (int k = 0; k < n; k++) s += A.a[i][k] * x.v[k]; y.v[i] = md(s); } return y; }
static int minv(mat A, mat *R) {
    int a[n][2 * n]; for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) { a[i][j] = A.a[i][j]; a[i][n + j] = i == j; }
    for (int col = 0; col < n; col++) {
        int p = -1; for (int i = col; i < n; i++) if (a[i][col]) { p = i; break; }
        if (p < 0) return 0;
        for (int j = 0; j < 2 * n; j++) { int t = a[col][j]; a[col][j] = a[p][j]; a[p][j] = t; }
        int inv = a[col][col] == 1 ? 1 : 2;
        for (int j = 0; j < 2 * n; j++) a[col][j] = md(a[col][j] * inv);
        for (int i = 0; i < n; i++) if (i != col && a[i][col]) { int f = a[i][col]; for (int j = 0; j < 2 * n; j++) a[i][j] = md(a[i][j] - f * a[col][j]); }
    }
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) R->a[i][j] = a[i][n + j];
    return 1;
}
static int vzero(vec x) { for (int i = 0; i < n; i++) if (x.v[i]) return 0; return 1; }

static mat M[8], Mi[8]; static vec b[8], dvec[8];
static int wpen = 1;

/* universal on one side with letters (P_c, w_c): P_c3 P_c2^-1 <w_c1, w_c2> + <w_c3, w_c4> = F^4 */
static int side_univ(mat *P, mat *Pi, vec *w) {
    int bad = 0;
    for (int c2 = 0; c2 < L; c2++) for (int c3 = 0; c3 < L; c3++) {
        if (c3 == c2) continue;
        mat T = mmul(P[c3], Pi[c2]);
        for (int c1 = 0; c1 < L; c1++) { if (c1 == c2) continue;
            vec x1 = mvec(T, w[c1]), x2 = mvec(T, w[c2]);
            for (int c4 = 0; c4 < L; c4++) { if (c4 == c3) continue;
                int r[4][n]; memcpy(r[0], x1.v, sizeof x1.v); memcpy(r[1], x2.v, sizeof x2.v); memcpy(r[2], w[c3].v, sizeof x1.v); memcpy(r[3], w[c4].v, sizeof x1.v);
                if (rank_rows(r, 4) < 4) bad++;
            }
        }
    }
    return bad;
}
/* pencil on one side: Z(i,j) image in F^4/<w_i,w_j> hits all 4 points of PG(1,3) */
static int side_pencil(mat *P, mat *Pi, vec *w) {
    int bad = 0;
    for (int i = 0; i < L; i++) for (int j = 0; j < L; j++) {
        if (i == j) continue;
        vec Z[32]; int nz = 0;
        for (int k = 0; k < L; k++) if (k != i) Z[nz++] = mvec(mmul(P[i], Pi[k]), w[k]);
        for (int l = 0; l < L; l++) if (l != i && l != j) Z[nz++] = w[l];
        for (int k = 0; k < L; k++) if (k != j) Z[nz++] = mvec(mmul(P[j], Pi[k]), w[k]);
        /* quotient: the classes of z modulo W=<w_i,w_j>; two z's give the same projective point iff
           rank(w_i,w_j,z,z') == 3; a z in W gives nothing.  Need 4 distinct points. */
        int pts[32], np = 0;
        for (int a = 0; a < nz; a++) {
            int r[3][n]; memcpy(r[0], w[i].v, sizeof r[0]); memcpy(r[1], w[j].v, sizeof r[0]); memcpy(r[2], Z[a].v, sizeof r[0]);
            if (rank_rows(r, 3) < 3) continue;
            int dup = 0;
            for (int q = 0; q < np; q++) {
                int r4[4][n]; memcpy(r4[0], w[i].v, sizeof r[0]); memcpy(r4[1], w[j].v, sizeof r[0]); memcpy(r4[2], Z[a].v, sizeof r[0]); memcpy(r4[3], Z[pts[q]].v, sizeof r[0]);
                if (rank_rows(r4, 4) < 4) { dup = 1; break; }
            }
            if (!dup) pts[np++] = a;
        }
        if (np < 4) bad++;
    }
    return bad;
}
static int wb_indep(void) { /* b's pairwise independent, d's too */
    for (int i = 0; i < L; i++) for (int j = i + 1; j < L; j++) {
        int r[2][n]; memcpy(r[0], b[i].v, sizeof r[0]); memcpy(r[1], b[j].v, sizeof r[0]); if (rank_rows(r, 2) < 2) return 0;
        memcpy(r[0], dvec[i].v, sizeof r[0]); memcpy(r[1], dvec[j].v, sizeof r[0]); if (rank_rows(r, 2) < 2) return 0;
    }
    return 1;
}
static int costv(int *ua, int *ub, int *pa, int *pb) {
    for (int c = 0; c < L; c++) { if (!minv(M[c], &Mi[c])) return 1000; dvec[c] = mvec(Mi[c], b[c]); if (vzero(b[c])) return 1000; }
    if (!wb_indep()) return 500;
    *ua = side_univ(M, Mi, b); *ub = side_univ(Mi, M, dvec);
    *pa = side_pencil(M, Mi, b); *pb = side_pencil(Mi, M, dvec);
    return *ua + *ub + wpen * (*pa + *pb);
}
static void randmat(mat *A) { do { for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) A->a[i][j] = rnd() % 3; } while (!minv(*A, &Mi[7])); }
static void print_chart(FILE *f) {
    for (int c = 0; c < L; c++) {
        fprintf(f, "M%d ", c); for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) fprintf(f, "%d", M[c].a[i][j]);
        fprintf(f, " b%d ", c); for (int i = 0; i < n; i++) fprintf(f, "%d", b[c].v[i]); fprintf(f, "\n");
    }
}
int main(int argc, char **argv) {
    double secs = argc > 1 ? atof(argv[1]) : 10; rs ^= (argc > 2 ? strtoull(argv[2], 0, 10) : 1) * 0x9E3779B97F4A7C15ULL;
    if (argc > 3) L = atoi(argv[3]);
    if (getenv("WPEN")) wpen = atoi(getenv("WPEN"));
    for (int i = 0; i < 30; i++) rnd();
    double t0 = now(); int best = 1 << 30; long restarts = 0;
    mat bM[8]; vec bb[8];
    while (now() - t0 < secs && best > 0) {
        restarts++;
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) M[0].a[i][j] = i == j;
        for (int c = 1; c < L; c++) randmat(&M[c]);
        for (int c = 0; c < L; c++) do { for (int i = 0; i < n; i++) b[c].v[i] = rnd() % 3; } while (vzero(b[c]));
        int ua, ub, pa, pb, cur = costv(&ua, &ub, &pa, &pb);
        int stall = 0;
        while (stall < 3000 && now() - t0 < secs) {
            mat sM[8]; vec sb[8]; memcpy(sM, M, sizeof M); memcpy(sb, b, sizeof b);
            int c = rnd() % L;
            if (rnd() % 3 == 0) { int i = rnd() % n; b[c].v[i] = rnd() % 3; }
            else if (c > 0) { int i = rnd() % n, j = rnd() % n; M[c].a[i][j] = rnd() % 3; }
            else { int i = rnd() % n; b[0].v[i] = rnd() % 3; }
            int c2 = costv(&ua, &ub, &pa, &pb);
            if (c2 <= cur) { if (c2 < cur) stall = 0; else stall++; cur = c2; }
            else { memcpy(M, sM, sizeof M); memcpy(b, sb, sizeof b); stall++; }
            if (cur < best) { best = cur; memcpy(bM, M, sizeof M); memcpy(bb, b, sizeof b);
                costv(&ua, &ub, &pa, &pb);
                fprintf(stderr, "t=%.1f restart=%ld best=%d (univA %d univB %d penA %d penB %d)\n", now() - t0, restarts, best, ua, ub, pa, pb); }
            if (best == 0) break;
        }
    }
    memcpy(M, bM, sizeof M); memcpy(b, bb, sizeof b);
    int ua, ub, pa, pb; costv(&ua, &ub, &pa, &pb);
    printf("RESULT chart3 L=%d best=%d univA=%d univB=%d penA=%d penB=%d restarts=%ld\n", L, best, ua, ub, pa, pb, restarts);
    print_chart(stdout);
    return 0;
}
