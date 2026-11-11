/* chart2.c: route charts for Delta = 10 = 5 letters x 2 scalars over GF(2)^4 (job cell-10-5).

   Lift of a properly 5-edge-coloured 5-regular bipartite controller C: controller edge u (side A) -- v (side B)
   with letter t gives the lift edges (u, x) ~ (v, A_t x + lam b_t), lam in {0, 1}, x in GF(2)^4.  Degree 10.
   Moving B -> A along letter t: y -> A_t^-1 y + lam A_t^-1 b_t.

   A walk pattern is a sequence of letters with a start side.  Its reached set from x = 0 is computed by brute force
   over all lam in {0,1}^len (no formulas, so no sign/convention mistakes).  Conditions on a chart:
     - pattern (i1 i2 i3 i4), consecutive letters distinct (= a nonbacktracking controller walk): nonsingular iff the
       reached set is all 16 points;
     - pencil (side, i, j), i != j: u -> a -> v with letters i, j.  All walks of length <= 4 from u to v that exist in
       every such controller: (i j), (k k i j) for all k, (i l l j) for l != i, j, (i j k k) for all k.  Their linear
       parts agree, so "union of reached sets = everything" is a condition on the chart only;
     - diagonal (side): closed walks (i i), (k k l l), (i l l i) at u; union = everything.
   Score = number of nonsingular patterns (A side 320 + B side 320); pencil and diagonal failures are penalised.

   usage: chart2 search SECONDS SEED OUT     anneal a chart, write it to OUT
          chart2 show CHART                   print the analysis and the pattern table (lines "A i1 i2 i3 i4 r")
   Chart file: 5 lines "c0 c1 c2 c3 b": columns of A_t and b_t as integers 0..15 (bit r = row r).          */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

typedef struct { int c[4]; } mat;            /* columns */
static inline int mv(const mat *M, int x) { int y = 0; for (int r = 0; r < 4; r++) if (x >> r & 1) y ^= M->c[r]; return y; }
static int rank4(int *v, int nv) {           /* rank of nv vectors in GF(2)^4 */
    int basis[4] = {0}, r = 0;
    for (int i = 0; i < nv; i++) { int x = v[i];
        for (int b = 3; b >= 0; b--) if (x >> b & 1) { if (basis[b]) x ^= basis[b]; else { basis[b] = x; r++; break; } } }
    return r;
}
static int inverse(const mat *M, mat *I) {   /* brute force over images */
    int img[16]; for (int x = 0; x < 16; x++) img[x] = mv(M, x);
    int pre[16]; for (int x = 0; x < 16; x++) pre[x] = -1;
    for (int x = 0; x < 16; x++) { if (pre[img[x]] >= 0) return 0; pre[img[x]] = x; }
    for (int r = 0; r < 4; r++) I->c[r] = pre[1 << r];
    return 1;
}

static mat A[5], Ai[5]; static int B[5], Bi[5];      /* Bi[t] = A_t^-1 b_t */

/* one step from side s (0 = A, 1 = B) along letter t with scalar lam */
static inline int step(int x, int s, int t, int lam) {
    if (s == 0) return mv(&A[t], x) ^ (lam ? B[t] : 0);
    return mv(&Ai[t], x) ^ (lam ? Bi[t] : 0);
}
/* reached set (16-bit mask) from x0 of the walk with letters L[0..len-1] starting on side s */
static int reach(int x0, int s, const int *L, int len) {
    int mask = 0;
    for (int lm = 0; lm < (1 << len); lm++) { int x = x0, side = s;
        for (int i = 0; i < len; i++) { x = step(x, side, L[i], lm >> i & 1); side ^= 1; }
        mask |= 1 << x; }
    return mask;
}

static int nsA[5][5][5][5], nsB[5][5][5][5];
static int pencil_ok[2][5][5], diag_ok[2];
static int evaluate(int verbose) {
    int good = 0;
    for (int s = 0; s < 2; s++)
    for (int a = 0; a < 5; a++) for (int b = 0; b < 5; b++) for (int c = 0; c < 5; c++) for (int d = 0; d < 5; d++) {
        if (a == b || b == c || c == d) continue;
        int L[4] = {a, b, c, d}; int ok = reach(0, s, L, 4) == 0xFFFF;
        if (s == 0) nsA[a][b][c][d] = ok; else nsB[a][b][c][d] = ok;
        good += ok;
    }
    int pen = 0;
    for (int s = 0; s < 2; s++) for (int i = 0; i < 5; i++) for (int j = 0; j < 5; j++) { if (i == j) continue;
        int m = 0, L[4];
        L[0] = i; L[1] = j; m |= reach(0, s, L, 2);
        for (int k = 0; k < 5; k++) { L[0] = k; L[1] = k; L[2] = i; L[3] = j; m |= reach(0, s, L, 4);
                                      L[0] = i; L[1] = j; L[2] = k; L[3] = k; m |= reach(0, s, L, 4); }
        for (int l = 0; l < 5; l++) if (l != i && l != j) { L[0] = i; L[1] = l; L[2] = l; L[3] = j; m |= reach(0, s, L, 4); }
        pencil_ok[s][i][j] = (m == 0xFFFF); pen += (m != 0xFFFF);
    }
    int dg = 0;
    for (int s = 0; s < 2; s++) { int m = 0, L[4];
        for (int i = 0; i < 5; i++) { L[0] = i; L[1] = i; m |= reach(0, s, L, 2); }
        for (int k = 0; k < 5; k++) for (int l = 0; l < 5; l++) { L[0] = k; L[1] = k; L[2] = l; L[3] = l; m |= reach(0, s, L, 4);
            if (l != k) { L[0] = k; L[1] = l; L[2] = l; L[3] = k; m |= reach(0, s, L, 4); } }
        diag_ok[s] = (m == 0xFFFF); dg += (m != 0xFFFF);
        if (verbose) printf("diagonal side %c: %d of 16 points\n", "AB"[s], __builtin_popcount(m));
    }
    if (verbose) printf("nonsingular patterns %d of 640, pencil failures %d of 40, diagonal failures %d of 2\n", good, pen, dg);
    return good - 40 * pen - 200 * dg;
}

static int random_inv(mat *M) {
    for (;;) { for (int r = 0; r < 4; r++) M->c[r] = xr() % 16; int v[4] = {M->c[0], M->c[1], M->c[2], M->c[3]}; if (rank4(v, 4) == 4) return 1; }
}
static void fix(void) { for (int t = 0; t < 5; t++) { inverse(&A[t], &Ai[t]); Bi[t] = mv(&Ai[t], B[t]); } }

static void save(const char *fn) {
    FILE *f = fopen(fn, "w");
    for (int t = 0; t < 5; t++) fprintf(f, "%d %d %d %d %d\n", A[t].c[0], A[t].c[1], A[t].c[2], A[t].c[3], B[t]);
    fclose(f);
}
static void load(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { printf("cannot open %s\n", fn); exit(1); }
    for (int t = 0; t < 5; t++) if (fscanf(f, "%d %d %d %d %d", &A[t].c[0], &A[t].c[1], &A[t].c[2], &A[t].c[3], &B[t]) != 5) { printf("bad chart\n"); exit(1); }
    fclose(f); fix();
}

int main(int argc, char **argv) {
    if (argc >= 3 && !strcmp(argv[1], "show")) {
        load(argv[2]); evaluate(1);
        for (int s = 0; s < 2; s++) for (int i = 0; i < 5; i++) for (int j = 0; j < 5; j++) if (i != j && !pencil_ok[s][i][j]) printf("pencil fails: side %c i=%d j=%d\n", "AB"[s], i, j);
        int cntA = 0, cntB = 0;
        for (int a = 0; a < 5; a++) for (int b = 0; b < 5; b++) for (int c = 0; c < 5; c++) for (int d = 0; d < 5; d++) {
            if (a == b || b == c || c == d) continue; cntA += nsA[a][b][c][d]; cntB += nsB[a][b][c][d]; }
        printf("A side nonsingular %d of 320, B side %d of 320\n", cntA, cntB);
        if (argc >= 4) { FILE *f = fopen(argv[3], "w");
            for (int s = 0; s < 2; s++)
            for (int a = 0; a < 5; a++) for (int b = 0; b < 5; b++) for (int c = 0; c < 5; c++) for (int d = 0; d < 5; d++) {
                if (a == b || b == c || c == d) continue;
                fprintf(f, "%c %d %d %d %d %d\n", "AB"[s], a, b, c, d, s ? nsB[a][b][c][d] : nsA[a][b][c][d]); }
            fclose(f); }
        return 0;
    }
    if (argc < 5 || strcmp(argv[1], "search")) { printf("usage: chart2 search SECONDS SEED OUT | chart2 show CHART [PATTERNS]\n"); return 1; }
    double secs = atof(argv[2]); rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    for (int t = 0; t < 5; t++) { random_inv(&A[t]); B[t] = 1 + xr() % 15; }
    fix(); int sc = evaluate(0), best = sc; mat bA[5]; int bB[5]; memcpy(bA, A, sizeof A); memcpy(bB, B, sizeof B);
    clock_t t0 = clock(); long it = 0; double T0 = 3.0;
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
        it++; double fr = (double)(clock() - t0) / CLOCKS_PER_SEC / secs, TT = T0 * pow(0.01, fr);
        mat sA[5]; int sB[5]; memcpy(sA, A, sizeof A); memcpy(sB, B, sizeof B);
        int t = xr() % 5, kind = xr() % 3;
        if (kind == 0) B[t] = 1 + xr() % 15;
        else if (kind == 1) random_inv(&A[t]);
        else { int r = xr() % 4; A[t].c[r] ^= 1 << (xr() % 4); int v[4] = {A[t].c[0], A[t].c[1], A[t].c[2], A[t].c[3]}; if (rank4(v, 4) < 4) { memcpy(A, sA, sizeof A); continue; } }
        fix(); int s2 = evaluate(0);
        if (s2 >= sc || exp((s2 - sc) / TT) > (double)(xr() % 1000000) / 1e6) { sc = s2; if (sc > best) { best = sc; memcpy(bA, A, sizeof A); memcpy(bB, B, sizeof B); } }
        else { memcpy(A, sA, sizeof A); memcpy(B, sB, sizeof B); fix(); }
    }
    memcpy(A, bA, sizeof A); memcpy(B, bB, sizeof B); fix();
    printf("best score %d after %ld steps\n", best, it); evaluate(1); save(argv[4]);
    return 0;
}
