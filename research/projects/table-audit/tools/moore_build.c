/* moore_build.c (table-audit): incidence graphs of PG(2,q), W(q) and the split Cayley hexagon H(q), any prime power
   q <= 16, written independently of research/p4/d6/hexgen.c (which handles odd q only).
   GF(q): q prime -> integers mod q; q = p^e -> polynomials mod a fixed irreducible (4: x^2+x+1, 8: x^3+x+1,
   9: x^2+1, 16: x^4+x+1), element index = coefficient vector in base p.
   PG(2,q): point x on line l iff x.l = 0.
   W(q): points of PG(3,q); lines are the totally isotropic lines of w(x,y) = x0y1-x1y0+x2y3-x3y2 (the lines through x
     inside the plane x^perp).
   H(q): points of Q(6,q): X0X4+X1X5+X2X6 = X3^2; the hexagon lines through x are the lines through x in the plane
     {y : Tits' six equations p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31 hold and B(x,y)=0}
     (p_ij = x_i y_j - x_j y_i, B the polar form of the quadric), van Maldeghem, Generalized Polygons, 2.4.13.
   Every line is recorded once, from its smallest point. The program checks: every line has q+1 points, every point
   is on q+1 lines, #lines = #points, and every plane point found is on the quadric (H) / isotropic (W).
   Output: edge list "n" then "u v" per edge, points 0..N-1, lines N..2N-1.
   Usage: moore_build pg|w|h q OUT [COORDS]   (COORDS: one line per point: index and its normalized coordinates) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int q, p, e, ADD[16][16], MUL[16][16], NEG[16], INV[16];
static void field(void) {
    int poly = 0; /* irreducible: coefficients of x^0..x^{e-1} of x^e (i.e. x^e = -poly) */
    p = q; e = 1;
    for (int t = 2; t <= q; t++) if (q % t == 0) { p = t; break; }
    for (int r = p; r < q; r *= p) e++;
    int red[4] = {0};               /* x^e = sum red[i] x^i  */
    if (q == 4) { red[0] = 1; red[1] = 1; }          /* x^2 = x + 1 */
    else if (q == 8) { red[0] = 1; red[1] = 1; }     /* x^3 = x + 1 */
    else if (q == 9) { red[0] = 2; }                 /* x^2 = -1 = 2 */
    else if (q == 16) { red[0] = 1; red[1] = 1; }    /* x^4 = x + 1 */
    else if (e > 1) { fprintf(stderr, "unsupported q\n"); exit(1); }
    (void)poly;
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) {
        int ca[4] = {0}, cb[4] = {0}, s = 0, m = 1;
        for (int i = 0, x = a, y = b; i < e; i++, x /= p, y /= p) { ca[i] = x % p; cb[i] = y % p; }
        for (int i = 0; i < e; i++) { s += ((ca[i] + cb[i]) % p) * m; m *= p; }
        ADD[a][b] = s;
        int pr[8] = {0};
        for (int i = 0; i < e; i++) for (int j = 0; j < e; j++) pr[i + j] = (pr[i + j] + ca[i] * cb[j]) % p;
        for (int k = 2 * e - 2; k >= e; k--) { int c = pr[k]; pr[k] = 0; for (int i = 0; i < e; i++) pr[k - e + i] = (pr[k - e + i] + c * red[i]) % p; }
        s = 0; m = 1; for (int i = 0; i < e; i++) { s += pr[i] * m; m *= p; }
        MUL[a][b] = s;
    }
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) { if (ADD[a][b] == 0) NEG[a] = b; if (MUL[a][b] == 1) INV[a] = b; }
    /* field axioms spot check: every nonzero has an inverse, distributivity */
    for (int a = 1; a < q; a++) if (MUL[a][INV[a]] != 1) { fprintf(stderr, "not a field\n"); exit(1); }
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) for (int c = 0; c < q; c++)
        if (MUL[a][ADD[b][c]] != ADD[MUL[a][b]][MUL[a][c]] || MUL[a][MUL[b][c]] != MUL[MUL[a][b]][c]) { fprintf(stderr, "not a field\n"); exit(1); }
}
#define AD(a, b) ADD[a][b]
#define MU(a, b) MUL[a][b]
#define SB(a, b) ADD[a][NEG[b]]

static int dim;
static int64_t code(const int *v) { int64_t c = 0; for (int i = dim - 1; i >= 0; i--) c = c * q + v[i]; return c; }
static void normalize(int *v) { for (int i = 0; i < dim; i++) if (v[i]) { int s = INV[v[i]]; for (int j = 0; j < dim; j++) v[j] = MU(s, v[j]); return; } }
static int64_t *codes; static int N;
static int lookup(int *v) {
    normalize(v); int64_t c = code(v); int lo = 0, hi = N - 1;
    while (lo <= hi) { int m = (lo + hi) / 2; if (codes[m] == c) return m; if (codes[m] < c) lo = m + 1; else hi = m - 1; }
    return -1;
}
static int cmp64(const void *a, const void *b) { int64_t x = *(const int64_t *)a, y = *(const int64_t *)b; return x < y ? -1 : x > y; }
static int cmpi(const void *a, const void *b) { return *(const int *)a - *(const int *)b; }

static int Qform(const int *x) { /* X0X4+X1X5+X2X6-X3^2 */
    return SB(AD(AD(MU(x[0], x[4]), MU(x[1], x[5])), MU(x[2], x[6])), MU(x[3], x[3]));
}
/* nullspace of a (r x dim) matrix over GF(q); returns basis count, basis in B[k][dim] */
static int nullspace(int r, int A[][7], int B[][7]) {
    int M[8][7], piv[7], pc = 0, row = 0; memcpy(M, A, sizeof(int) * 7 * r);
    int isp[7] = {0};
    for (int c = 0; c < dim && row < r; c++) {
        int k = -1; for (int i = row; i < r; i++) if (M[i][c]) { k = i; break; }
        if (k < 0) continue;
        for (int j = 0; j < dim; j++) { int t = M[row][j]; M[row][j] = M[k][j]; M[k][j] = t; }
        int s = INV[M[row][c]]; for (int j = 0; j < dim; j++) M[row][j] = MU(s, M[row][j]);
        for (int i = 0; i < r; i++) if (i != row && M[i][c]) { int f = M[i][c]; for (int j = 0; j < dim; j++) M[i][j] = SB(M[i][j], MU(f, M[row][j])); }
        piv[row] = c; isp[c] = 1; row++; pc++;
    }
    int nb = 0;
    for (int c = 0; c < dim; c++) if (!isp[c]) {
        for (int j = 0; j < dim; j++) B[nb][j] = 0; B[nb][c] = 1;
        for (int i = 0; i < row; i++) B[nb][piv[i]] = NEG[M[i][c]];
        nb++;
    }
    return nb;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: moore_build pg|w|h q OUT\n"); return 2; }
    char kind = argv[1][0]; q = atoi(argv[2]); field();
    dim = kind == 'p' ? 3 : kind == 'w' ? 4 : 7;
    /* enumerate points */
    int64_t tot = 1; for (int i = 0; i < dim; i++) tot *= q;
    codes = malloc(sizeof(int64_t) * (tot / (q - 1) + 2)); N = 0;
    int v[7];
    for (int64_t c = 1; c < tot; c++) {
        int64_t t = c; for (int i = 0; i < dim; i++) { v[i] = t % q; t /= q; }
        int f = 0; for (int i = 0; i < dim; i++) if (v[i]) { f = v[i]; break; }
        if (f != 1) continue;
        if (kind == 'h' && Qform(v)) continue;
        codes[N++] = c;
    }
    qsort(codes, N, sizeof(int64_t), cmp64);
    int k1 = q + 1;
    int *lines = malloc(sizeof(int) * (size_t)N * k1 * 2); long L = 0;
    int *onl = calloc(N, sizeof(int));
    if (kind == 'p') {
        /* lines indexed by the same normalized vectors */
        for (int l = 0; l < N; l++) {
            int lv[7], cnt = 0; int64_t t = codes[l]; for (int i = 0; i < 3; i++) { lv[i] = t % q; t /= q; }
            for (int x = 0; x < N; x++) {
                int xv[7]; int64_t s = codes[x]; for (int i = 0; i < 3; i++) { xv[i] = s % q; s /= q; }
                if (AD(AD(MU(xv[0], lv[0]), MU(xv[1], lv[1])), MU(xv[2], lv[2])) == 0) { if (cnt >= k1) { fprintf(stderr, "bad line\n"); return 1; } lines[L * k1 + cnt++] = x; }
            }
            if (cnt != k1) { fprintf(stderr, "bad line size %d\n", cnt); return 1; }
            L++;
        }
    } else {
        for (int x = 0; x < N; x++) {
            int xv[7]; int64_t s = codes[x]; for (int i = 0; i < dim; i++) { xv[i] = s % q; s /= q; }
            int A[8][7], r = 0;
            if (kind == 'w') { /* w(x,y) = x0y1-x1y0+x2y3-x3y2 */
                int row[7] = {NEG[xv[1]], xv[0], NEG[xv[3]], xv[2]}; memcpy(A[r++], row, sizeof row);
            } else {
                const int *X = xv;
                int R[7][7]; memset(R, 0, sizeof R);
                /* p_ij(x,y) = x_i y_j - x_j y_i: coefficient of y_j is x_i, of y_i is -x_j */
#define P(rw, i, j, sg) do { if (sg > 0) { R[rw][j] = AD(R[rw][j], X[i]); R[rw][i] = SB(R[rw][i], X[j]); } \
                             else { R[rw][j] = SB(R[rw][j], X[i]); R[rw][i] = AD(R[rw][i], X[j]); } } while (0)
                P(0, 1, 2, 1); P(0, 3, 4, -1);   /* p12 - p34 */
                P(1, 5, 4, 1); P(1, 3, 2, -1);   /* p54 - p32 */
                P(2, 2, 0, 1); P(2, 3, 5, -1);   /* p20 - p35 */
                P(3, 6, 5, 1); P(3, 3, 0, -1);   /* p65 - p30 */
                P(4, 0, 1, 1); P(4, 3, 6, -1);   /* p01 - p36 */
                P(5, 4, 6, 1); P(5, 3, 1, -1);   /* p46 - p31 */
                /* B(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3 */
                R[6][4] = X[0]; R[6][0] = X[4]; R[6][5] = X[1]; R[6][1] = X[5]; R[6][6] = X[2]; R[6][2] = X[6];
                R[6][3] = SB(0, AD(X[3], X[3]));
                for (int i = 0; i < 7; i++) memcpy(A[r++], R[i], sizeof R[i]);
            }
            int B[7][7]; int nb = nullspace(r, A, B);
            if (nb != 3) { fprintf(stderr, "point %d: solution space dim %d\n", x, nb); return 1; }
            /* enumerate plane points y = a B0 + b B1 + c B2, y != x; collect line span(x,y) */
            int seen_cnt = 0; int64_t ycodes[300]; int ny = 0;
            for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) for (int c = 0; c < q; c++) {
                if (!a && !b && !c) continue;
                int y[7]; for (int j = 0; j < dim; j++) y[j] = AD(AD(MU(a, B[0][j]), MU(b, B[1][j])), MU(c, B[2][j]));
                int f = 0; for (int j = 0; j < dim; j++) if (y[j]) { f = y[j]; break; }
                if (f != 1) continue;
                int yi = lookup(y);
                if (yi < 0) { fprintf(stderr, "plane point not a point of the geometry (x=%d)\n", x); return 1; }
                if (yi == x) continue;
                ycodes[ny++] = yi;
            }
            (void)seen_cnt;
            if (ny != q * q + q) { fprintf(stderr, "plane size %d\n", ny); return 1; }
            /* group y's into lines through x */
            int used[300] = {0};
            for (int t = 0; t < ny; t++) if (!used[t]) {
                int yv[7]; int64_t s2 = codes[ycodes[t]]; for (int j = 0; j < dim; j++) { yv[j] = s2 % q; s2 /= q; }
                int pts[17], np = 0; pts[np++] = x;
                for (int lam = 0; lam < q; lam++) { int z[7]; for (int j = 0; j < dim; j++) z[j] = AD(MU(lam, xv[j]), yv[j]); int zi = lookup(z); pts[np++] = zi; }
                for (int u = 1; u < np; u++) for (int w = 0; w < ny; w++) if (ycodes[w] == pts[u]) used[w] = 1;
                qsort(pts, np, sizeof(int), cmpi);
                if (pts[0] == x) { memcpy(lines + L * k1, pts, sizeof(int) * k1); L++; }
            }
        }
    }
    for (long l = 0; l < L; l++) for (int t = 0; t < k1; t++) onl[lines[l * k1 + t]]++;
    for (int x = 0; x < N; x++) if (onl[x] != k1) { fprintf(stderr, "point %d on %d lines\n", x, onl[x]); return 1; }
    if (L != N) { fprintf(stderr, "lines %ld points %d\n", L, N); return 1; }
    FILE *f = fopen(argv[3], "w"); fprintf(f, "%ld\n", (long)N + L);
    for (long l = 0; l < L; l++) for (int t = 0; t < k1; t++) fprintf(f, "%d %ld\n", lines[l * k1 + t], N + l);
    fclose(f);
    if (argc > 4) {
        FILE *g = fopen(argv[4], "w");
        for (int x = 0; x < N; x++) { int64_t s = codes[x]; fprintf(g, "%d", x); for (int i = 0; i < dim; i++) { fprintf(g, " %d", (int)(s % q)); s /= q; } fprintf(g, "\n"); }
        fclose(g);
    }
    printf("%s q=%d points=%d lines=%ld vertices=%ld edges=%ld\n", argv[1], q, N, L, N + L, L * k1);
    return 0;
}
