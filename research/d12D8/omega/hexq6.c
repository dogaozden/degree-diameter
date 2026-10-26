/* Split Cayley hexagon H(q) in the parabolic quadric Q(6,q) (Tits 1959; Van Maldeghem, Generalized Polygons, 2.4.13).
   Points: all points of Q(6,q): X0X4 + X1X5 + X2X6 = X3^2.
   Lines: the lines of Q(6,q) whose Grassmann coordinates p_ij = x_i y_j - x_j y_i satisfy
          p12 = p34, p54 = p32, p20 = p35, p65 = p30, p01 = p36, p46 = p31.
   q prime, 4, 8 (polynomial basis) or 9 (GF(9) = GF(3)[i], i^2 = -1). Writes:  "q npoints nlines" then one line per H-line (its q+1 point
   indices, sorted), then the point coordinates ("P x0..x6", field elements as integers, GF(9): a+bi -> a+3b).
   Usage: hexq6 q out.txt          (build: cc -O2 -o hexq6 hexq6.c) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int q, p, ADD[16][16], MUL[16][16], NEG[16], INV[16];
static void field(void) {
    if (q == 4 || q == 8) { p = 2; int m = q == 4 ? 2 : 3, poly = q == 4 ? 7 : 11;   /* x^2+x+1, x^3+x+1 */
        for (int x = 0; x < q; x++) for (int y = 0; y < q; y++) { int r = 0, a = x, b = y;
            ADD[x][y] = x ^ y; while (b) { if (b & 1) r ^= a; b >>= 1; a <<= 1; if (a & q) a ^= poly; } MUL[x][y] = r; }
        (void)m;
    } else if (q == 9) { p = 3;
        for (int x = 0; x < 9; x++) for (int y = 0; y < 9; y++) {
            int a = x % 3, b = x / 3, c = y % 3, d = y / 3;
            ADD[x][y] = (a + c) % 3 + 3 * ((b + d) % 3);
            MUL[x][y] = ((a * c - b * d) % 3 + 3) % 3 + 3 * ((a * d + b * c) % 3); }
    } else { p = q;
        for (int x = 0; x < q; x++) for (int y = 0; y < q; y++) { ADD[x][y] = (x + y) % q; MUL[x][y] = x * y % q; } }
    for (int x = 0; x < q; x++) for (int y = 0; y < q; y++) { if (ADD[x][y] == 0) NEG[x] = y; if (MUL[x][y] == 1) INV[x] = y; }
}
static int sub(int a, int b) { return ADD[a][NEG[b]]; }
static int Qf(const int *x) { /* X0X4 + X1X5 + X2X6 - X3^2 */
    int s = MUL[x[0]][x[4]]; s = ADD[s][MUL[x[1]][x[5]]]; s = ADD[s][MUL[x[2]][x[6]]]; return sub(s, MUL[x[3]][x[3]]); }
static int Bf(const int *x, const int *y) { /* polar form */
    int s = ADD[MUL[x[0]][y[4]]][MUL[x[4]][y[0]]]; s = ADD[s][ADD[MUL[x[1]][y[5]]][MUL[x[5]][y[1]]]];
    s = ADD[s][ADD[MUL[x[2]][y[6]]][MUL[x[6]][y[2]]]]; int t = MUL[x[3]][y[3]]; return sub(s, ADD[t][t]); }
static long code(const int *x) { long c = 0; for (int i = 0; i < 7; i++) c = c * q + x[i]; return c; }
static int npt; static int (*P)[7]; static int *idx;
static void normalize(int *x) { int i = 0; while (x[i] == 0) i++; int s = INV[x[i]]; for (int j = 0; j < 7; j++) x[j] = MUL[x[j]][s]; }
static int pg(const int *x, const int *y, int i, int j) { return sub(MUL[x[i]][y[j]], MUL[x[j]][y[i]]); }
static int tits(const int *x, const int *y) {
    return pg(x, y, 1, 2) == pg(x, y, 3, 4) && pg(x, y, 5, 4) == pg(x, y, 3, 2) && pg(x, y, 2, 0) == pg(x, y, 3, 5) &&
           pg(x, y, 6, 5) == pg(x, y, 3, 0) && pg(x, y, 0, 1) == pg(x, y, 3, 6) && pg(x, y, 4, 6) == pg(x, y, 3, 1); }
static int cmpi(const void *a, const void *b) { return *(const int *)a - *(const int *)b; }
int main(int argc, char **argv) {
    q = atoi(argv[1]); field();
    long tot = 1; for (int i = 0; i < 7; i++) tot *= q;
    idx = malloc(tot * sizeof(int)); for (long c = 0; c < tot; c++) idx[c] = -1;
    P = malloc(sizeof(int[7]) * (tot / (q - 1) + 1)); npt = 0;
    int x[7];
    for (long c = 1; c < tot; c++) { long r = c; for (int i = 6; i >= 0; i--) { x[i] = r % q; r /= q; }
        int i = 0; while (x[i] == 0) i++; if (x[i] != 1) continue;     /* normalized: first nonzero = 1 */
        if (Qf(x) != 0) continue; memcpy(P[npt], x, sizeof x); idx[c] = npt++; }
    fprintf(stderr, "q=%d points=%d (expect %ld)\n", q, npt, (tot / q * q - 1) / (q - 1) == 0 ? 0 : ((long)q*q*q*q*q*q - 1) / (q - 1));
    /* lines: for each point a, each later point b with B(a,b)=0 and Tits(a,b): line = span(a,b); keep it once (min index = a, and b = second smallest) */
    int *L = malloc(sizeof(int) * (q + 1) * (long)npt * 2); int nl = 0, *deg = calloc(npt, sizeof(int));
    int pts[16];
    for (int a = 0; a < npt; a++) for (int b = a + 1; b < npt; b++) {
        if (Bf(P[a], P[b]) != 0 || !tits(P[a], P[b])) continue;
        /* points of span: b + l*a (l in F) and a */
        int ok = 1, m = 0; pts[m++] = a;
        for (int l = 0; l < q; l++) { int y[7]; for (int j = 0; j < 7; j++) y[j] = ADD[P[b][j]][MUL[l][P[a][j]]]; normalize(y);
            int id = idx[code(y)]; if (id < 0) { fprintf(stderr, "line point not on quadric\n"); return 1; } if (id < b && id != a) { ok = 0; break; } pts[m++] = id; }
        if (!ok) continue;                      /* (a,b) is not the (smallest, second smallest) pair of its line */
        qsort(pts, q + 1, sizeof(int), cmpi);
        if (pts[0] != a || pts[1] != b) continue;
        memcpy(L + (long)nl * (q + 1), pts, sizeof(int) * (q + 1)); nl++; for (int j = 0; j <= q; j++) deg[pts[j]]++; }
    int mind = 1 << 30, maxd = 0; for (int a = 0; a < npt; a++) { if (deg[a] < mind) mind = deg[a]; if (deg[a] > maxd) maxd = deg[a]; }
    fprintf(stderr, "lines=%d, lines per point min %d max %d\n", nl, mind, maxd);
    FILE *f = fopen(argv[2], "w"); fprintf(f, "%d %d %d\n", q, npt, nl);
    for (int l = 0; l < nl; l++) { for (int j = 0; j <= q; j++) fprintf(f, "%d%c", L[(long)l * (q + 1) + j], j == q ? '\n' : ' '); }
    for (int a = 0; a < npt; a++) { fprintf(f, "P"); for (int j = 0; j < 7; j++) fprintf(f, " %d", P[a][j]); fprintf(f, "\n"); }
    fclose(f); return 0;
}
