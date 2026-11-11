/* hexgf.c (referee omega-dq): the split Cayley hexagon H(q) for any prime power q <= 16, same split-octonion model
   as hexgen.c, but the lines through a point x are found as the kernel of the linear map y -> xy on pure octonions
   (a plane; its q^2+q other points are the points collinear with x) instead of a loop over all pairs.
   GF(q) = GF(p)[X]/(f), f the first monic irreducible of degree e found by search (elements coded in base p).
   Same output format and same point numbering as hexgen.c (points in increasing base-q code of the normalised vector).
   usage: hexgf q out.txt */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int q, p, e;
static int ad[16][16], mu[16][16], ng[16], iv[16];

static int polymul(int a, int b, const int *f) {   /* product of polynomials coded in base p, reduced mod monic f */
    int A[8] = {0}, Bc[8] = {0}, R[16] = {0};
    for (int i = 0; i < e; i++) { A[i] = a % p; a /= p; Bc[i] = b % p; b /= p; }
    for (int i = 0; i < e; i++) for (int j = 0; j < e; j++) R[i + j] = (R[i + j] + A[i] * Bc[j]) % p;
    for (int d = 2 * e - 2; d >= e; d--) if (R[d]) { int c = R[d];
        for (int i = 0; i <= e; i++) R[d - e + i] = ((R[d - e + i] - c * f[i]) % p + p) % p; }
    int r = 0; for (int i = e - 1; i >= 0; i--) r = r * p + R[i]; return r;
}

static void field(void) {
    p = q; e = 1;
    for (int d = 2; d <= q; d++) if (q % d == 0) { p = d; break; }
    for (int t = q; t > p; t /= p) e++;
    int f[9];
    for (int code = 0;; code++) {                     /* f = X^e + sum c_i X^i, c coded by 'code' */
        int c = code; for (int i = 0; i < e; i++) { f[i] = c % p; c /= p; } f[e] = 1;
        if (c) { fprintf(stderr, "no irreducible found\n"); exit(1); }
        int okf = 1;
        for (int a = 0; a < q && okf; a++) for (int b = 0; b < q; b++) {
            mu[a][b] = polymul(a, b, f);
            if (a && b && !mu[a][b]) { okf = 0; break; }
        }
        if (okf) break;
    }
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) {
        int x = a, y = b, r = 0, pw = 1;
        for (int i = 0; i < e; i++) { r += ((x % p + y % p) % p) * pw; x /= p; y /= p; pw *= p; }
        ad[a][b] = r;
    }
    for (int a = 0; a < q; a++) { for (int b = 0; b < q; b++) if (!ad[a][b]) ng[a] = b;
        for (int b = 1; b < q; b++) if (mu[a][b] == 1) iv[a] = b; }
}
#define ADD(a,b) ad[a][b]
#define MUL(a,b) mu[a][b]
#define SUB(a,b) ad[a][ng[b]]

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: hexgf q out\n"); return 1; }
    q = atoi(argv[1]); field();
    long qq7 = 1; for (int i = 0; i < 7; i++) qq7 *= q;
    long want = (qq7 / q - 1) / (q - 1);
    int (*P)[7] = malloc(sizeof(int[7]) * want); int n = 0;
    int *idx = malloc(sizeof(int) * qq7);
    for (long c = 0; c < qq7; c++) idx[c] = -1;
    for (long c = 1; c < qq7; c++) {
        int x[7]; long r = c;
        for (int i = 6; i >= 0; i--) { x[i] = r % q; r /= q; }
        int f = 0; while (x[f] == 0) f++;
        if (x[f] != 1) continue;
        int Q = ADD(ADD(MUL(x[0], x[0]), MUL(x[1], x[4])), ADD(MUL(x[2], x[5]), MUL(x[3], x[6])));
        if (Q) continue;
        if (n >= want) { fprintf(stderr, "too many points\n"); return 2; }
        memcpy(P[n], x, sizeof x); idx[c] = n; n++;
    }
    fprintf(stderr, "q=%d (p=%d, e=%d) points %d (expected %ld)\n", q, p, e, n, want);
    if (n != want) return 2;
    int *lines = malloc(sizeof(int) * (q + 1) * (long)n); long nl = 0;
    int *deg = calloc(n, sizeof(int)); long nbad = 0;
    for (int a = 0; a < n; a++) {
        const int *x = P[a]; int A = x[0], nA = ng[x[0]]; const int *u = x + 1, *v = x + 4;
        int M[8][7]; memset(M, 0, sizeof M);              /* rows: coordinates of xy; columns: y = (a', u', v') */
        M[0][0] = A; for (int i = 0; i < 3; i++) M[0][4 + i] = u[i];             /* tl = a a' + u.v' */
        M[7][0] = A; for (int i = 0; i < 3; i++) M[7][1 + i] = v[i];             /* br = a a' + v.u' */
        for (int i = 0; i < 3; i++) { int j = (i + 1) % 3, k = (i + 2) % 3;
            M[1 + i][1 + i] = A; M[1 + i][0] = ng[u[i]];                         /* tr_i = a u'_i - a' u_i + v_j v'_k - v_k v'_j */
            M[1 + i][4 + k] = ADD(M[1 + i][4 + k], v[j]); M[1 + i][4 + j] = ADD(M[1 + i][4 + j], ng[v[k]]);
            M[4 + i][0] = v[i]; M[4 + i][4 + i] = nA;                            /* bl_i = a' v_i - a v'_i - u_j u'_k + u_k u'_j */
            M[4 + i][1 + k] = ADD(M[4 + i][1 + k], ng[u[j]]); M[4 + i][1 + j] = ADD(M[4 + i][1 + j], u[k]); }
        /* row reduce, kernel basis */
        int piv[8], np = 0, isp[7] = {0};
        for (int col = 0; col < 7 && np < 8; col++) {
            int r = -1; for (int i = np; i < 8; i++) if (M[i][col]) { r = i; break; }
            if (r < 0) continue;
            for (int j = 0; j < 7; j++) { int t = M[r][j]; M[r][j] = M[np][j]; M[np][j] = t; }
            int s = iv[M[np][col]]; for (int j = 0; j < 7; j++) M[np][j] = MUL(M[np][j], s);
            for (int i = 0; i < 8; i++) if (i != np && M[i][col]) { int c = M[i][col];
                for (int j = 0; j < 7; j++) M[i][j] = SUB(M[i][j], MUL(c, M[np][j])); }
            piv[np++] = col; isp[col] = 1;
        }
        int kd = 7 - np, K[7][7], fr[7], nf = 0;
        if (kd != 3) { fprintf(stderr, "point %d: kernel dimension %d\n", a, kd); return 3; }
        for (int col = 0; col < 7; col++) if (!isp[col]) fr[nf++] = col;
        for (int b = 0; b < kd; b++) { for (int j = 0; j < 7; j++) K[b][j] = 0; K[b][fr[b]] = 1;
            for (int i = 0; i < np; i++) K[b][piv[i]] = ng[M[i][fr[b]]]; }
        /* all points of the kernel plane */
        int plane[400], npl = 0;
        for (int c0 = 0; c0 < q; c0++) for (int c1 = 0; c1 < q; c1++) for (int c2 = 0; c2 < q; c2++) {
            int z[7]; for (int j = 0; j < 7; j++) z[j] = ADD(ADD(MUL(c0, K[0][j]), MUL(c1, K[1][j])), MUL(c2, K[2][j]));
            int f = 0; while (f < 7 && z[f] == 0) f++;
            if (f == 7 || z[f] != 1) continue;            /* normalised representatives only */
            long code = 0; for (int j = 0; j < 7; j++) code = code * q + z[j];
            if (idx[code] < 0) { nbad++; continue; }
            plane[npl++] = idx[code];
        }
        if (npl != q * q + q + 1) { fprintf(stderr, "point %d: plane has %d points\n", a, npl); return 4; }
        for (int i = 0; i < npl; i++) { int b = plane[i]; if (b <= a) continue;
            /* line through a and b: b and P[b] + l*P[a] */
            int pts[32], m = 0; pts[m++] = a;
            for (int l = 0; l < q; l++) { int z[7]; for (int j = 0; j < 7; j++) z[j] = ADD(P[b][j], MUL(l, P[a][j]));
                int f = 0; while (z[f] == 0) f++; int s = iv[z[f]]; long code = 0;
                for (int j = 0; j < 7; j++) code = code * q + MUL(z[j], s);
                pts[m++] = idx[code]; }
            int m1 = n, m2 = n;
            for (int j = 0; j < m; j++) { int w = pts[j]; if (w < m1) { m2 = m1; m1 = w; } else if (w < m2) m2 = w; }
            if (m1 != a || m2 != b) continue;
            for (int j = 0; j < m; j++) { lines[nl * (q + 1) + j] = pts[j]; deg[pts[j]]++; }
            nl++;
        }
    }
    int bad = 0; for (int a = 0; a < n; a++) if (deg[a] != q + 1) bad++;
    fprintf(stderr, "lines %ld (expected %d); points not on exactly q+1 lines: %d; kernel vectors off the quadric: %ld\n", nl, n, bad, nbad);
    if (nl != n || bad || nbad) return 5;
    FILE *fo = fopen(argv[2], "w");
    fprintf(fo, "%d\n", 2 * n);
    for (long l = 0; l < nl; l++) for (int i = 0; i <= q; i++) fprintf(fo, "%d %ld\n", lines[l * (q + 1) + i], n + l);
    fclose(fo);
    return 0;
}
