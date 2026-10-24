/* gh8.c: split Cayley hexagon H(8) over GF(8) = GF(2)[t]/(t^3+t+1), Tits' coordinates as in research/p4/d6/hexgen.c
   (characteristic 2: minus = plus, 2 = 0). Points: normalized vectors of PG(6,8) on X0X4 + X1X5 + X2X6 + X3^2 = 0.
   Lines: for each point x the plane pi_x = {y : B(x,y) = 0 and the six Tits equations p12=p34, p54=p32, p20=p35,
   p65=p30, p01=p36, p46=p31 with p_ab = x_a y_b - x_b y_a} (a 3-dim space through x); its q+1 lines through x are hexagon lines.
   Checks (stderr): dim pi_x = 3, pi_x totally singular, every point on q+1 lines, L = P = 37449, q+1 points per line.
   Output (stdout): "P q", then L lines with their q+1 point ids (text format of gh_build.c / hexbin2txt.py).
   Compile: gcc -O2 -o gh8 gh8.c    Run: ./gh8 > gh_8.txt */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define Q 8
#define Q1 9
static int ADD[Q][Q], MUL[Q][Q], NEG[Q], INV[Q];
static inline int ad(int a, int b) { return a ^ b; }
static inline int mu(int a, int b) { return MUL[a][b]; }
static inline int sb(int a, int b) { return a ^ b; }   /* characteristic 2 */

static int gmul(int a, int b) {
    int r = 0;
    for (int i = 0; i < 3; i++) if ((b >> i) & 1) r ^= a << i;
    for (int bit = 4; bit >= 3; bit--) if ((r >> bit) & 1) r ^= 0xB << (bit - 3);   /* t^3 = t + 1 */
    return r;
}
static void field(void) {
    for (int x = 0; x < Q; x++) for (int y = 0; y < Q; y++) { ADD[x][y] = x ^ y; MUL[x][y] = gmul(x, y); }
    for (int x = 0; x < Q; x++) { NEG[x] = x; INV[x] = -1; for (int y = 0; y < Q; y++) if (MUL[x][y] == 1) INV[x] = y; }
    for (int x = 1; x < Q; x++) if (INV[x] < 0) { fprintf(stderr, "field error\n"); exit(1); }
}

int64_t code(const int *v) { int64_t c = 0; for (int i = 6; i >= 0; i--) c = c * Q + v[i]; return c; }
void normalize(int *v) { for (int i = 0; i < 7; i++) if (v[i]) { int s = INV[v[i]]; for (int j = 0; j < 7; j++) v[j] = mu(s, v[j]); return; } }

int64_t *codes; int N;
int lookup(int *v) {
    normalize(v); int64_t c = code(v); int lo = 0, hi = N - 1;
    while (lo <= hi) { int m = (lo + hi) / 2; if (codes[m] == c) return m; if (codes[m] < c) lo = m + 1; else hi = m - 1; }
    fprintf(stderr, "point not found\n"); exit(1);
}
int Qf(const int *v) { /* X0X4 + X1X5 + X2X6 - X3^2 (= + in char 2) */
    return sb(ad(ad(mu(v[0], v[4]), mu(v[1], v[5])), mu(v[2], v[6])), mu(v[3], v[3]));
}

/* nullspace of a k x 7 matrix over GF(8); returns dimension, basis rows in B */
int nullspace(int M[][7], int k, int B[][7]) {
    int piv[7], r = 0, isp[7] = {0};
    for (int c = 0; c < 7 && r < k; c++) {
        int s = -1; for (int i = r; i < k; i++) if (M[i][c]) { s = i; break; }
        if (s < 0) continue;
        for (int j = 0; j < 7; j++) { int t = M[r][j]; M[r][j] = M[s][j]; M[s][j] = t; }
        int iv = INV[M[r][c]]; for (int j = 0; j < 7; j++) M[r][j] = mu(iv, M[r][j]);
        for (int i = 0; i < k; i++) if (i != r && M[i][c]) { int f = M[i][c]; for (int j = 0; j < 7; j++) M[i][j] = sb(M[i][j], mu(f, M[r][j])); }
        piv[r] = c; isp[c] = 1; r++;
    }
    int d = 0;
    for (int fcol = 0; fcol < 7; fcol++) if (!isp[fcol]) {
        for (int j = 0; j < 7; j++) B[d][j] = 0;
        B[d][fcol] = 1;
        for (int i = 0; i < r; i++) B[d][piv[i]] = NEG[M[i][fcol]];
        d++;
    }
    return d;
}

int main(void) {
    field();
    int64_t total = 1; for (int i = 0; i < 7; i++) total *= Q;
    int64_t want = 0, pw = 1; for (int i = 0; i < 6; i++) { want += pw; pw *= Q; }   /* (q^6-1)/(q-1) */
    codes = malloc(sizeof(int64_t) * want); N = 0;
    int v[7];
    for (int64_t c = 0; c < total; c++) {
        int64_t t = c; for (int i = 0; i < 7; i++) { v[i] = t % Q; t /= Q; }
        int f = -1; for (int i = 0; i < 7; i++) if (v[i]) { f = v[i]; break; }
        if (f != 1) continue;               /* normalized: first nonzero coordinate is 1 */
        if (Qf(v)) continue;
        if (N >= want) { fprintf(stderr, "too many points\n"); return 1; }
        codes[N++] = c;                     /* increasing order of c */
    }
    fprintf(stderr, "H(8): points %d (want %lld)\n", N, (long long)want);
    if (N != want) return 1;
    int32_t *lines = malloc(sizeof(int32_t) * (int64_t)N * Q1); int L = 0;
    int *cnt = calloc(N, sizeof(int));
    uint8_t *coord = malloc((size_t)N * 7);
    for (int i = 0; i < N; i++) { int64_t t = codes[i]; for (int j = 0; j < 7; j++) { coord[(size_t)i * 7 + j] = t % Q; t /= Q; } }
    for (int i = 0; i < N; i++) {
        int x[7]; for (int j = 0; j < 7; j++) x[j] = coord[(size_t)i * 7 + j];
        int M[7][7]; memset(M, 0, sizeof M);
        /* polar: x0y4+x4y0+x1y5+x5y1+x2y6+x6y2 + x3y3 * (2 = 0) */
        M[0][4] = x[0]; M[0][0] = x[4]; M[0][5] = x[1]; M[0][1] = x[5]; M[0][6] = x[2]; M[0][2] = x[6]; M[0][3] = 0;
        /* p_ab - p_cd = 0 with p_ab = x_a y_b - x_b y_a, as a row in y (same table as hexgen.c) */
        int eq[6][4] = {{1,2,3,4},{5,4,3,2},{2,0,3,5},{6,5,3,0},{0,1,3,6},{4,6,3,1}};
        for (int r = 0; r < 6; r++) {
            int a = eq[r][0], b = eq[r][1], c = eq[r][2], d = eq[r][3];
            int *R = M[r + 1];
            R[b] = ad(R[b], x[a]); R[a] = sb(R[a], x[b]);
            R[d] = sb(R[d], x[c]); R[c] = ad(R[c], x[d]);
        }
        int B[7][7]; int dim = nullspace(M, 7, B);
        if (dim != 3) { fprintf(stderr, "point %d: plane dim %d\n", i, dim); return 1; }
        int b[2][7], nb = 0;
        for (int k = 0; k < 3 && nb < 2; k++) {
            int T[3][7]; int rows = 0;
            for (int j = 0; j < 7; j++) T[0][j] = x[j]; rows = 1;
            for (int s = 0; s < nb; s++) { for (int j = 0; j < 7; j++) T[rows][j] = b[s][j]; rows++; }
            for (int j = 0; j < 7; j++) T[rows][j] = B[k][j]; rows++;
            int Z[7][7]; int dz = nullspace(T, rows, Z);
            if (7 - dz == rows) { for (int j = 0; j < 7; j++) b[nb][j] = B[k][j]; nb++; }
        }
        if (nb != 2) { fprintf(stderr, "basis fail at %d\n", i); return 1; }
        /* pi_x totally singular: all nonzero alpha x + beta b0 + gamma b1 lie on Q */
        for (int al = 0; al < Q; al++) for (int be = 0; be < Q; be++) for (int ga = 0; ga < Q; ga++) {
            if (!al && !be && !ga) continue;
            int y[7]; for (int j = 0; j < 7; j++) y[j] = ad(ad(mu(al, x[j]), mu(be, b[0][j])), mu(ga, b[1][j]));
            if (Qf(y)) { fprintf(stderr, "pi_x not totally singular at %d\n", i); return 1; }
        }
        for (int t = 0; t <= Q; t++) {
            int d[7];
            for (int j = 0; j < 7; j++) d[j] = (t == Q) ? b[1][j] : ad(b[0][j], mu(t, b[1][j]));
            int ids[Q1 + 1], n = 0, mn = 1 << 30;
            int w[7]; for (int j = 0; j < 7; j++) w[j] = d[j];
            ids[n++] = lookup(w);
            for (int lam = 0; lam < Q; lam++) { for (int j = 0; j < 7; j++) w[j] = ad(x[j], mu(lam, d[j])); ids[n++] = lookup(w); }
            for (int s = 0; s < n; s++) if (ids[s] < mn) mn = ids[s];
            if (mn != i) continue;          /* each line recorded once, from its smallest point */
            for (int s = 1; s < n; s++) { int k2 = ids[s], u = s - 1; while (u >= 0 && ids[u] > k2) { ids[u + 1] = ids[u]; u--; } ids[u + 1] = k2; }
            for (int s = 0; s < n; s++) { if (s && ids[s] == ids[s - 1]) { fprintf(stderr, "dup point on line\n"); return 1; } lines[(int64_t)L * Q1 + s] = ids[s]; cnt[ids[s]]++; }
            L++;
            if (L > N) { fprintf(stderr, "too many lines\n"); return 1; }
        }
    }
    int ok = (L == N);
    for (int i = 0; i < N; i++) if (cnt[i] != Q1) ok = 0;
    fprintf(stderr, "lines %d (want %d), every point on q+1 = 9 lines: %s\n", L, N, ok ? "yes" : "NO");
    if (!ok) return 1;
    printf("%d %d\n", N, Q);
    for (int l = 0; l < L; l++) {
        for (int a = 0; a < Q1; a++) printf(a ? " %d" : "%d", lines[(int64_t)l * Q1 + a]);
        printf("\n");
    }
    return 0;
}
