/* hexgen.c: the split Cayley hexagon H(q) for q = p or p^2 (p odd prime), as in research/gh6/gh_build.py.
   Points: points of the quadric X0X4 + X1X5 + X2X6 = X3^2 in PG(6,q).
   Lines: for each point x, the points y with Tits' six equations p12=p34, p54=p32, p20=p35, p65=p30, p01=p36,
   p46=p31 (p_ij = x_i y_j - x_j y_i) and B(x,y)=0 form a plane through x; its q+1 lines through x are the lines
   of H(q) on x.  Checks: |lines| = |points| = (q^6-1)/(q-1), q+1 points per line, q+1 lines per point.
   Output: hex_q{q}.bin = int32 q, N, L, then L*(q+1) int32 point ids, then N*7 uint8 coordinates.
   Usage: hexgen q */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

int q, p, e;
int ADD[32][32], MUL[32][32], NEG[32], INV[32];

void field(void) {
    /* elements a + b*alpha, index a + p*b, alpha^2 = nr (a non-square mod p) */
    int nr = 0;
    if (e == 2) { for (int t = 2; t < p; t++) { int sq = 0; for (int u = 1; u < p; u++) if (u * u % p == t) sq = 1; if (!sq) { nr = t; break; } } }
    for (int x = 0; x < q; x++) for (int y = 0; y < q; y++) {
        int a = x % p, b = x / p, c = y % p, d = y / p;
        ADD[x][y] = (a + c) % p + p * ((b + d) % p);
        int re = (a * c + b * d % p * nr) % p, im = (a * d + b * c) % p;
        MUL[x][y] = re + p * im;
    }
    for (int x = 0; x < q; x++) { for (int y = 0; y < q; y++) { if (ADD[x][y] == 0) NEG[x] = y; if (MUL[x][y] == 1) INV[x] = y; } }
}
static inline int ad(int a, int b) { return ADD[a][b]; }
static inline int mu(int a, int b) { return MUL[a][b]; }
static inline int sb(int a, int b) { return ADD[a][NEG[b]]; }

int64_t code(const int *v) { int64_t c = 0; for (int i = 6; i >= 0; i--) c = c * q + v[i]; return c; }
void normalize(int *v) { for (int i = 0; i < 7; i++) if (v[i]) { int s = INV[v[i]]; for (int j = 0; j < 7; j++) v[j] = mu(s, v[j]); return; } }

int64_t *codes; int N;
int lookup(int *v) {
    normalize(v); int64_t c = code(v); int lo = 0, hi = N - 1;
    while (lo <= hi) { int m = (lo + hi) / 2; if (codes[m] == c) return m; if (codes[m] < c) lo = m + 1; else hi = m - 1; }
    fprintf(stderr, "point not found\n"); exit(1);
}
int Qf(const int *v) { /* X0X4 + X1X5 + X2X6 - X3^2 */
    return sb(ad(ad(mu(v[0], v[4]), mu(v[1], v[5])), mu(v[2], v[6])), mu(v[3], v[3]));
}

/* nullspace of a k x 7 matrix; returns dimension, basis rows in B */
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

int main(int argc, char **argv) {
    q = atoi(argv[1]);
    for (p = 2; q % p; p++) {}
    e = (q == p) ? 1 : 2;
    if (e == 2 && p * p != q) { fprintf(stderr, "q must be p or p^2\n"); return 1; }
    field();
    int64_t total = 1; for (int i = 0; i < 7; i++) total *= q;
    int64_t want = 0, pw = 1; for (int i = 0; i < 6; i++) { want += pw; pw *= q; }
    codes = malloc(sizeof(int64_t) * want); N = 0;
    int v[7];
    for (int64_t c = 0; c < total; c++) {
        int64_t t = c; for (int i = 0; i < 7; i++) { v[i] = t % q; t /= q; }
        int f = -1; for (int i = 0; i < 7; i++) if (v[i]) { f = v[i]; break; }
        if (f != 1) continue;
        if (Qf(v)) continue;
        codes[N++] = c;  /* increasing order of c */
    }
    fprintf(stderr, "q=%d points %d (want %lld)\n", q, N, (long long)want);
    if (N != want) return 1;
    int Q1 = q + 1;
    int32_t *lines = malloc(sizeof(int32_t) * (int64_t)N * Q1); int L = 0;
    int *cnt = calloc(N, sizeof(int));
    uint8_t *coord = malloc((size_t)N * 7);
    for (int i = 0; i < N; i++) { int64_t t = codes[i]; for (int j = 0; j < 7; j++) { coord[(size_t)i * 7 + j] = t % q; t /= q; } }
    int two = ad(1, 1);
    for (int i = 0; i < N; i++) {
        int x[7]; for (int j = 0; j < 7; j++) x[j] = coord[(size_t)i * 7 + j];
        int M[7][7]; memset(M, 0, sizeof M);
        /* polar: x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3 */
        M[0][4] = x[0]; M[0][0] = x[4]; M[0][5] = x[1]; M[0][1] = x[5]; M[0][6] = x[2]; M[0][2] = x[6]; M[0][3] = NEG[mu(two, x[3])];
        /* p_ab - p_cd = 0 with p_ab = x_a y_b - x_b y_a, as a row in y */
        int eq[6][4] = {{1,2,3,4},{5,4,3,2},{2,0,3,5},{6,5,3,0},{0,1,3,6},{4,6,3,1}};
        for (int r = 0; r < 6; r++) {
            int a = eq[r][0], b = eq[r][1], c = eq[r][2], d = eq[r][3];
            int *R = M[r + 1];
            R[b] = ad(R[b], x[a]); R[a] = sb(R[a], x[b]);
            R[d] = sb(R[d], x[c]); R[c] = ad(R[c], x[d]);
        }
        int B[7][7]; int dim = nullspace(M, 7, B);
        if (dim != 3) { fprintf(stderr, "point %d: plane dim %d\n", i, dim); return 1; }
        /* basis b1, b2 of the plane independent of x: pick two basis vectors not making a dependent set with x */
        int b[2][7], nb = 0;
        for (int k = 0; k < 3 && nb < 2; k++) {
            /* test rank of {x, chosen..., B[k]} */
            int T[3][7]; int rows = 0;
            for (int j = 0; j < 7; j++) T[0][j] = x[j]; rows = 1;
            for (int s = 0; s < nb; s++) { for (int j = 0; j < 7; j++) T[rows][j] = b[s][j]; rows++; }
            for (int j = 0; j < 7; j++) T[rows][j] = B[k][j]; rows++;
            int Z[7][7]; int dz = nullspace(T, rows, Z);  /* rank = 7 - dz */
            if (7 - dz == rows) { for (int j = 0; j < 7; j++) b[nb][j] = B[k][j]; nb++; }
        }
        if (nb != 2) { fprintf(stderr, "basis fail\n"); return 1; }
        for (int t = 0; t <= q; t++) {
            int d[7];
            for (int j = 0; j < 7; j++) d[j] = (t == q) ? b[1][j] : ad(b[0][j], mu(t, b[1][j]));
            int ids[32], n = 0, mn = 1 << 30;
            int w[7]; for (int j = 0; j < 7; j++) w[j] = d[j];
            ids[n++] = lookup(w);
            for (int lam = 0; lam < q; lam++) { for (int j = 0; j < 7; j++) w[j] = ad(x[j], mu(lam, d[j])); ids[n++] = lookup(w); }
            for (int s = 0; s < n; s++) if (ids[s] < mn) mn = ids[s];
            if (mn != i) continue;
            /* sort ids */
            for (int s = 1; s < n; s++) { int k2 = ids[s], u = s - 1; while (u >= 0 && ids[u] > k2) { ids[u + 1] = ids[u]; u--; } ids[u + 1] = k2; }
            for (int s = 0; s < n; s++) { if (s && ids[s] == ids[s - 1]) { fprintf(stderr, "dup point on line\n"); return 1; } lines[(int64_t)L * Q1 + s] = ids[s]; cnt[ids[s]]++; }
            L++;
            if (L > N) { fprintf(stderr, "too many lines\n"); return 1; }
        }
    }
    int ok = (L == N);
    for (int i = 0; i < N; i++) if (cnt[i] != Q1) ok = 0;
    fprintf(stderr, "lines %d, every point on q+1 lines: %s\n", L, ok ? "yes" : "NO");
    if (!ok) return 1;
    char fn[64]; sprintf(fn, "hex/hex_q%d.bin", q);
    FILE *f = fopen(fn, "wb"); int32_t hdr[3] = {q, N, L};
    fwrite(hdr, 4, 3, f); fwrite(lines, 4, (size_t)L * Q1, f); fwrite(coord, 1, (size_t)N * 7, f); fclose(f);
    fprintf(stderr, "wrote %s\n", fn);
    return 0;
}
