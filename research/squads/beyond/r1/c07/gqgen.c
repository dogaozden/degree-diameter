/* gqgen.c: the symplectic generalized quadrangle W(q) (points of PG(3,q), totally isotropic lines of
   x0y1 - x1y0 + x2y3 - x3y2) for any prime power q <= 32, written in the hex bin format of hexgen2.c:
   int32 q, N, L, then L*(q+1) int32 point ids, then N*7 uint8 coordinates (the 4 coordinates, then 3 zeros).
   Lines through x = the q+1 lines through x in the plane x^perp.  usage: gqgen q  -> gq/gq_q{q}.bin */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int q, p, e; int ADD[32][32], MUL[32][32], NEG[32], INV[32];
static int poly_for(int q, int *c) { memset(c, 0, sizeof(int) * 8);
    switch (q) { case 4: c[0] = 1; c[1] = 1; return 2; case 8: c[0] = 1; c[1] = 1; return 3; case 9: c[0] = 1; return 2;
        case 16: c[0] = 1; c[1] = 1; return 4; case 25: c[0] = 2; return 2; case 27: c[0] = 1; c[1] = 2; return 3;
        case 32: c[0] = 1; c[2] = 1; return 5; } return 1; }
void field(void) { int c[8]; e = poly_for(q, c);
    for (int x = 0; x < q; x++) for (int y = 0; y < q; y++) { int a[8] = {0}, b[8] = {0}, r[16] = {0};
        int t = x; for (int i = 0; i < e; i++) { a[i] = t % p; t /= p; } t = y; for (int i = 0; i < e; i++) { b[i] = t % p; t /= p; }
        int s = 0, pw = 1; for (int i = 0; i < e; i++) { s += ((a[i] + b[i]) % p) * pw; pw *= p; } ADD[x][y] = s;
        for (int i = 0; i < e; i++) for (int j = 0; j < e; j++) r[i + j] = (r[i + j] + a[i] * b[j]) % p;
        for (int k = 2 * e - 2; k >= e; k--) { int f = r[k]; if (!f) continue; r[k] = 0; for (int i = 0; i < e; i++) r[k - e + i] = ((r[k - e + i] - f * c[i]) % p + p) % p; }
        s = 0; pw = 1; for (int i = 0; i < e; i++) { s += r[i] * pw; pw *= p; } MUL[x][y] = s; }
    for (int x = 0; x < q; x++) for (int y = 0; y < q; y++) { if (ADD[x][y] == 0) NEG[x] = y; if (MUL[x][y] == 1) INV[x] = y; } }
#define ad(a,b) ADD[a][b]
#define mu(a,b) MUL[a][b]
#define sb(a,b) ADD[a][NEG[b]]
int N; int64_t *codes;
int64_t code(const int *v) { int64_t c = 0; for (int i = 3; i >= 0; i--) c = c * q + v[i]; return c; }
void normalize(int *v) { for (int i = 0; i < 4; i++) if (v[i]) { int s = INV[v[i]]; for (int j = 0; j < 4; j++) v[j] = mu(s, v[j]); return; } }
int lookup(int *v) { normalize(v); int64_t c = code(v); int lo = 0, hi = N - 1;
    while (lo <= hi) { int m = (lo + hi) / 2; if (codes[m] == c) return m; if (codes[m] < c) lo = m + 1; else hi = m - 1; }
    fprintf(stderr, "not found\n"); exit(1); }
int main(int argc, char **argv) {
    q = atoi(argv[1]); for (p = 2; q % p; p++) {} field();
    int64_t total = (int64_t)q * q * q * q; codes = malloc(8 * total); N = 0; int v[4];
    for (int64_t c = 0; c < total; c++) { int64_t t = c; for (int i = 0; i < 4; i++) { v[i] = t % q; t /= q; }
        int f = -1; for (int i = 0; i < 4; i++) if (v[i]) { f = v[i]; break; } if (f != 1) continue; codes[N++] = c; }
    int want = (q + 1) * (q * q + 1); if (N != want) { fprintf(stderr, "points %d want %d\n", N, want); return 1; }
    int Q1 = q + 1; int32_t *lines = malloc(4L * N * Q1); int L = 0; int *cnt = calloc(N, sizeof(int)); uint8_t *coord = calloc((size_t)N * 7, 1);
    for (int i = 0; i < N; i++) { int64_t t = codes[i]; for (int j = 0; j < 4; j++) { coord[(size_t)i * 7 + j] = t % q; t /= q; } }
    for (int i = 0; i < N; i++) {
        int x[4]; for (int j = 0; j < 4; j++) x[j] = coord[(size_t)i * 7 + j];
        /* x^perp: y with x0y1 - x1y0 + x2y3 - x3y2 = 0  -> row (-x1, x0, -x3, x2) */
        int row[4] = {NEG[x[1]], x[0], NEG[x[3]], x[2]};
        /* basis of the nullspace (3-dim), then pick 2 vectors independent of x */
        int piv = -1; for (int j = 0; j < 4; j++) if (row[j]) { piv = j; break; }
        int B[3][4], nb = 0;
        for (int fcol = 0; fcol < 4; fcol++) if (fcol != piv) { int w[4] = {0}; w[fcol] = 1; w[piv] = mu(NEG[row[fcol]], INV[row[piv]]); memcpy(B[nb++], w, sizeof w); }
        int b[2][4], k2 = 0;
        for (int k = 0; k < 3 && k2 < 2; k++) {   /* test independence of {x, chosen, B[k]} via 2x2/3x3 minors */
            int M[3][4], r = 0; memcpy(M[r++], x, sizeof x); for (int s = 0; s < k2; s++) memcpy(M[r++], b[s], sizeof b[s]); memcpy(M[r++], B[k], sizeof B[k]);
            /* rank by elimination */
            int rank = 0, used[4] = {0};
            for (int c = 0; c < 4 && rank < r; c++) { int s = -1; for (int i2 = rank; i2 < r; i2++) if (M[i2][c]) { s = i2; break; } if (s < 0) continue;
                int tmp[4]; memcpy(tmp, M[s], sizeof tmp); memcpy(M[s], M[rank], sizeof tmp); memcpy(M[rank], tmp, sizeof tmp);
                int iv = INV[M[rank][c]]; for (int j = 0; j < 4; j++) M[rank][j] = mu(iv, M[rank][j]);
                for (int i2 = 0; i2 < r; i2++) if (i2 != rank && M[i2][c]) { int f = M[i2][c]; for (int j = 0; j < 4; j++) M[i2][j] = sb(M[i2][j], mu(f, M[rank][j])); }
                rank++; used[c] = 1; }
            if (rank == r) { memcpy(b[k2++], B[k], sizeof B[k]); }
        }
        if (k2 != 2) { fprintf(stderr, "basis fail\n"); return 1; }
        for (int t = 0; t <= q; t++) {
            int d[4]; for (int j = 0; j < 4; j++) d[j] = (t == q) ? b[1][j] : ad(b[0][j], mu(t, b[1][j]));
            int ids[40], n = 0, mn = 1 << 30, w[4];
            memcpy(w, d, sizeof w); ids[n++] = lookup(w);
            for (int lam = 0; lam < q; lam++) { for (int j = 0; j < 4; j++) w[j] = ad(x[j], mu(lam, d[j])); ids[n++] = lookup(w); }
            for (int s = 0; s < n; s++) if (ids[s] < mn) mn = ids[s];
            if (mn != i) continue;
            for (int s = 1; s < n; s++) { int k3 = ids[s], u = s - 1; while (u >= 0 && ids[u] > k3) { ids[u + 1] = ids[u]; u--; } ids[u + 1] = k3; }
            for (int s = 0; s < n; s++) { if (s && ids[s] == ids[s - 1]) { fprintf(stderr, "dup\n"); return 1; } lines[(int64_t)L * Q1 + s] = ids[s]; cnt[ids[s]]++; }
            L++; if (L > N) { fprintf(stderr, "too many lines\n"); return 1; }
        }
    }
    int ok = (L == N); for (int i = 0; i < N; i++) if (cnt[i] != Q1) ok = 0;
    fprintf(stderr, "W(%d): points %d lines %d, regular: %s\n", q, N, L, ok ? "yes" : "NO"); if (!ok) return 1;
    char fn[64]; sprintf(fn, "gq/gq_q%d.bin", q); FILE *f = fopen(fn, "wb"); int32_t hdr[3] = {q, N, L};
    fwrite(hdr, 4, 3, f); fwrite(lines, 4, (size_t)L * Q1, f); fwrite(coord, 1, (size_t)N * 7, f); fclose(f);
    return 0;
}
