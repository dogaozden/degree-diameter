/* (field code copied from research/d10D7/hexgen2.c) hexgen2.c: the split Cayley hexagon H(q) for any prime power q <= 32 (including q even).
   Same model as research/p4/d6/hexgen.c: points of X0X4 + X1X5 + X2X6 = X3^2 in PG(6,q); the lines through x are
   the lines through x in the plane pi_x = {y : Tits' six equations, B(x,y) = 0} (B the polar form; in
   characteristic 2 its X3 term vanishes and pi_x is still a plane through x).
   Field GF(p^e): polynomials over GF(p) mod a fixed irreducible, element a0 + a1 p + ... .
   Checks: |lines| = |points| = (q^6-1)/(q-1), q+1 points per line, q+1 lines per point.
   Output: hex/hex_q{q}.bin = int32 q, N, L, then L*(q+1) int32 point ids, then N*7 uint8 coordinates.
   Usage: hexgen2 q */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

int q, p, e;
int ADD[32][32], MUL[32][32], NEG[32], INV[32];

static int poly_for(int q, int *c) { /* monic irreducible of degree e: coefficients c[0..e-1] of x^e = -(c0 + c1 x + ...) */
    /* x^e + c_{e-1} x^{e-1} + ... + c0 */
    memset(c, 0, sizeof(int) * 8);
    switch (q) {
        case 4: c[0] = 1; c[1] = 1; return 2;          /* x^2+x+1 */
        case 8: c[0] = 1; c[1] = 1; return 3;          /* x^3+x+1 */
        case 9: c[0] = 1; return 2;                    /* x^2+1 */
        case 16: c[0] = 1; c[1] = 1; return 4;         /* x^4+x+1 */
        case 25: c[0] = 2; return 2;                   /* x^2+2 */
        case 27: c[0] = 1; c[1] = 2; return 3;         /* x^3+2x+1 */
        case 32: c[0] = 1; c[2] = 1; return 5;         /* x^5+x^2+1 */
    }
    return 1;
}

void field(void) {
    int c[8]; e = poly_for(q, c);
    for (int x = 0; x < q; x++) for (int y = 0; y < q; y++) {
        int a[8] = {0}, b[8] = {0}, r[16] = {0};
        int t = x; for (int i = 0; i < e; i++) { a[i] = t % p; t /= p; }
        t = y; for (int i = 0; i < e; i++) { b[i] = t % p; t /= p; }
        int s = 0, pw = 1;
        for (int i = 0; i < e; i++) { s += ((a[i] + b[i]) % p) * pw; pw *= p; }
        ADD[x][y] = s;
        for (int i = 0; i < e; i++) for (int j = 0; j < e; j++) r[i + j] = (r[i + j] + a[i] * b[j]) % p;
        for (int k = 2 * e - 2; k >= e; k--) {          /* reduce x^k = x^{k-e} * x^e = -x^{k-e}(c0 + ...) */
            int f = r[k]; if (!f) continue; r[k] = 0;
            for (int i = 0; i < e; i++) r[k - e + i] = ((r[k - e + i] - f * c[i]) % p + p) % p;
        }
        s = 0; pw = 1; for (int i = 0; i < e; i++) { s += r[i] * pw; pw *= p; }
        MUL[x][y] = s;
    }
    for (int x = 0; x < q; x++) { NEG[x] = -1; INV[x] = -1;
        for (int y = 0; y < q; y++) { if (ADD[x][y] == 0) NEG[x] = y; if (MUL[x][y] == 1) INV[x] = y; } }
    for (int x = 1; x < q; x++) if (INV[x] < 0) { fprintf(stderr, "not a field\n"); exit(1); }
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

/* hexauto: from hex/hex_q{q}.bin (hexgen2 output) write
     hex_q{q}.edges   incidence graph, points 0..N-1, lines N..2N-1 (apsp.c format)
     hex_q{q}.aut     int32 k, n, then k permutations of 0..n-1: torus elements diag(a, b, (ab)^-1, 1, a^-1, b^-1, ab)
                      for (a,b) = (w,1) and (1,w), w a primitive element. They preserve the quadric and Tits' six
                      equations; the checker (apsp_auto) verifies independently that they are graph automorphisms.
   usage: hexauto q */
int main(int argc, char **argv) {
    q = atoi(argv[1]); p = q; for (int d = 2; d <= q; d++) if (q % d == 0) { p = d; break; }
    field();
    char fn[256]; sprintf(fn, "hex/hex_q%d.bin", q); FILE *f = fopen(fn, "rb");
    int hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1; N = hdr[1]; int L = hdr[2], k1 = q + 1;
    int *lp = malloc((size_t)L * k1 * 4); if (fread(lp, 4, (size_t)L * k1, f) != (size_t)L * k1) return 1;
    uint8_t *co = malloc((size_t)N * 7); if (fread(co, 1, (size_t)N * 7, f) != (size_t)N * 7) return 1; fclose(f);
    codes = malloc(N * 8);
    for (int i = 0; i < N; i++) { int v[7]; for (int j = 0; j < 7; j++) v[j] = co[i * 7 + j]; codes[i] = code(v); if (i && codes[i] <= codes[i-1]) { fprintf(stderr, "codes not sorted\n"); return 1; } }
    /* lines through each point */
    int *deg = calloc(N, 4), *lt = malloc((size_t)N * k1 * 4);
    for (int l = 0; l < L; l++) for (int t = 0; t < k1; t++) { int x = lp[l * k1 + t]; lt[(size_t)x * k1 + deg[x]++] = l; }
    sprintf(fn, "hex_q%d.edges", q); f = fopen(fn, "w"); fprintf(f, "%d\n", 2 * N);
    for (int l = 0; l < L; l++) for (int t = 0; t < k1; t++) fprintf(f, "%d %d\n", lp[l * k1 + t], N + l);
    fclose(f);
    /* primitive element */
    int w = -1;
    for (int c = 2; c < q && w < 0; c++) { int x = c, ord = 1; while (x != 1) { x = mu(x, c); ord++; } if (ord == q - 1) w = c; }
    if (q == 2) w = 1; if (q == 3) w = 2;
    int nperm = 2; int n = 2 * N;
    sprintf(fn, "hex_q%d.aut", q); FILE *g = fopen(fn, "wb"); fwrite(&nperm, 4, 1, g); fwrite(&n, 4, 1, g);
    int *perm = malloc((size_t)n * 4);
    for (int which = 0; which < 2; which++) {
        int a = which == 0 ? w : 1, b = which == 0 ? 1 : w;
        int ab = mu(a, b), lam[7] = {a, b, INV[ab], 1, INV[a], INV[b], ab};
        for (int i = 0; i < N; i++) { int v[7]; for (int j = 0; j < 7; j++) v[j] = mu(lam[j], co[i * 7 + j]); perm[i] = lookup(v); }
        for (int l = 0; l < L; l++) {
            int x0 = perm[lp[l * k1]], x1 = perm[lp[l * k1 + 1]], img = -1;
            for (int t = 0; t < k1 && img < 0; t++) { int m = lt[(size_t)x0 * k1 + t];
                for (int s = 0; s < k1; s++) if (lp[m * k1 + s] == x1) { img = m; break; } }
            if (img < 0) { fprintf(stderr, "torus element %d does not map line %d to a line\n", which, l); return 2; }
            perm[N + l] = N + img;
        }
        fwrite(perm, 4, n, g);
    }
    fclose(g);
    printf("q=%d N=%d L=%d primitive w=%d; wrote hex_q%d.edges and hex_q%d.aut (2 torus generators)\n", q, N, L, w, q, q);
    return 0;
}
