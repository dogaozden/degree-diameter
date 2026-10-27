/* q6.h: shared helpers for the hexagon-family project.
   Field GF(q), q = p^e <= 32, encoded as in research/d10D7/hexgen2.c (a0 + a1 p + ..., same irreducibles), H(q) bins
   from hexgen2 (int32 q, N, L; L*(q+1) int32 point ids; N*7 uint8 coordinates), and the polar form
   B(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3 of Q = x0x4+x1x5+x2x6-x3^2. Two points of H(q) are opposite
   (distance 6 in the incidence graph) iff B(x,y) != 0. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int q, p, e;
static int ADD[32][32], MUL[32][32], NEG[32], INV[32];

static int poly_for(int qq, int *c) {
    memset(c, 0, sizeof(int) * 8);
    switch (qq) {
        case 4: c[0] = 1; c[1] = 1; return 2;
        case 8: c[0] = 1; c[1] = 1; return 3;
        case 9: c[0] = 1; return 2;
        case 16: c[0] = 1; c[1] = 1; return 4;
        case 25: c[0] = 2; return 2;
        case 27: c[0] = 1; c[1] = 2; return 3;
        case 32: c[0] = 1; c[2] = 1; return 5;
    }
    return 1;
}
static void field_init(int qq) {
    q = qq; for (p = 2; q % p; p++) {}
    int c[8]; e = poly_for(q, c);
    for (int x = 0; x < q; x++) for (int y = 0; y < q; y++) {
        int a[8] = {0}, b[8] = {0}, r[16] = {0};
        int t = x; for (int i = 0; i < e; i++) { a[i] = t % p; t /= p; }
        t = y; for (int i = 0; i < e; i++) { b[i] = t % p; t /= p; }
        int s = 0, pw = 1;
        for (int i = 0; i < e; i++) { s += ((a[i] + b[i]) % p) * pw; pw *= p; }
        ADD[x][y] = s;
        for (int i = 0; i < e; i++) for (int j = 0; j < e; j++) r[i + j] = (r[i + j] + a[i] * b[j]) % p;
        for (int k = 2 * e - 2; k >= e; k--) {
            int f = r[k]; if (!f) continue; r[k] = 0;
            for (int i = 0; i < e; i++) r[k - e + i] = ((r[k - e + i] - f * c[i]) % p + p) % p;
        }
        s = 0; pw = 1; for (int i = 0; i < e; i++) { s += r[i] * pw; pw *= p; }
        MUL[x][y] = s;
    }
    for (int x = 0; x < q; x++) { NEG[x] = -1; INV[x] = -1;
        for (int y = 0; y < q; y++) { if (ADD[x][y] == 0) NEG[x] = y; if (MUL[x][y] == 1) INV[x] = y; } }
}
typedef struct { int q, N, L; int32_t *LP; uint8_t *C; int32_t *PL; } Hex;
static Hex hex_load(const char *fn) {
    Hex h; FILE *f = fopen(fn, "rb"); if (!f) { fprintf(stderr, "cannot open %s\n", fn); exit(1); }
    int hd[3]; if (fread(hd, 4, 3, f) != 3) exit(1);
    h.q = hd[0]; h.N = hd[1]; h.L = hd[2]; int Q1 = h.q + 1;
    h.LP = malloc(sizeof(int32_t) * (size_t)h.L * Q1); if (fread(h.LP, 4, (size_t)h.L * Q1, f) != (size_t)h.L * Q1) exit(1);
    h.C = malloc((size_t)h.N * 7); if (fread(h.C, 1, (size_t)h.N * 7, f) != (size_t)h.N * 7) exit(1);
    fclose(f);
    h.PL = malloc(sizeof(int32_t) * (size_t)h.N * Q1); int *cnt = calloc(h.N, sizeof(int));
    for (int l = 0; l < h.L; l++) for (int k = 0; k < Q1; k++) { int pt = h.LP[(size_t)l * Q1 + k]; h.PL[(size_t)pt * Q1 + cnt[pt]++] = l; }
    free(cnt); field_init(h.q); return h;
}
static inline int Bxy(const uint8_t *x, const uint8_t *y) {
    int s = ADD[ADD[MUL[x[0]][y[4]]][MUL[x[4]][y[0]]]][ADD[MUL[x[1]][y[5]]][MUL[x[5]][y[1]]]];
    s = ADD[s][ADD[MUL[x[2]][y[6]]][MUL[x[6]][y[2]]]];
    int t = MUL[x[3]][y[3]]; t = ADD[t][t];
    return ADD[s][NEG[t]];
}
/* read whitespace-separated ints (lines starting with '#' skipped) */
static int read_ids(const char *fn, int **out) {
    FILE *f = fopen(fn, "r"); if (!f) { fprintf(stderr, "cannot open %s\n", fn); exit(1); }
    int cap = 1024, n = 0; int *a = malloc(sizeof(int) * cap); char buf[1 << 16];
    while (fgets(buf, sizeof buf, f)) {
        if (buf[0] == '#') continue;
        char *s = buf, *end; for (;;) { long v = strtol(s, &end, 10); if (end == s) break; if (n == cap) { cap *= 2; a = realloc(a, sizeof(int) * cap); } a[n++] = (int)v; s = end; }
    }
    fclose(f); *out = a; return n;
}
